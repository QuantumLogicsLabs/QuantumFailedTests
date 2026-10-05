# Compression suite
#
# Four lossless codecs written from scratch -- run-length encoding, Huffman
# coding (built with a binary heap), LZW with 12-bit codes and LZSS with a
# hash-chain match finder -- plus the bit-level reader/writer they share and
# CRC-32 / Adler-32 checksums. The workload compresses generated text and
# verifies every codec restores the input exactly.
#
# Self-checking: published check values and textbook examples are embedded,
# the rest is compared against values verified with the reference Ruby
# implementation, and the first mismatch raises.

class Checker
  def initialize(suite)
    @suite = suite
    @passed = 0
  end

  def eq(label, actual, expected)
    raise "#{@suite}: #{label}: expected #{expected}, got #{actual}" unless actual == expected
    @passed += 1
  end

  def near(label, actual, expected, tolerance)
    unless (actual - expected).abs <= tolerance
      raise "#{@suite}: #{label}: expected #{expected} +/- #{tolerance}, got #{actual}"
    end
    @passed += 1
  end

  def finish
    puts "#{@suite}: all #{@passed} checks passed"
  end
end

# Park-Miller generator. Every intermediate product stays below 2**53.
class Lcg
  def initialize(seed)
    @state = seed % 2147483647
    @state = 1 if @state.zero?
  end

  def next_int(bound)
    @state = (@state * 48271) % 2147483647
    @state % bound
  end

  def pick(items)
    items[next_int(items.length)]
  end
end

module Checksums
  CRC_TABLE = Array.new(256) do |index|
    value = index
    8.times { value = value.odd? ? (value >> 1) ^ 0xEDB88320 : value >> 1 }
    value
  end.freeze

  def self.crc32(bytes)
    crc = 0xFFFFFFFF
    bytes.each { |byte| crc = CRC_TABLE[(crc ^ byte) & 0xFF] ^ (crc >> 8) }
    crc ^ 0xFFFFFFFF
  end

  def self.adler32(bytes)
    a = 1
    b = 0
    bytes.each do |byte|
      a = (a + byte) % 65_521
      b = (b + a) % 65_521
    end
    (b << 16) | a
  end
end

class BitWriter
  def initialize
    @bytes = []
    @current = 0
    @filled = 0
  end

  def write(value, width)
    (width - 1).downto(0) do |shift|
      @current = (@current << 1) | ((value >> shift) & 1)
      @filled += 1
      next unless @filled == 8
      @bytes << @current
      @current = 0
      @filled = 0
    end
  end

  # Pads the last byte with zero bits and returns everything written.
  def finish
    write(0, 8 - @filled) if @filled > 0
    @bytes
  end
end

class BitReader
  def initialize(bytes)
    @bytes = bytes
    @position = 0
  end

  def read(width)
    value = 0
    width.times do
      byte = @bytes[@position >> 3]
      raise EOFError, "bit stream exhausted" if byte.nil?
      value = (value << 1) | ((byte >> (7 - (@position & 7))) & 1)
      @position += 1
    end
    value
  end
end

class MinHeap
  def initialize(&order)
    @items = []
    @order = order
  end

  def size
    @items.length
  end

  def push(item)
    @items << item
    index = @items.length - 1
    while index > 0
      parent = (index - 1) / 2
      break if @order.call(@items[parent], @items[index]) <= 0
      @items[parent], @items[index] = @items[index], @items[parent]
      index = parent
    end
    self
  end

  def pop
    top = @items.first
    last = @items.pop
    return top if @items.empty?
    @items[0] = last
    index = 0
    loop do
      left = index * 2 + 1
      right = left + 1
      smallest = index
      smallest = left if left < @items.length && @order.call(@items[left], @items[smallest]) < 0
      smallest = right if right < @items.length && @order.call(@items[right], @items[smallest]) < 0
      break if smallest == index
      @items[smallest], @items[index] = @items[index], @items[smallest]
      index = smallest
    end
    top
  end
end

module Rle
  def self.encode(bytes)
    bytes.chunk_while { |a, b| a == b }.flat_map do |run|
      run.each_slice(255).map { |piece| [piece.length, piece[0]] }
    end
  end

  def self.decode(pairs)
    pairs.flat_map { |count, byte| [byte] * count }
  end
end

module Huffman
  Node = Struct.new(:weight, :order, :symbol, :left, :right) do
    def leaf?
      left.nil?
    end
  end

  # Ties are broken by creation order so the tree is fully deterministic.
  def self.build_tree(frequencies)
    heap = MinHeap.new { |a, b| a.weight == b.weight ? a.order <=> b.order : a.weight <=> b.weight }
    order = 0
    frequencies.keys.sort.each do |symbol|
      heap.push(Node.new(frequencies[symbol], order, symbol, nil, nil))
      order += 1
    end
    while heap.size > 1
      left = heap.pop
      right = heap.pop
      heap.push(Node.new(left.weight + right.weight, order, nil, left, right))
      order += 1
    end
    heap.pop
  end

  def self.assign_codes(node, code, width, codes)
    if node.leaf?
      codes[node.symbol] = [code, width]
    else
      assign_codes(node.left, code << 1, width + 1, codes)
      assign_codes(node.right, (code << 1) | 1, width + 1, codes)
    end
    codes
  end

  def self.encode(bytes)
    frequencies = Hash.new(0)
    bytes.each { |byte| frequencies[byte] += 1 }
    codes = assign_codes(build_tree(frequencies), 0, 0, {})
    writer = BitWriter.new
    bit_count = 0
    bytes.each do |byte|
      code, width = codes[byte]
      writer.write(code, width)
      bit_count += width
    end
    { frequencies: frequencies, length: bytes.length, bit_count: bit_count, payload: writer.finish, codes: codes }
  end

  def self.decode(packet)
    tree = build_tree(packet[:frequencies])
    return Array.new(packet[:length], tree.symbol) if tree.leaf?
    reader = BitReader.new(packet[:payload])
    Array.new(packet[:length]) do
      node = tree
      node = reader.read(1).zero? ? node.left : node.right until node.leaf?
      node.symbol
    end
  end
end

module Lzw
  CODE_WIDTH = 12
  MAX_CODE = (1 << CODE_WIDTH) - 1

  # The dictionary maps (prefix code, next byte) -> code, packed in one Integer.
  def self.encode(bytes)
    return [] if bytes.empty?
    table = {}
    next_code = 256
    codes = []
    current = bytes[0]
    bytes.drop(1).each do |byte|
      key = current * 256 + byte
      if table.key?(key)
        current = table[key]
      else
        codes << current
        if next_code <= MAX_CODE
          table[key] = next_code
          next_code += 1
        end
        current = byte
      end
    end
    codes << current
  end

  def self.decode(codes)
    return [] if codes.empty?
    entries = Array.new(256) { |byte| [byte] }
    previous = entries[codes[0]]
    output = previous.dup
    codes.drop(1).each do |code|
      entry = if code < entries.length
                entries[code]
              elsif code == entries.length
                previous + [previous[0]]
              else
                raise ArgumentError, "corrupt LZW stream: code #{code}"
              end
      output.concat(entry)
      entries << previous + [entry[0]] if entries.length <= MAX_CODE
      previous = entry
    end
    output
  end

  def self.pack(codes)
    writer = BitWriter.new
    codes.each { |code| writer.write(code, CODE_WIDTH) }
    writer.finish
  end

  def self.unpack(bytes, count)
    reader = BitReader.new(bytes)
    Array.new(count) { reader.read(CODE_WIDTH) }
  end
end

module Lzss
  WINDOW = 4095
  MIN_MATCH = 3
  MAX_MATCH = 18
  MAX_CHAIN = 16

  def self.key_at(bytes, position)
    (bytes[position] << 16) | (bytes[position + 1] << 8) | bytes[position + 2]
  end

  def self.remember(bytes, position, heads, previous)
    return if position + MIN_MATCH > bytes.length
    key = key_at(bytes, position)
    previous[position] = heads[key]
    heads[key] = position
  end

  # Tokens are [:literal, byte] or [:match, distance, length].
  def self.encode(bytes)
    tokens = []
    heads = {}
    previous = []
    position = 0
    while position < bytes.length
      best_length = 0
      best_distance = 0
      if position + MIN_MATCH <= bytes.length
        candidate = heads[key_at(bytes, position)]
        limit = [MAX_MATCH, bytes.length - position].min
        chain = 0
        while candidate && position - candidate <= WINDOW && chain < MAX_CHAIN
          length = 0
          length += 1 while length < limit && bytes[candidate + length] == bytes[position + length]
          if length > best_length
            best_length = length
            best_distance = position - candidate
          end
          candidate = previous[candidate]
          chain += 1
        end
      end
      if best_length >= MIN_MATCH
        tokens << [:match, best_distance, best_length]
        best_length.times do
          remember(bytes, position, heads, previous)
          position += 1
        end
      else
        tokens << [:literal, bytes[position]]
        remember(bytes, position, heads, previous)
        position += 1
      end
    end
    tokens
  end

  def self.decode(tokens)
    output = []
    tokens.each do |kind, first, second|
      if kind == :literal
        output << first
      else
        start = output.length - first
        second.times { |offset| output << output[start + offset] }
      end
    end
    output
  end

  # literal: 0 + 8 bits; match: 1 + 12-bit distance + 4-bit (length - 3)
  def self.pack(tokens)
    writer = BitWriter.new
    tokens.each do |kind, first, second|
      if kind == :literal
        writer.write(0, 1)
        writer.write(first, 8)
      else
        writer.write(1, 1)
        writer.write(first, 12)
        writer.write(second - MIN_MATCH, 4)
      end
    end
    writer.finish
  end

  def self.unpack(bytes, count)
    reader = BitReader.new(bytes)
    Array.new(count) do
      if reader.read(1).zero?
        [:literal, reader.read(8)]
      else
        distance = reader.read(12)
        [:match, distance, reader.read(4) + MIN_MATCH]
      end
    end
  end
end

def shannon_entropy(bytes)
  counts = bytes.tally
  total = bytes.length.to_f
  -counts.values.sum { |count| (count / total) * Math.log2(count / total) }
end

WORDS = %w[
  the stream packet buffer window match literal code table entry symbol tree leaf node byte
  compress expand encode decode offset length repeat pattern data block header checksum
].freeze

def build_text(rng, target_length)
  text = String.new
  while text.length < target_length
    sentence = Array.new(4 + rng.next_int(9)) { rng.pick(WORDS) }.join(" ")
    text << sentence.capitalize << ". "
    text << "\n" if rng.next_int(5).zero?
  end
  text
end

def byte_checksum(bytes)
  bytes.reduce(7) { |hash, byte| (hash * 131 + byte) % 1_000_000_007 }
end

chk = Checker.new("compression_suite")

# --- checksums ----------------------------------------------------------------
chk.eq("crc32 check value", Checksums.crc32("123456789".bytes), 0xCBF43926)
chk.eq("crc32 of nothing", Checksums.crc32([]), 0)
chk.eq("adler32 check value", Checksums.adler32("Wikipedia".bytes), 0x11E60398)

# --- bit streams --------------------------------------------------------------
writer = BitWriter.new
[[5, 3], [0x1FF, 9], [1, 1], [0xABC, 12]].each { |value, width| writer.write(value, width) }
packed = writer.finish
chk.eq("bit writer output", packed, [0xBF, 0xFD, 0x5E, 0x00])
reader = BitReader.new(packed)
chk.eq("bit reader round trip", [3, 9, 1, 12].map { |width| reader.read(width) }, [5, 0x1FF, 1, 0xABC])
begin
  BitReader.new([0xFF]).read(9)
  outcome = "no error"
rescue EOFError => e
  outcome = e.message
end
chk.eq("bit reader detects truncation", outcome, "bit stream exhausted")

# --- heap ---------------------------------------------------------------------
heap = MinHeap.new { |a, b| a <=> b }
[42, 7, 19, 3, 88, 3, 61, 25].each { |value| heap.push(value) }
chk.eq("heap drains in order", Array.new(heap.size) { heap.pop }, [3, 3, 7, 19, 25, 42, 61, 88])

# --- textbook examples --------------------------------------------------------
chk.eq("rle example", Rle.encode([7, 7, 7, 7, 1, 2, 2]), [[4, 7], [1, 1], [2, 2]])
chk.eq("rle splits long runs", Rle.encode([0] * 600), [[255, 0], [255, 0], [90, 0]])

abracadabra = Huffman.encode("abracadabra".bytes)
chk.eq("huffman code lengths", "abcdr".bytes.map { |byte| abracadabra[:codes][byte][1] }, [1, 3, 3, 3, 3])
chk.eq("huffman bit count", abracadabra[:bit_count], 23)
chk.eq("huffman round trip", Huffman.decode(abracadabra).pack("C*"), "abracadabra")
chk.eq("huffman single symbol", Huffman.decode(Huffman.encode([65] * 9)), [65] * 9)

chk.eq("lzw example", Lzw.encode("TOBEORNOTTOBEORTOBEORNOT".bytes),
       [84, 79, 66, 69, 79, 82, 78, 79, 84, 256, 258, 260, 265, 259, 261, 263])
chk.eq("lzw decodes the self-referential case", Lzw.decode(Lzw.encode("aaaaaaa".bytes)).pack("C*"), "aaaaaaa")

chk.eq("lzss example", Lzss.encode("abcabcabcabcX".bytes),
       [[:literal, 97], [:literal, 98], [:literal, 99], [:match, 3, 9], [:literal, 88]])
chk.eq("lzss overlapping copy", Lzss.decode([[:literal, 120], [:match, 1, 6]]).pack("C*"), "xxxxxxx")

# --- generated text -----------------------------------------------------------
rng = Lcg.new(8_675_309)
text = build_text(rng, 36_000)
bytes = text.bytes
chk.eq("text length", bytes.length, 36041)
chk.eq("text crc32", Checksums.crc32(bytes), 2034820946)
chk.eq("text adler32", Checksums.adler32(bytes), 3355922597)

huffman = Huffman.encode(bytes)
chk.eq("huffman restores the text", Huffman.decode(huffman) == bytes, true)
chk.eq("huffman payload size", huffman[:payload].length, 19280)
chk.eq("huffman payload checksum", byte_checksum(huffman[:payload]), 428469332)
entropy = shannon_entropy(bytes)
average_bits = huffman[:bit_count].to_f / bytes.length
chk.near("entropy in bits per byte", entropy, 4.251948146192869, 1e-9)
chk.eq("huffman is within one bit of the entropy", average_bits >= entropy && average_bits < entropy + 1, true)

lzw_codes = Lzw.encode(bytes)
lzw_packed = Lzw.pack(lzw_codes)
chk.eq("lzw restores the text", Lzw.decode(Lzw.unpack(lzw_packed, lzw_codes.length)) == bytes, true)
chk.eq("lzw code count", lzw_codes.length, 6186)
chk.eq("lzw payload checksum", byte_checksum(lzw_packed), 791426919)

lzss_tokens = Lzss.encode(bytes)
lzss_packed = Lzss.pack(lzss_tokens)
chk.eq("lzss restores the text", Lzss.decode(Lzss.unpack(lzss_packed, lzss_tokens.length)) == bytes, true)
chk.eq("lzss token count", lzss_tokens.length, 4420)
chk.eq("lzss match count", lzss_tokens.count { |token| token[0] == :match }, 4181)
chk.eq("lzss payload size", lzss_packed.length, 9154)
chk.eq("lzss payload checksum", byte_checksum(lzss_packed), 478756099)

sizes = [bytes.length, huffman[:payload].length, lzw_packed.length, lzss_packed.length]
chk.eq("every codec shrinks the text", sizes.drop(1).all? { |size| size < bytes.length }, true)

# --- run-heavy data -----------------------------------------------------------
bitmap = []
300.times { bitmap.concat([rng.next_int(4)] * (1 + rng.next_int(40))) }
runs = Rle.encode(bitmap)
chk.eq("rle restores the bitmap", Rle.decode(runs) == bitmap, true)
chk.eq("rle run count", runs.length, 230)
chk.eq("rle shrinks the bitmap", runs.length * 2 < bitmap.length, true)
chk.eq("lzss restores the bitmap", Lzss.decode(Lzss.encode(bitmap)) == bitmap, true)

puts "text: #{bytes.length} bytes, entropy #{entropy.round(3)} bits/byte"
puts format("huffman %5d bytes (%.1f%%)", sizes[1], 100.0 * sizes[1] / sizes[0])
puts format("lzw     %5d bytes (%.1f%%)", sizes[2], 100.0 * sizes[2] / sizes[0])
puts format("lzss    %5d bytes (%.1f%%)", sizes[3], 100.0 * sizes[3] / sizes[0])
chk.finish

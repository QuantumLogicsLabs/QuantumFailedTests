# SHA-256, HMAC, PBKDF2 and a Merkle tree
#
# A dependency-free implementation of SHA-256 (FIPS 180-4) with HMAC
# (RFC 2104), PBKDF2 (RFC 8018), a Merkle tree with inclusion proofs and a
# small proof-of-work miner. Everything is 32-bit modular arithmetic done
# with shifts, masks and xor.
#
# Self-checking: the published NIST / RFC test vectors are embedded, the
# rest is compared against values verified with the reference Ruby
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

module Sha256
  MASK = 0xFFFFFFFF

  K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ].freeze

  INITIAL = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ].freeze

  def self.rotr(value, count)
    ((value >> count) | (value << (32 - count))) & MASK
  end

  # Appends the 0x80 marker, zero padding and the 64-bit big-endian bit length.
  def self.pad(bytes)
    bit_length = bytes.length * 8
    padded = bytes.dup
    padded << 0x80
    padded << 0 while padded.length % 64 != 56
    7.downto(0) { |index| padded << ((bit_length >> (index * 8)) & 0xFF) }
    padded
  end

  # bytes: Array of Integers in 0..255. Returns the 32 digest bytes.
  def self.digest(bytes)
    message = pad(bytes)
    state = INITIAL.dup
    w = Array.new(64, 0)
    offset = 0
    while offset < message.length
      16.times do |i|
        j = offset + i * 4
        w[i] = (message[j] << 24) | (message[j + 1] << 16) | (message[j + 2] << 8) | message[j + 3]
      end
      (16...64).each do |i|
        s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
        s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) & MASK
      end

      a, b, c, d, e, f, g, h = state
      64.times do |i|
        s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
        choice = (e & f) ^ (~e & MASK & g)
        temp1 = (h + s1 + choice + K[i] + w[i]) & MASK
        s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
        majority = (a & b) ^ (a & c) ^ (b & c)
        temp2 = (s0 + majority) & MASK
        h = g
        g = f
        f = e
        e = (d + temp1) & MASK
        d = c
        c = b
        b = a
        a = (temp1 + temp2) & MASK
      end

      state = state.zip([a, b, c, d, e, f, g, h]).map { |before, after| (before + after) & MASK }
      offset += 64
    end
    state.flat_map { |word| [(word >> 24) & 0xFF, (word >> 16) & 0xFF, (word >> 8) & 0xFF, word & 0xFF] }
  end

  def self.hex(bytes)
    bytes.map { |byte| format("%02x", byte) }.join
  end

  def self.hexdigest(text)
    hex(digest(text.bytes))
  end
end

module Hmac
  BLOCK_SIZE = 64

  def self.digest(key_bytes, message_bytes)
    key = key_bytes.length > BLOCK_SIZE ? Sha256.digest(key_bytes) : key_bytes.dup
    key << 0 while key.length < BLOCK_SIZE
    inner_pad = key.map { |byte| byte ^ 0x36 }
    outer_pad = key.map { |byte| byte ^ 0x5c }
    Sha256.digest(outer_pad + Sha256.digest(inner_pad + message_bytes))
  end

  def self.hexdigest(key, message)
    Sha256.hex(digest(key.bytes, message.bytes))
  end
end

module Pbkdf2
  def self.derive(password, salt, iterations, length)
    key = password.bytes
    output = []
    block_index = 1
    while output.length < length
      counter = [(block_index >> 24) & 0xFF, (block_index >> 16) & 0xFF, (block_index >> 8) & 0xFF, block_index & 0xFF]
      round = Hmac.digest(key, salt.bytes + counter)
      block = round.dup
      (iterations - 1).times do
        round = Hmac.digest(key, round)
        block = block.zip(round).map { |x, y| x ^ y }
      end
      output.concat(block)
      block_index += 1
    end
    Sha256.hex(output.first(length))
  end
end

class MerkleTree
  attr_reader :root, :levels

  def initialize(records)
    raise ArgumentError, "a Merkle tree needs at least one record" if records.empty?
    @levels = [records.map { |record| Sha256.digest(record.bytes) }]
    while @levels.last.length > 1
      parents = @levels.last.each_slice(2).map { |left, right| Sha256.digest(left + (right || left)) }
      @levels << parents
    end
    @root = @levels.last.first
  end

  # The sibling hashes needed to recompute the root from one leaf.
  def proof(index)
    path = []
    @levels[0...-1].each do |level|
      sibling = index.even? ? index + 1 : index - 1
      sibling = index if sibling >= level.length
      path << [level[sibling], index.even?]
      index /= 2
    end
    path
  end

  def self.verify(record, path, root)
    hash = Sha256.digest(record.bytes)
    path.each do |sibling, node_is_left|
      hash = node_is_left ? Sha256.digest(hash + sibling) : Sha256.digest(sibling + hash)
    end
    hash == root
  end
end

# Finds the first nonce whose digest starts with the requested zero nibbles.
def mine(prefix, zero_nibbles)
  target = "0" * zero_nibbles
  nonce = 0
  loop do
    digest = Sha256.hexdigest("#{prefix}:#{nonce}")
    return [nonce, digest] if digest.start_with?(target)
    nonce += 1
  end
end

def differing_bits(left, right)
  left.zip(right).sum { |x, y| (x ^ y).to_s(2).count("1") }
end

chk = Checker.new("sha256_hmac")

# --- primitives ---------------------------------------------------------------
chk.eq("rotr", Sha256.rotr(0x80000001, 1), 0xC0000000)
chk.eq("rotr wraps", Sha256.rotr(0x12345678, 8), 0x78123456)
chk.eq("padding length", [0, 55, 56, 64, 119, 120].map { |n| Sha256.pad([0] * n).length }, [64, 64, 128, 128, 128, 192])
chk.eq("padding tail", Sha256.pad([97, 98, 99]).last(3), [0, 0, 24])

# --- FIPS 180-4 vectors -------------------------------------------------------
chk.eq("sha256 empty", Sha256.hexdigest(""),
       "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
chk.eq("sha256 abc", Sha256.hexdigest("abc"),
       "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
chk.eq("sha256 two blocks", Sha256.hexdigest("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
       "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
chk.eq("sha256 pangram", Sha256.hexdigest("The quick brown fox jumps over the lazy dog"),
       "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")
chk.eq("sha256 10000 x a", Sha256.hexdigest("a" * 10_000), "27dd1f61b867b6a0f6e9d8a41c43231de52107e53ae424de8f847b821db4b711")

# --- RFC 4231 HMAC vectors ----------------------------------------------------
chk.eq("hmac case 1", Sha256.hex(Hmac.digest([0x0b] * 20, "Hi There".bytes)),
       "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
chk.eq("hmac case 2", Hmac.hexdigest("Jefe", "what do ya want for nothing?"),
       "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
chk.eq("hmac long key", Sha256.hex(Hmac.digest([0xaa] * 131, "Test Using Larger Than Block-Size Key - Hash Key First".bytes)),
       "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")

# --- PBKDF2-HMAC-SHA256 -------------------------------------------------------
chk.eq("pbkdf2 1 iteration", Pbkdf2.derive("password", "salt", 1, 32),
       "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b")
chk.eq("pbkdf2 2 iterations", Pbkdf2.derive("password", "salt", 2, 32),
       "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43")
chk.eq("pbkdf2 60 iterations, 40 bytes", Pbkdf2.derive("correct horse", "battery staple", 60, 40), "fb649d43c0cad5b6eee3ff0a543fd7ae6e9f46dd6bf6ab70466996dddb5032991360744fd03bd1f1")

# --- hash chain ---------------------------------------------------------------
link = "genesis".bytes
250.times { link = Sha256.digest(link) }
chk.eq("hash chain of 250", Sha256.hex(link), "3a298f28a9ccea1bed352d0739271bf39649e9198e2d3f8b8b7345f61f8367b0")

# --- Merkle tree --------------------------------------------------------------
records = Array.new(203) { |i| "account-#{i}:balance=#{(i * 7919) % 10_007}" }
tree = MerkleTree.new(records)
chk.eq("merkle level sizes", tree.levels.map(&:length), [203, 102, 51, 26, 13, 7, 4, 2, 1])
chk.eq("merkle root", Sha256.hex(tree.root), "57290bba16aefd12c5a5c88bd2b36cf1d0a6e43b9daed26302b2012c59f443f4")

proofs_ok = [0, 1, 77, 100, 101, 201, 202].all? do |index|
  MerkleTree.verify(records[index], tree.proof(index), tree.root)
end
chk.eq("merkle proofs verify", proofs_ok, true)
chk.eq("merkle proof length", tree.proof(202).length, 8)
chk.eq("merkle rejects a tampered record",
       MerkleTree.verify("account-77:balance=999999", tree.proof(77), tree.root), false)
chk.eq("merkle rejects a proof for the wrong leaf",
       MerkleTree.verify(records[78], tree.proof(77), tree.root), false)

# --- proof of work ------------------------------------------------------------
nonce, digest = mine("block-42", 2)
chk.eq("proof of work nonce", nonce, 273)
chk.eq("proof of work digest", digest, "0010bbaed31c78e94d2d80e183ec6b6596ec4867962c4b9436aeddb4027f7099")
chk.eq("proof of work is reproducible", Sha256.hexdigest("block-42:#{nonce}"), digest)

# --- avalanche effect ---------------------------------------------------------
flipped = differing_bits(Sha256.digest("avalanche0".bytes), Sha256.digest("avalanche1".bytes))
chk.eq("avalanche bit count", flipped, 133)
chk.eq("avalanche is near half of 256 bits", flipped.between?(96, 160), true)

puts "merkle root : #{Sha256.hex(tree.root)}"
puts "mined nonce : #{nonce} -> #{digest}"
puts "avalanche   : #{flipped} of 256 bits changed"
chk.finish

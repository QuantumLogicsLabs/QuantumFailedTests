# JSON codec
#
# A hand-written JSON toolkit: a recursive-descent parser that reports the
# exact offset of a syntax error, compact and pretty serializers, a dotted
# path query helper and a tree walker. The workload generates a few thousand
# nested nodes and round-trips them through every component.
#
# Self-checking: results are compared against values verified with the
# reference Ruby implementation, and the first mismatch raises.

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

class JsonError < StandardError
  attr_reader :offset

  def initialize(message, offset)
    super("#{message} at offset #{offset}")
    @offset = offset
  end
end

class JsonParser
  ESCAPES = {
    '"' => '"', "\\" => "\\", "/" => "/", "b" => "\b",
    "f" => "\f", "n" => "\n", "r" => "\r", "t" => "\t"
  }.freeze

  def self.parse(text)
    new(text).parse_document
  end

  def initialize(text)
    @text = text
    @pos = 0
  end

  def parse_document
    skip_whitespace
    value = parse_value
    skip_whitespace
    fail_at("unexpected trailing data") unless eof?
    value
  end

  private

  def eof?
    @pos >= @text.length
  end

  def peek
    @text[@pos]
  end

  def fail_at(message)
    raise JsonError.new(message, @pos)
  end

  def skip_whitespace
    @pos += 1 while !eof? && " \t\r\n".include?(peek)
  end

  def digit?(ch)
    ch >= "0" && ch <= "9"
  end

  def parse_value
    fail_at("unexpected end of input") if eof?
    case peek
    when "{" then parse_object
    when "[" then parse_array
    when '"' then parse_string
    when "t" then parse_literal("true", true)
    when "f" then parse_literal("false", false)
    when "n" then parse_literal("null", nil)
    when "-", "0".."9" then parse_number
    else fail_at("unexpected character '#{peek}'")
    end
  end

  def parse_literal(word, value)
    fail_at("invalid literal") unless @text[@pos, word.length] == word
    @pos += word.length
    value
  end

  def parse_number
    start = @pos
    @pos += 1 if peek == "-"
    fail_at("invalid number") if eof? || !digit?(peek)
    if peek == "0"
      @pos += 1
    else
      @pos += 1 while !eof? && digit?(peek)
    end
    is_float = false
    if !eof? && peek == "."
      is_float = true
      @pos += 1
      fail_at("digit expected after decimal point") if eof? || !digit?(peek)
      @pos += 1 while !eof? && digit?(peek)
    end
    if !eof? && (peek == "e" || peek == "E")
      is_float = true
      @pos += 1
      @pos += 1 if !eof? && (peek == "+" || peek == "-")
      fail_at("digit expected in exponent") if eof? || !digit?(peek)
      @pos += 1 while !eof? && digit?(peek)
    end
    literal = @text[start...@pos]
    is_float ? literal.to_f : literal.to_i
  end

  def parse_string
    @pos += 1
    out = String.new
    loop do
      fail_at("unterminated string") if eof?
      ch = peek
      @pos += 1
      case ch
      when '"' then return out
      when "\\" then out << parse_escape
      else out << ch
      end
    end
  end

  def parse_escape
    fail_at("unterminated escape") if eof?
    ch = peek
    @pos += 1
    if ch == "u"
      hex = @text[@pos, 4]
      fail_at("invalid unicode escape") unless hex && hex.match?(/\A[0-9a-fA-F]{4}\z/)
      @pos += 4
      [hex.to_i(16)].pack("U")
    elsif ESCAPES.key?(ch)
      ESCAPES[ch]
    else
      @pos -= 1
      fail_at("invalid escape")
    end
  end

  def parse_array
    @pos += 1
    items = []
    skip_whitespace
    if peek == "]"
      @pos += 1
      return items
    end
    loop do
      skip_whitespace
      items << parse_value
      skip_whitespace
      fail_at("unterminated array") if eof?
      ch = peek
      @pos += 1
      return items if ch == "]"
      unless ch == ","
        @pos -= 1
        fail_at("expected ',' or ']'")
      end
    end
  end

  def parse_object
    @pos += 1
    object = {}
    skip_whitespace
    if peek == "}"
      @pos += 1
      return object
    end
    loop do
      skip_whitespace
      fail_at("expected string key") unless peek == '"'
      key = parse_string
      skip_whitespace
      fail_at("expected ':'") unless peek == ":"
      @pos += 1
      skip_whitespace
      object[key] = parse_value
      skip_whitespace
      fail_at("unterminated object") if eof?
      ch = peek
      @pos += 1
      return object if ch == "}"
      unless ch == ","
        @pos -= 1
        fail_at("expected ',' or '}'")
      end
    end
  end
end

class JsonWriter
  def initialize(indent: 0)
    @indent = indent
  end

  def write(value)
    parts = []
    emit(value, 0, parts)
    parts.join
  end

  private

  def emit(value, level, parts)
    case value
    when nil then parts << "null"
    when true then parts << "true"
    when false then parts << "false"
    when Integer then parts << value.to_s
    when Float then parts << format_float(value)
    when String then parts << quote(value)
    when Array then emit_array(value, level, parts)
    when Hash then emit_object(value, level, parts)
    else raise ArgumentError, "cannot serialize #{value.class}"
    end
  end

  def format_float(value)
    raise ArgumentError, "cannot serialize a non-finite float" if value.nan? || value.infinite?
    value.to_s
  end

  def quote(text)
    out = String.new('"')
    text.each_char do |ch|
      case ch
      when '"' then out << '\\"'
      when "\\" then out << "\\\\"
      when "\n" then out << "\\n"
      when "\r" then out << "\\r"
      when "\t" then out << "\\t"
      else out << (ch.ord < 0x20 ? format("\\u%04x", ch.ord) : ch)
      end
    end
    out << '"'
  end

  def newline(level, parts)
    return if @indent.zero?
    parts << "\n" << (" " * (@indent * level))
  end

  def emit_array(items, level, parts)
    if items.empty?
      parts << "[]"
      return
    end
    parts << "["
    items.each_with_index do |item, index|
      parts << "," if index > 0
      newline(level + 1, parts)
      emit(item, level + 1, parts)
    end
    newline(level, parts)
    parts << "]"
  end

  def emit_object(object, level, parts)
    if object.empty?
      parts << "{}"
      return
    end
    parts << "{"
    first = true
    object.each do |key, value|
      parts << "," unless first
      first = false
      newline(level + 1, parts)
      parts << quote(key) << (@indent.zero? ? ":" : ": ")
      emit(value, level + 1, parts)
    end
    newline(level, parts)
    parts << "}"
  end
end

module JsonPath
  # "orders[2].lines[0].sku" -> ["orders", 2, "lines", 0, "sku"]
  def self.compile(path)
    steps = []
    path.split(".").each do |segment|
      name = segment[/\A[^\[]*/]
      steps << name unless name.empty?
      segment.scan(/\[(\d+)\]/) { |match| steps << match[0].to_i }
    end
    steps
  end

  def self.fetch(document, path)
    compile(path).reduce(document) do |node, step|
      case node
      when Hash then node[step]
      when Array then step.is_a?(Integer) ? node[step] : nil
      else nil
      end
    end
  end
end

class TreeStats
  attr_reader :counts, :max_depth, :integer_sum

  def initialize
    @counts = Hash.new(0)
    @max_depth = 0
    @integer_sum = 0
  end

  def visit(node, depth = 1)
    @max_depth = depth if depth > @max_depth
    case node
    when Hash
      @counts[:object] += 1
      node.each_value { |child| visit(child, depth + 1) }
    when Array
      @counts[:array] += 1
      node.each { |child| visit(child, depth + 1) }
    when String then @counts[:string] += 1
    when Integer
      @counts[:integer] += 1
      @integer_sum += node
    when Float then @counts[:float] += 1
    when true, false then @counts[:boolean] += 1
    when nil then @counts[:null] += 1
    end
    self
  end
end

class DocumentBuilder
  WORDS = %w[alpha bravo charlie delta echo foxtrot golf hotel india juliet kilo lima].freeze
  TAILS = ["plain", "\"quoted\"", "back\\slash", "tab\there", "line\nbreak", "slash/ok"].freeze

  def initialize(seed)
    @rng = Lcg.new(seed)
  end

  def build(depth)
    roll = @rng.next_int(depth > 0 ? 9 : 5)
    case roll
    when 0 then @rng.next_int(100_000) - 50_000
    when 1 then (@rng.next_int(4000) - 2000) / 4.0
    when 2 then phrase
    when 3 then @rng.next_int(2).zero?
    when 4 then nil
    when 5, 6 then Array.new(1 + @rng.next_int(5)) { build(depth - 1) }
    else build_object(depth)
    end
  end

  private

  def phrase
    words = Array.new(1 + @rng.next_int(3)) { @rng.pick(WORDS) }
    "#{words.join(' ')} #{@rng.pick(TAILS)}"
  end

  def build_object(depth)
    object = {}
    (1 + @rng.next_int(5)).times do |index|
      object["#{@rng.pick(WORDS)}_#{index}"] = build(depth - 1)
    end
    object
  end
end

def text_checksum(text)
  hash = 7
  text.each_byte { |byte| hash = (hash * 131 + byte) % 1_000_000_007 }
  hash
end

def deep_map(node, &block)
  case node
  when Hash then node.each_with_object({}) { |(key, value), out| out[key] = deep_map(value, &block) }
  when Array then node.map { |child| deep_map(child, &block) }
  else block.call(node)
  end
end

chk = Checker.new("json_codec")

# --- hand-written fixture ----------------------------------------------------
fixture = '{"name":"Widget","tags":["a","b"],"price":12.5,"stock":{"warehouse":[3,0,17],"ok":true},' \
          '"note":null,"esc":"line\\nbreak \\"q\\" \\u0041"}'
doc = JsonParser.parse(fixture)
chk.eq("fixture name", doc["name"], "Widget")
chk.eq("fixture tags", doc["tags"], ["a", "b"])
chk.eq("fixture price", doc["price"], 12.5)
chk.eq("fixture key order", doc.keys, ["name", "tags", "price", "stock", "note", "esc"])
chk.eq("fixture nested path", JsonPath.fetch(doc, "stock.warehouse[2]"), 17)
chk.eq("fixture boolean path", JsonPath.fetch(doc, "stock.ok"), true)
chk.eq("fixture null", doc["note"], nil)
chk.eq("fixture escapes", doc["esc"], "line\nbreak \"q\" A")
chk.eq("fixture missing path", JsonPath.fetch(doc, "stock.missing[4].x"), nil)
chk.eq("fixture compact round trip", JsonWriter.new.write(doc), fixture.sub("\\u0041", "A"))
chk.eq("whitespace tolerance", JsonParser.parse(" [ 1 , 2.5e1 , -3 , { } , [ ] ] "), [1, 25.0, -3, {}, []])
chk.eq("control characters", JsonWriter.new.write("bell\u0007"), '"bell\u0007"')

pretty = JsonWriter.new(indent: 2).write({ "a" => [1, 2], "b" => {}, "c" => { "d" => nil } })
expected_pretty = <<~JSON.chomp
  {
    "a": [
      1,
      2
    ],
    "b": {},
    "c": {
      "d": null
    }
  }
JSON
chk.eq("pretty layout", pretty, expected_pretty)

# --- error reporting ---------------------------------------------------------
malformed = ['{"a":}', "[1,2", '{"a" 1}', '"open', "tru", "[1,]", '{"a":1,}', "-", "1.e3", "[1] 2", '"bad\\q"', ""]
offsets = malformed.map do |text|
  begin
    JsonParser.parse(text)
    -1
  rescue JsonError => e
    e.offset
  end
end
chk.eq("error offsets", offsets, [5, 4, 5, 5, 0, 3, 7, 1, 2, 4, 5, 0])

begin
  JsonParser.parse('{"key": [true, flase]}')
  message = "no error"
rescue JsonError => e
  message = e.message
end
chk.eq("error message", message, "invalid literal at offset 15")

# --- generated workload ------------------------------------------------------
builder = DocumentBuilder.new(20240607)
catalog = Array.new(400) { |id| { "id" => id, "payload" => builder.build(6) } }

compact = JsonWriter.new.write(catalog)
reparsed = JsonParser.parse(compact)
chk.eq("compact round trip", reparsed == catalog, true)

pretty_text = JsonWriter.new(indent: 2).write(catalog)
from_pretty = JsonParser.parse(pretty_text)
chk.eq("pretty round trip", from_pretty == catalog, true)
chk.eq("pretty reserializes to compact", JsonWriter.new.write(from_pretty) == compact, true)

stats = TreeStats.new.visit(reparsed)
chk.eq("compact length", compact.length, 100677)
chk.eq("compact checksum", text_checksum(compact), 423005771)
chk.eq("pretty line count", pretty_text.count("\n") + 1, 11381)
chk.eq("node counts", stats.counts, {array: 1235, object: 1634, integer: 1438, string: 1078, float: 998, boolean: 1068, null: 1061})
chk.eq("max depth", stats.max_depth, 9)
chk.eq("integer sum", stats.integer_sum, 552175)

kinds = Hash.new(0)
catalog.each_index do |index|
  payload = JsonPath.fetch(reparsed, "[#{index}].payload")
  kinds[payload.class.name] += 1
end
chk.eq("payload kinds", kinds, {"Hash" => 91, "Array" => 88, "String" => 58, "NilClass" => 34, "Float" => 50, "FalseClass" => 24, "TrueClass" => 16, "Integer" => 39})
chk.eq("payload kinds total", kinds.values.sum, 400)

doubled = deep_map(catalog) { |leaf| leaf.is_a?(Integer) ? leaf * 2 : leaf }
chk.eq("deep_map doubles integers", TreeStats.new.visit(doubled).integer_sum, stats.integer_sum * 2)

shouted = deep_map(catalog) { |leaf| leaf.is_a?(String) ? leaf.upcase : leaf }
shouted_text = JsonWriter.new.write(shouted)
chk.eq("deep_map keeps length", shouted_text.length, compact.length)
chk.eq("deep_map upcases strings", text_checksum(shouted_text), 314939917)

puts "documents: #{catalog.length}, nodes: #{stats.counts.values.sum}, depth: #{stats.max_depth}"
puts "compact: #{compact.length} bytes, pretty: #{pretty_text.length} bytes"
chk.finish

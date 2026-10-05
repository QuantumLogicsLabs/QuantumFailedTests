# Regular expression engine
#
# A regex engine that never backtracks: a recursive-descent parser builds an
# AST, Thompson's construction turns it into an NFA, and matching runs a
# DFA that is built lazily from sets of NFA states. Supports literals, ".",
# character classes with ranges and negation, \d \w \s, groups, alternation
# and the * + ? {m} {m,} {m,n} repetitions. Because it simulates all NFA
# states at once, patterns that make backtracking engines take exponential
# time run in linear time here.
#
# Self-checking: a table of hand-checked cases is embedded, the engine is
# cross-checked against Ruby's own Regexp, counts found by scanning a
# generated log must equal the counts the generator recorded, and the first
# mismatch raises.

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

class RegexSyntaxError < StandardError
end

# alternation := sequence ("|" sequence)*
# sequence    := repeat*
# repeat      := atom ("*" | "+" | "?" | "{m}" | "{m,}" | "{m,n}")*
# atom        := literal | "." | "[...]" | "(" alternation ")" | "\" escape
class RegexParser
  CLASS_ESCAPES = {
    "d" => [[48, 57]],
    "w" => [[48, 57], [65, 90], [95, 95], [97, 122]],
    "s" => [[9, 10], [13, 13], [32, 32]]
  }.freeze

  def initialize(pattern)
    @pattern = pattern
    @pos = 0
  end

  def parse
    node = parse_alternation
    raise RegexSyntaxError, "unexpected ')' at #{@pos}" unless eof?
    node
  end

  private

  def eof?
    @pos >= @pattern.length
  end

  def peek
    @pattern[@pos]
  end

  def take
    ch = @pattern[@pos]
    @pos += 1
    ch
  end

  def parse_alternation
    branches = [parse_sequence]
    while peek == "|"
      take
      branches << parse_sequence
    end
    branches.length == 1 ? branches[0] : [:alt, branches]
  end

  def parse_sequence
    items = []
    items << parse_repeat until eof? || peek == "|" || peek == ")"
    case items.length
    when 0 then [:empty]
    when 1 then items[0]
    else [:concat, items]
    end
  end

  def parse_repeat
    atom = parse_atom
    loop do
      case peek
      when "*"
        take
        atom = [:star, atom]
      when "+"
        take
        atom = [:plus, atom]
      when "?"
        take
        atom = [:optional, atom]
      when "{"
        minimum, maximum = parse_bounds
        atom = [:repeat, atom, minimum, maximum]
      else
        return atom
      end
    end
  end

  def parse_bounds
    take
    minimum = parse_integer
    maximum = minimum
    if peek == ","
      take
      maximum = peek == "}" ? nil : parse_integer
    end
    raise RegexSyntaxError, "expected '}' at #{@pos}" unless peek == "}"
    take
    raise RegexSyntaxError, "invalid repeat range {#{minimum},#{maximum}}" if maximum && maximum < minimum
    [minimum, maximum]
  end

  def parse_integer
    start = @pos
    @pos += 1 while !eof? && peek >= "0" && peek <= "9"
    raise RegexSyntaxError, "expected a number at #{@pos}" if start == @pos
    @pattern[start...@pos].to_i
  end

  def parse_atom
    raise RegexSyntaxError, "unexpected end of pattern" if eof?
    ch = take
    case ch
    when "("
      inner = parse_alternation
      raise RegexSyntaxError, "missing ')'" unless peek == ")"
      take
      inner
    when "[" then parse_class
    when "." then [:any]
    when "\\" then parse_escape
    when "*", "+", "?", "{" then raise RegexSyntaxError, "nothing to repeat at #{@pos - 1}"
    else [:char, ch]
    end
  end

  def parse_escape
    raise RegexSyntaxError, "dangling backslash" if eof?
    ch = take
    return [:set, CLASS_ESCAPES[ch], false] if CLASS_ESCAPES.key?(ch)
    return [:char, "\n"] if ch == "n"
    return [:char, "\t"] if ch == "t"
    [:char, ch]
  end

  def parse_class
    negated = false
    if peek == "^"
      take
      negated = true
    end
    ranges = []
    until peek == "]"
      raise RegexSyntaxError, "unterminated character class" if eof?
      low = take
      if low == "\\"
        escaped = take
        if CLASS_ESCAPES.key?(escaped)
          ranges.concat(CLASS_ESCAPES[escaped])
          next
        end
        low = escaped
      end
      if peek == "-" && @pos + 1 < @pattern.length && @pattern[@pos + 1] != "]"
        take
        high = take
        raise RegexSyntaxError, "invalid range #{low}-#{high}" if high.ord < low.ord
        ranges << [low.ord, high.ord]
      else
        ranges << [low.ord, low.ord]
      end
    end
    take
    [:set, ranges, negated]
  end
end

class Regex
  attr_reader :pattern

  def initialize(pattern)
    @pattern = pattern
    # NFA states: [:accept], [:consume, matcher, next] or [:split, [next, ...]]
    @states = []
    @accept = add_state([:accept])
    start = build(RegexParser.new(pattern).parse, @accept)
    # DFA states are sorted sets of NFA states, numbered as they are discovered.
    @dfa_ids = {}
    @dfa_sets = []
    @dfa_next = []
    @dfa_accepting = []
    @dead = dfa_state([])
    @initial = dfa_state(closure([start]))
  end

  def nfa_size
    @states.length
  end

  def dfa_size
    @dfa_sets.length
  end

  # Length of the longest match that begins at `start`, or nil.
  def match_length(text, start = 0)
    state = @initial
    longest = @dfa_accepting[state] ? 0 : nil
    position = start
    while position < text.length
      state = step(state, text[position])
      break if state == @dead
      position += 1
      longest = position - start if @dfa_accepting[state]
    end
    longest
  end

  def full_match?(text)
    match_length(text) == text.length
  end

  # Leftmost-longest search: [start, length] or nil.
  def search(text, from = 0)
    (from..text.length).each do |start|
      length = match_length(text, start)
      return [start, length] if length
    end
    nil
  end

  # Every non-overlapping match, left to right.
  def scan(text)
    matches = []
    position = 0
    while position <= text.length
      found = search(text, position)
      break if found.nil?
      start, length = found
      matches << text[start, length]
      position = start + [length, 1].max
    end
    matches
  end

  private

  def add_state(state)
    @states << state
    @states.length - 1
  end

  # Thompson's construction, built back to front: returns the entry state of
  # a fragment that continues at `target` once `node` has matched.
  def build(node, target)
    case node[0]
    when :empty
      target
    when :char, :any, :set
      add_state([:consume, node, target])
    when :concat
      node[1].reverse.reduce(target) { |following, child| build(child, following) }
    when :alt
      add_state([:split, node[1].map { |child| build(child, target) }])
    when :optional
      add_state([:split, [build(node[1], target), target]])
    when :star
      fork = add_state([:split, []])
      @states[fork][1] = [build(node[1], fork), target]
      fork
    when :plus
      fork = add_state([:split, []])
      entry = build(node[1], fork)
      @states[fork][1] = [entry, target]
      entry
    when :repeat
      minimum = node[2]
      maximum = node[3]
      entry = target
      if maximum.nil?
        entry = build([:star, node[1]], entry)
      else
        (maximum - minimum).times { entry = build([:optional, node[1]], entry) }
      end
      minimum.times { entry = build(node[1], entry) }
      entry
    end
  end

  # Every NFA state reachable through split states alone.
  def closure(ids)
    seen = {}
    pending = ids.dup
    until pending.empty?
      id = pending.pop
      next if seen[id]
      seen[id] = true
      state = @states[id]
      pending.concat(state[1]) if state[0] == :split
    end
    seen.keys.sort
  end

  def dfa_state(set)
    known = @dfa_ids[set]
    return known if known
    id = @dfa_sets.length
    @dfa_ids[set] = id
    @dfa_sets << set
    @dfa_next << {}
    @dfa_accepting << set.include?(@accept)
    id
  end

  def step(id, ch)
    cached = @dfa_next[id][ch]
    return cached if cached
    code = ch.ord
    targets = []
    @dfa_sets[id].each do |nfa_id|
      state = @states[nfa_id]
      targets << state[2] if state[0] == :consume && accepts?(state[1], ch, code)
    end
    @dfa_next[id][ch] = dfa_state(closure(targets))
  end

  def accepts?(matcher, ch, code)
    case matcher[0]
    when :char then matcher[1] == ch
    when :any then ch != "\n"
    when :set
      inside = matcher[1].any? { |low, high| code >= low && code <= high }
      matcher[2] ? !inside : inside
    end
  end
end

# [pattern, text, does the whole text match?]
CASES = [
  ["abc", "abc", true], ["abc", "abd", false], ["abc", "ab", false],
  ["a*", "", true], ["a*", "aaaa", true], ["a+", "", false],
  ["a+b?", "aaab", true], ["a+b?", "aabb", false],
  ["colou?r", "color", true], ["colou?r", "colour", true], ["colou?r", "colouur", false],
  ["(ab|cd)+", "abcdab", true], ["(ab|cd)+", "abc", false],
  ["a|b|c", "b", true], ["a|b|c", "d", false],
  ["(a|b)*abb", "babaabb", true], ["(a|b)*abb", "abab", false],
  ["[a-c]+", "abcabc", true], ["[a-c]+", "abcd", false],
  ["[^0-9]+", "hello", true], ["[^0-9]+", "he11o", false],
  ["\\d{3}-\\d{4}", "555-1234", true], ["\\d{3}-\\d{4}", "55-12345", false],
  ["\\w+@\\w+\\.com", "user_1@example.com", true], ["\\w+@\\w+\\.com", "user@example.org", false],
  ["a{2,4}", "a", false], ["a{2,4}", "aaa", true], ["a{2,4}", "aaaaa", false],
  ["a{3,}", "aaaaaaa", true], ["a{3,}", "aa", false],
  ["(ab){2}c", "ababc", true], ["(ab){2}c", "abc", false],
  ["x.z", "xyz", true], ["x.z", "xz", false], ["x.*z", "xabcz", true], ["x.*z", "xabc", false],
  ["\\s*\\w+\\s*", "  word ", true], ["\\s*\\w+\\s*", "two words", false],
  ["(a*)*b", "aaab", true], ["(a*)*b", "aaa", false],
  ["", "", true], ["", "a", false],
  ["a\\+b", "a+b", true], ["a\\+b", "aab", false],
  ["[\\d.]+", "3.14", true], ["[\\d.]+", "3,14", false],
  ["[a-zA-Z_][a-zA-Z0-9_]*", "_ident42", true], ["[a-zA-Z_][a-zA-Z0-9_]*", "9lives", false],
  ["(0|1(01*0)*1)*", "110", true], ["(0|1(01*0)*1)*", "111", false], ["(0|1(01*0)*1)*", "1001", true],
  ["(a|ab)(c|bcd)(d*)", "abcd", true], ["(|a)+b", "aab", true], ["[-+]?\\d+(\\.\\d+)?", "-12.50", true]
].freeze

LEVELS = %w[INFO INFO INFO WARN ERROR DEBUG].freeze
RESOURCES = %w[items users orders].freeze

def build_log(rng, count)
  Array.new(count) do |index|
    level = rng.pick(LEVELS)
    ip = Array.new(4) { rng.next_int(256) }.join(".")
    latency = 5 + rng.next_int(900)
    path = "/api/v#{1 + rng.next_int(3)}/#{rng.pick(RESOURCES)}"
    path += "/#{rng.next_int(10_000)}" if rng.next_int(2).zero?
    line = "2024-03-#{format('%02d', 1 + index % 28)} [#{level}] ip=#{ip} latency=#{latency}ms GET #{path}"
    { level: level, ip: ip, latency: latency, path: path, line: line }
  end
end

chk = Checker.new("regex_engine")

# --- matching -----------------------------------------------------------------
results = CASES.map { |pattern, text, _| Regex.new(pattern).full_match?(text) }
failures = CASES.zip(results).reject { |(_, _, expected), actual| expected == actual }
chk.eq("case table failures", failures.map { |(pattern, text, _), _| "#{pattern} ~ #{text}" }, [])
chk.eq("case table size", [CASES.length, results.count(true)], [54, 29])

# --- searching ----------------------------------------------------------------
chk.eq("search finds the first match", Regex.new("\\d+").search("abc 123 def 4567"), [4, 3])
chk.eq("search is leftmost-longest", Regex.new("a+").search("baaac"), [1, 3])
chk.eq("search prefers the longer alternative", Regex.new("ab|abcd").search("xabcdx"), [1, 4])
chk.eq("search with no match", Regex.new("z+").search("abc"), nil)
chk.eq("search from an offset", Regex.new("\\d+").search("abc 123 def 4567", 7), [12, 4])
chk.eq("scan numbers", Regex.new("\\d+").scan("a1b22c333"), ["1", "22", "333"])
chk.eq("scan addresses", Regex.new("[a-z]+@[a-z]+\\.[a-z]+").scan("mail bob@site.org and amy@corp.com now"),
       ["bob@site.org", "amy@corp.com"])
chk.eq("scan words", Regex.new("\\w+").scan("  the quick-brown fox  "), %w[the quick brown fox])
chk.eq("scan with no match", Regex.new("\\d").scan("none here"), [])

# --- syntax errors ------------------------------------------------------------
messages = ["(ab", "ab)", "*a", "a{3", "a{4,2}", "[abc", "a\\", "a{x}"].map do |pattern|
  begin
    Regex.new(pattern)
    "no error"
  rescue RegexSyntaxError => e
    e.message
  end
end
chk.eq("syntax errors", messages,
       ["missing ')'", "unexpected ')' at 2", "nothing to repeat at 0", "expected '}' at 3",
        "invalid repeat range {4,2}", "unterminated character class", "dangling backslash", "expected a number at 2"])

# --- automaton sizes ----------------------------------------------------------
binary = Regex.new("(0|1(01*0)*1)*")
multiples = (0...3000).select { |n| binary.full_match?(n.to_s(2)) }
chk.eq("binary multiples of three", multiples, (0...3000).select { |n| (n % 3).zero? })
chk.eq("divisibility automaton sizes", [binary.nfa_size, binary.dfa_size], [11, 4])

# --- a pattern that defeats backtracking --------------------------------------
size = 28
pathological = Regex.new("(a?){#{size}}a{#{size}}")
chk.eq("pathological matches", [size - 1, size, 2 * size, 2 * size + 1].map { |n| pathological.full_match?("a" * n) },
       [false, true, true, false])
chk.eq("pathological automaton sizes", [pathological.nfa_size, pathological.dfa_size], [85, 58])

# --- log scanning -------------------------------------------------------------
rng = Lcg.new(31_415_926)
log = build_log(rng, 2400)
address = Regex.new("\\d+\\.\\d+\\.\\d+\\.\\d+")
severity = Regex.new("ERROR|WARN")
latency = Regex.new("latency=\\d+ms")
detail = Regex.new("/api/v\\d/[a-z]+/\\d+")
digits = Regex.new("\\d+")

found_addresses = log.map do |entry|
  start, length = address.search(entry[:line])
  entry[:line][start, length]
end
chk.eq("addresses extracted", found_addresses == log.map { |entry| entry[:ip] }, true)

severe = log.count { |entry| severity.search(entry[:line]) }
chk.eq("severe lines", severe, log.count { |entry| %w[ERROR WARN].include?(entry[:level]) })
chk.eq("severe line count", severe, 773)

total_latency = log.sum do |entry|
  start, length = latency.search(entry[:line])
  digits.scan(entry[:line][start, length]).first.to_i
end
chk.eq("latency total", total_latency, log.sum { |entry| entry[:latency] })
chk.eq("latency total value", total_latency, 1089690)

detail_lines = log.count { |entry| detail.search(entry[:line]) }
chk.eq("detail requests", detail_lines, log.count { |entry| entry[:path].count("/") == 4 })
chk.eq("numbers per line", log.first(5).map { |entry| digits.scan(entry[:line]).length }, [10, 10, 9, 10, 10])
chk.eq("lazy automaton sizes", [address, severity, latency, detail].map(&:dfa_size), [9, 10, 13, 13])

# --- agreement with the built-in engine ---------------------------------------
disagreements = CASES.reject do |pattern, text, _|
  Regexp.new("\\A(?:#{pattern})\\z").match?(text) == Regex.new(pattern).full_match?(text)
end
chk.eq("agrees with Regexp", disagreements, [])
native_addresses = log.map { |entry| entry[:line][/\d+\.\d+\.\d+\.\d+/] }
chk.eq("agrees with Regexp on the log", native_addresses == found_addresses, true)

puts "#{CASES.length} cases, #{results.count(true)} matching"
puts "pathological pattern: #{pathological.nfa_size} NFA states, #{pathological.dfa_size} DFA states"
puts "log: #{log.length} lines, #{severe} severe, mean latency #{total_latency / log.length}ms"
chk.finish

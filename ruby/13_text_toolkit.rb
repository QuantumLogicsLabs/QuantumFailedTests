# Text processing toolkit
#
# Four tools a documentation pipeline needs: a line diff built on the
# longest common subsequence (with patch and reverse-patch), word wrapping
# and full justification, a Markdown-to-HTML converter, and a template
# engine with loops, conditionals, nested lookups and filters.
#
# Self-checking: patches must rebuild their target exactly, hand-written
# fixtures are embedded, the rest is compared against values verified with
# the reference Ruby implementation, and the first mismatch raises.

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

class PatchError < StandardError
end

module LineDiff
  # Returns the edit script from old to new as [:keep | :delete | :insert, line].
  def self.diff(old_lines, new_lines)
    rows = old_lines.length
    cols = new_lines.length
    # table[i][j] = length of the LCS of old_lines[i..] and new_lines[j..]
    table = Array.new(rows + 1) { Array.new(cols + 1, 0) }
    (rows - 1).downto(0) do |i|
      (cols - 1).downto(0) do |j|
        table[i][j] = if old_lines[i] == new_lines[j]
                        table[i + 1][j + 1] + 1
                      else
                        [table[i + 1][j], table[i][j + 1]].max
                      end
      end
    end

    script = []
    i = 0
    j = 0
    while i < rows && j < cols
      if old_lines[i] == new_lines[j]
        script << [:keep, old_lines[i]]
        i += 1
        j += 1
      elsif table[i + 1][j] >= table[i][j + 1]
        script << [:delete, old_lines[i]]
        i += 1
      else
        script << [:insert, new_lines[j]]
        j += 1
      end
    end
    old_lines[i..].each { |line| script << [:delete, line] }
    new_lines[j..].each { |line| script << [:insert, line] }
    script
  end

  def self.patch(lines, script)
    result = []
    position = 0
    script.each do |action, line|
      if action == :insert
        result << line
        next
      end
      unless lines[position] == line
        raise PatchError, "line #{position + 1} does not match the patch"
      end
      result << line if action == :keep
      position += 1
    end
    raise PatchError, "patch ends before line #{position + 1}" unless position == lines.length
    result
  end

  def self.reverse(script)
    swap = { keep: :keep, delete: :insert, insert: :delete }
    script.map { |action, line| [swap[action], line] }
  end

  def self.summary(script)
    counts = script.map(&:first).tally
    { kept: counts.fetch(:keep, 0), deleted: counts.fetch(:delete, 0), inserted: counts.fetch(:insert, 0) }
  end

  def self.render(script)
    markers = { keep: " ", delete: "-", insert: "+" }
    script.map { |action, line| "#{markers[action]}#{line}" }
  end
end

module TextLayout
  def self.wrap(text, width)
    lines = []
    current = String.new
    text.split.each do |word|
      if current.empty?
        current << word
      elsif current.length + 1 + word.length <= width
        current << " " << word
      else
        lines << current
        current = String.new(word)
      end
    end
    lines << current unless current.empty?
    lines
  end

  # Pads the gaps between words so every line but the last fills the width.
  def self.justify(text, width)
    lines = wrap(text, width)
    lines.each_with_index.map do |line, index|
      words = line.split
      next line if index == lines.length - 1 || words.length == 1
      gaps = words.length - 1
      spaces = width - words.sum(&:length)
      padded = words.each_with_index.map do |word, position|
        next word if position == gaps
        word + " " * (spaces / gaps + (position < spaces % gaps ? 1 : 0))
      end
      padded.join
    end
  end
end

class Markdown
  def render(source)
    @html = []
    @paragraph = []
    @list_tag = nil
    in_code = false
    source.each_line do |raw|
      line = raw.chomp
      if in_code
        if line.start_with?("```")
          @html << "</code></pre>"
          in_code = false
        else
          @html << escape(line)
        end
      elsif line.start_with?("```")
        flush
        @html << "<pre><code>"
        in_code = true
      elsif line.strip.empty?
        flush
      elsif (heading = line.match(/\A(#+)\s+(.*)\z/)) && heading[1].length <= 6
        flush
        level = heading[1].length
        @html << "<h#{level}>#{inline(heading[2])}</h#{level}>"
      elsif (item = line.match(/\A\s*[-*]\s+(.*)\z/))
        list_item("ul", item[1])
      elsif (item = line.match(/\A\s*\d+\.\s+(.*)\z/))
        list_item("ol", item[1])
      elsif line.start_with?("> ")
        flush
        @html << "<blockquote>#{inline(line[2..])}</blockquote>"
      else
        close_list
        @paragraph << line.strip
      end
    end
    flush
    @html << "</code></pre>" if in_code
    @html.join("\n")
  end

  private

  def flush
    close_list
    return if @paragraph.empty?
    @html << "<p>#{inline(@paragraph.join(' '))}</p>"
    @paragraph = []
  end

  def close_list
    return if @list_tag.nil?
    @html << "</#{@list_tag}>"
    @list_tag = nil
  end

  def list_item(tag, text)
    unless @list_tag == tag
      flush
      @html << "<#{tag}>"
      @list_tag = tag
    end
    @html << "<li>#{inline(text)}</li>"
  end

  def escape(text)
    text.gsub("&", "&amp;").gsub("<", "&lt;").gsub(">", "&gt;")
  end

  def inline(text)
    html = escape(text)
    html = html.gsub(/`([^`]+)`/) { "<code>#{$1}</code>" }
    html = html.gsub(/\*\*([^*]+)\*\*/, '<strong>\1</strong>')
    html = html.gsub(/\*([^*]+)\*/, '<em>\1</em>')
    html.gsub(/\[([^\]]+)\]\(([^)]+)\)/, '<a href="\2">\1</a>')
  end
end

# {{ path }}            value lookup, innermost scope first; "this" is the current item
# {{ path | filter }}   filters apply left to right
# {{#each path}} ... {{/each}}
# {{#if path}} ... {{else}} ... {{/if}}
class Template
  FILTERS = {
    "upcase" => ->(value) { value.to_s.upcase },
    "capitalize" => ->(value) { value.to_s.capitalize },
    "length" => ->(value) { value.length },
    "money" => ->(value) { format("%.2f", value / 100.0) },
    "join" => ->(value) { value.join(", ") },
    "pad" => ->(value) { value.to_s.rjust(8) }
  }.freeze

  def initialize(source)
    @tokens = source.split(/(\{\{.*?\}\})/)
    @position = 0
    @closed_by = nil
    @nodes = parse_until([])
  end

  def render(context)
    render_nodes(@nodes, [context])
  end

  private

  def parse_until(terminators)
    nodes = []
    while @position < @tokens.length
      token = @tokens[@position]
      @position += 1
      unless token.start_with?("{{")
        nodes << [:text, token] unless token.empty?
        next
      end
      tag = token[2...-2].strip
      if terminators.include?(tag)
        @closed_by = tag
        return nodes
      elsif tag.start_with?("#each ")
        nodes << [:each, tag[6..].strip, parse_until(["/each"])]
      elsif tag.start_with?("#if ")
        consequent = parse_until(["else", "/if"])
        alternative = @closed_by == "else" ? parse_until(["/if"]) : []
        nodes << [:if, tag[4..].strip, consequent, alternative]
      elsif tag.start_with?("/") || tag == "else"
        raise ArgumentError, "unexpected tag '#{tag}'"
      else
        path, *filters = tag.split("|").map(&:strip)
        nodes << [:value, path, filters]
      end
    end
    raise ArgumentError, "missing closing tag '#{terminators.last}'" unless terminators.empty?
    nodes
  end

  def lookup(path, scopes)
    return scopes.last if path == "this"
    first, *rest = path.split(".")
    scope = scopes.reverse.find { |candidate| candidate.is_a?(Hash) && candidate.key?(first) }
    value = scope ? scope[first] : nil
    rest.reduce(value) { |current, key| current.is_a?(Hash) ? current[key] : nil }
  end

  def truthy?(value)
    !(value.nil? || value == false || (value.respond_to?(:empty?) && value.empty?))
  end

  def render_nodes(nodes, scopes)
    nodes.map { |node| render_node(node, scopes) }.join
  end

  def render_node(node, scopes)
    case node[0]
    when :text
      node[1]
    when :value
      value = lookup(node[1], scopes)
      node[2].each do |name|
        filter = FILTERS.fetch(name) { raise ArgumentError, "unknown filter '#{name}'" }
        value = filter.call(value)
      end
      value.to_s
    when :each
      items = lookup(node[1], scopes) || []
      rendered = items.each_with_index.map do |item, index|
        render_nodes(node[2], scopes + [{ "index" => index + 1 }, item])
      end
      rendered.join
    when :if
      render_nodes(truthy?(lookup(node[1], scopes)) ? node[2] : node[3], scopes)
    end
  end
end

WORDS = %w[
  system module parser buffer handler request response token cache index worker queue
  schema record cursor engine filter adapter session channel payload socket thread
].freeze

def build_document(rng, line_count)
  Array.new(line_count) do |number|
    words = Array.new(3 + rng.next_int(6)) { rng.pick(WORDS) }
    "#{number + 1}: #{words.join(' ')}"
  end
end

# A deterministic revision: drops some lines, rewrites some, inserts others.
def revise(rng, lines)
  revised = []
  lines.each do |line|
    case rng.next_int(10)
    when 0 then next
    when 1 then revised << "#{line} (edited)"
    when 2
      revised << line
      revised << "inserted #{rng.pick(WORDS)} #{rng.next_int(1000)}"
    else revised << line
    end
  end
  revised
end

def text_checksum(text)
  hash = 7
  text.each_byte { |byte| hash = (hash * 131 + byte) % 1_000_000_007 }
  hash
end

chk = Checker.new("text_toolkit")

# --- diff ---------------------------------------------------------------------
script = LineDiff.diff(%w[a b c d], %w[a c d e])
chk.eq("diff script", script, [[:keep, "a"], [:delete, "b"], [:keep, "c"], [:keep, "d"], [:insert, "e"]])
chk.eq("diff rendering", LineDiff.render(script), [" a", "-b", " c", " d", "+e"])
chk.eq("diff summary", LineDiff.summary(script), { kept: 3, deleted: 1, inserted: 1 })
chk.eq("patch", LineDiff.patch(%w[a b c d], script), %w[a c d e])
chk.eq("reverse patch", LineDiff.patch(%w[a c d e], LineDiff.reverse(script)), %w[a b c d])
chk.eq("diff of identical input", LineDiff.summary(LineDiff.diff(%w[x y], %w[x y])), { kept: 2, deleted: 0, inserted: 0 })
chk.eq("diff against nothing", LineDiff.diff([], %w[x y]), [[:insert, "x"], [:insert, "y"]])
begin
  LineDiff.patch(%w[a x c d], script)
  outcome = "no error"
rescue PatchError => e
  outcome = e.message
end
chk.eq("patch rejects the wrong file", outcome, "line 2 does not match the patch")

rng = Lcg.new(60_221_023)
original = build_document(rng, 700)
revised = revise(rng, original)
script = LineDiff.diff(original, revised)
summary = LineDiff.summary(script)
chk.eq("large patch rebuilds the revision", LineDiff.patch(original, script) == revised, true)
chk.eq("large reverse patch rebuilds the original", LineDiff.patch(revised, LineDiff.reverse(script)) == original, true)
chk.eq("kept + deleted covers the original", summary[:kept] + summary[:deleted], original.length)
chk.eq("kept + inserted covers the revision", summary[:kept] + summary[:inserted], revised.length)
chk.eq("large diff summary", summary, {kept: 556, deleted: 144, inserted: 128})
chk.eq("large diff checksum", text_checksum(LineDiff.render(script).join("\n")), 244389421)

# --- wrapping -----------------------------------------------------------------
sentence = "The quick brown fox jumps over the lazy dog while the careful engineer reviews every changed line."
chk.eq("wrap", TextLayout.wrap(sentence, 30),
       ["The quick brown fox jumps over", "the lazy dog while the careful", "engineer reviews every changed", "line."])
chk.eq("justify", TextLayout.justify(sentence, 34),
       ["The quick brown fox jumps over the", "lazy   dog   while   the   careful", "engineer   reviews  every  changed", "line."])
chk.eq("wrap keeps a long word whole", TextLayout.wrap("a supercalifragilistic word", 10), ["a", "supercalifragilistic", "word"])
essay = build_document(rng, 60).join(" ")
justified = TextLayout.justify(essay, 72)
chk.eq("justified lines fill the width", justified[0...-1].all? { |line| line.length == 72 }, true)
chk.eq("justification keeps the words", justified.join(" ").split == essay.split, true)
chk.eq("justified line count", justified.length, 38)
chk.eq("justified checksum", text_checksum(justified.join("\n")), 647479681)

# --- markdown -----------------------------------------------------------------
markdown = <<~MARKDOWN
  # Release *notes*

  The **parser** now handles `a < b` and [links](https://example.com/docs).
  It also joins wrapped lines.

  - first item
  - second **bold** item

  1. step one
  2. step two

  > quoted & escaped

  ```
  if a < b && c > d
    puts "*not* emphasis"
  ```
  ## Done
MARKDOWN
expected_html = <<~HTML.chomp
  <h1>Release <em>notes</em></h1>
  <p>The <strong>parser</strong> now handles <code>a &lt; b</code> and <a href="https://example.com/docs">links</a>. It also joins wrapped lines.</p>
  <ul>
  <li>first item</li>
  <li>second <strong>bold</strong> item</li>
  </ul>
  <ol>
  <li>step one</li>
  <li>step two</li>
  </ol>
  <blockquote>quoted &amp; escaped</blockquote>
  <pre><code>
  if a &lt; b &amp;&amp; c &gt; d
    puts "*not* emphasis"
  </code></pre>
  <h2>Done</h2>
HTML
chk.eq("markdown", Markdown.new.render(markdown), expected_html)
chk.eq("markdown heading levels", Markdown.new.render("###### six\n####### seven"), "<h6>six</h6>\n<p>####### seven</p>")

# --- templates ----------------------------------------------------------------
invoice = Template.new(<<~TEMPLATE)
  Invoice for {{ customer.name | upcase }} ({{ customer.tags | join }})
  {{#each lines}}{{ index }}. {{ name | capitalize }} x{{ qty }} = {{ total | money | pad }}
  {{/each}}{{#if discount}}Discount: {{ discount | money }}{{else}}No discount{{/if}}
  {{#if notes}}Notes: {{ notes | length }}{{/if}}Total: {{ total | money }}
TEMPLATE
context = {
  "customer" => { "name" => "Ada Lovelace", "tags" => %w[vip wholesale] },
  "lines" => [
    { "name" => "widget", "qty" => 3, "total" => 3897 },
    { "name" => "gadget", "qty" => 1, "total" => 2450 }
  ],
  "discount" => 500,
  "notes" => [],
  "total" => 5847
}
expected_invoice = <<~TEXT
  Invoice for ADA LOVELACE (vip, wholesale)
  1. Widget x3 =    38.97
  2. Gadget x1 =    24.50
  Discount: 5.00
  Total: 58.47
TEXT
chk.eq("template", invoice.render(context), expected_invoice)
chk.eq("template else branch", invoice.render(context.merge("discount" => nil)).lines[3], "No discount\n")
chk.eq("template nested loops",
       Template.new("{{#each rows}}[{{#each this}}{{ this }}{{/each}}]{{/each}}").render({ "rows" => [[1, 2], [3], []] }),
       "[12][3][]")
chk.eq("template missing value", Template.new("<{{ nobody.home }}>").render({}), "<>")

errors = ["{{#each items}}never closed", "{{ name | shout }}", "stray {{/if}}"].map do |source|
  begin
    Template.new(source).render({ "name" => "x", "items" => [] })
    "no error"
  rescue ArgumentError => e
    e.message
  end
end
chk.eq("template errors", errors, ["missing closing tag '/each'", "unknown filter 'shout'", "unexpected tag '/if'"])

statement = Template.new("{{#each accounts}}{{ index }}:{{ owner | upcase }}:{{ balance | money }}{{#if flagged}}!{{/if}};{{/each}}")
accounts = Array.new(1500) do |id|
  { "owner" => "#{rng.pick(WORDS)}-#{id}", "balance" => rng.next_int(10_000_000), "flagged" => rng.next_int(7).zero? }
end
rendered = statement.render({ "accounts" => accounts })
chk.eq("statement entries", rendered.count(";"), 1500)
chk.eq("statement flags", rendered.count("!"), accounts.count { |account| account["flagged"] })
chk.eq("statement checksum", text_checksum(rendered), 758866778)

puts "diff: #{summary[:kept]} kept, #{summary[:deleted]} deleted, #{summary[:inserted]} inserted"
puts justified.first(3)
puts invoice.render(context)
chk.finish

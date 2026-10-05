# Full-text search engine
#
# A tokenizer with stop words and suffix stemming, a positional inverted
# index, BM25 ranking, phrase queries, a boolean query language
# (AND / OR / NOT with parentheses) evaluated by merging sorted posting
# lists, prefix completion by binary search and "did you mean" suggestions
# from edit distance. The workload indexes about a thousand generated
# documents and runs every kind of query against them.
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

class Tokenizer
  STOP_WORDS = %w[the a an and or of to in is it for on with as by at be this that].freeze
  SUFFIXES = %w[ingly edly ing ed ly es s].freeze

  def tokens(text)
    text.downcase.scan(/[a-z0-9]+/).reject { |word| STOP_WORDS.include?(word) }.map { |word| stem(word) }
  end

  def stem(word)
    return word if word.length <= 4
    SUFFIXES.each do |suffix|
      return word[0...-suffix.length] if word.end_with?(suffix) && word.length - suffix.length >= 3
    end
    word
  end
end

module EditDistance
  def self.levenshtein(a, b)
    previous = (0..b.length).to_a
    a.each_char.with_index(1) do |char_a, i|
      current = [i]
      b.each_char.with_index(1) do |char_b, j|
        cost = char_a == char_b ? 0 : 1
        current << [previous[j] + 1, current[j - 1] + 1, previous[j - 1] + cost].min
      end
      previous = current
    end
    previous.last
  end
end

# Set algebra on sorted, duplicate-free id lists.
module SortedLists
  def self.intersect(a, b)
    result = []
    i = 0
    j = 0
    while i < a.length && j < b.length
      if a[i] == b[j]
        result << a[i]
        i += 1
        j += 1
      elsif a[i] < b[j]
        i += 1
      else
        j += 1
      end
    end
    result
  end

  def self.union(a, b)
    result = []
    i = 0
    j = 0
    while i < a.length || j < b.length
      if j >= b.length || (i < a.length && a[i] < b[j])
        result << a[i]
        i += 1
      elsif i >= a.length || b[j] < a[i]
        result << b[j]
        j += 1
      else
        result << a[i]
        i += 1
        j += 1
      end
    end
    result
  end

  def self.difference(a, b)
    result = []
    j = 0
    a.each do |id|
      j += 1 while j < b.length && b[j] < id
      result << id unless j < b.length && b[j] == id
    end
    result
  end
end

class InvertedIndex
  attr_reader :doc_count, :token_count

  def initialize(tokenizer)
    @tokenizer = tokenizer
    @postings = Hash.new { |hash, term| hash[term] = {} }
    @doc_lengths = {}
    @doc_count = 0
    @token_count = 0
    @sorted_terms = nil
  end

  def add(doc_id, title, body)
    tokens = @tokenizer.tokens("#{title} #{body}")
    tokens.each_with_index do |term, position|
      (@postings[term][doc_id] ||= []) << position
    end
    @doc_lengths[doc_id] = tokens.length
    @doc_count += 1
    @token_count += tokens.length
    @sorted_terms = nil
  end

  def vocabulary_size
    @postings.size
  end

  def term?(term)
    @postings.key?(term)
  end

  def doc_ids_for(term)
    term?(term) ? @postings[term].keys.sort : []
  end

  def document_frequency(term)
    term?(term) ? @postings[term].size : 0
  end

  def average_length
    @token_count.to_f / @doc_count
  end

  # Okapi BM25. Returns [[doc_id, score], ...] best first.
  def rank(query, limit = 10, k1 = 1.2, b = 0.75)
    scores = Hash.new(0.0)
    average = average_length
    @tokenizer.tokens(query).uniq.each do |term|
      next unless term?(term)
      postings = @postings[term]
      idf = Math.log(1.0 + (@doc_count - postings.size + 0.5) / (postings.size + 0.5))
      postings.each do |doc_id, positions|
        frequency = positions.length
        length_norm = 1 - b + b * @doc_lengths[doc_id] / average
        scores[doc_id] += idf * frequency * (k1 + 1) / (frequency + k1 * length_norm)
      end
    end
    scores.sort_by { |doc_id, score| [-score, doc_id] }.first(limit)
  end

  # Documents containing the words as one consecutive run.
  def phrase(text)
    terms = @tokenizer.tokens(text)
    return [] if terms.empty? || terms.any? { |term| !term?(term) }
    candidates = terms.map { |term| @postings[term].keys }.reduce { |shared, ids| shared & ids }
    candidates.sort.select do |doc_id|
      @postings[terms[0]][doc_id].any? do |start|
        terms.each_with_index.all? { |term, offset| @postings[term][doc_id].include?(start + offset) }
      end
    end
  end

  def complete(prefix, limit = 5)
    @sorted_terms ||= @postings.keys.sort
    start = @sorted_terms.bsearch_index { |term| term >= prefix }
    return [] if start.nil?
    @sorted_terms[start..].take_while { |term| term.start_with?(prefix) }.first(limit)
  end

  def suggest(word, limit = 3)
    candidates = @postings.keys.select { |term| (term.length - word.length).abs <= 2 }
    scored = candidates.map { |term| [EditDistance.levenshtein(word, term), term] }
    scored.sort.first(limit).map { |_, term| term }
  end
end

# query := or_expr
# or_expr := and_expr ("OR" and_expr)*
# and_expr := primary (("AND" | "NOT") primary)*      "a NOT b" means a without b
# primary := word | "(" or_expr ")"
class BooleanQuery
  def initialize(index, tokenizer)
    @index = index
    @tokenizer = tokenizer
  end

  def evaluate(text)
    @tokens = text.scan(/\(|\)|[A-Za-z0-9]+/)
    @cursor = 0
    result = parse_or
    raise ArgumentError, "unexpected token '#{@tokens[@cursor]}'" if @cursor < @tokens.length
    result
  end

  private

  def parse_or
    left = parse_and
    while @tokens[@cursor] == "OR"
      @cursor += 1
      left = SortedLists.union(left, parse_and)
    end
    left
  end

  def parse_and
    left = parse_primary
    loop do
      case @tokens[@cursor]
      when "AND"
        @cursor += 1
        left = SortedLists.intersect(left, parse_primary)
      when "NOT"
        @cursor += 1
        left = SortedLists.difference(left, parse_primary)
      else
        break
      end
    end
    left
  end

  def parse_primary
    token = @tokens[@cursor]
    raise ArgumentError, "unexpected end of query" if token.nil?
    @cursor += 1
    if token == "("
      inner = parse_or
      raise ArgumentError, "missing ')'" unless @tokens[@cursor] == ")"
      @cursor += 1
      inner
    elsif token == ")" || %w[AND OR NOT].include?(token)
      raise ArgumentError, "unexpected token '#{token}'"
    else
      stems = @tokenizer.tokens(token)
      stems.empty? ? [] : @index.doc_ids_for(stems.first)
    end
  end
end

SYLLABLES = %w[ka lo mi ren tu sha vel dor nim pax qui zor bel fen gra tho].freeze

def build_vocabulary(rng, size)
  seen = {}
  words = []
  while words.length < size
    word = Array.new(2 + rng.next_int(2)) { rng.pick(SYLLABLES) }.join
    next if seen[word]
    seen[word] = true
    words << word
  end
  words
end

# Squaring a uniform draw skews the pick towards the front of the list,
# giving the corpus a few very common words and a long tail of rare ones.
def skewed_pick(rng, words)
  draw = rng.next_int(words.length)
  words[(draw * draw) / words.length]
end

def id_checksum(ids)
  ids.reduce(7) { |hash, id| (hash * 131 + id) % 1_000_000_007 }
end

chk = Checker.new("search_engine")
tokenizer = Tokenizer.new

# --- primitives ---------------------------------------------------------------
chk.eq("tokenizer", tokenizer.tokens("The Quick-Brown foxes, jumped over 2 lazy dogs!"),
       ["quick", "brown", "fox", "jump", "over", "2", "lazy", "dogs"])
chk.eq("stemmer", %w[running quickly boxes jumped cats houses amazingly sing].map { |word| tokenizer.stem(word) },
       ["runn", "quick", "box", "jump", "cats", "hous", "amaz", "sing"])
chk.eq("levenshtein", [%w[kitten sitting], %w[flaw lawn], ["", "abc"], %w[same same]].map { |a, b| EditDistance.levenshtein(a, b) },
       [3, 2, 3, 0])
chk.eq("sorted intersect", SortedLists.intersect([1, 3, 5, 7, 9], [3, 4, 5, 9, 10]), [3, 5, 9])
chk.eq("sorted union", SortedLists.union([1, 3, 5], [2, 3, 6, 7]), [1, 2, 3, 5, 6, 7])
chk.eq("sorted difference", SortedLists.difference([1, 2, 3, 4, 5], [2, 4, 6]), [1, 3, 5])

# --- a tiny hand-checked corpus -----------------------------------------------
small = InvertedIndex.new(tokenizer)
small.add(9001, "", "The quick brown fox jumps over the lazy dog")
small.add(9002, "", "A quick brown dog outpaces a lazy fox")
small.add(9003, "", "Brown quick fox")
small.add(9004, "", "The lazy dog sleeps while quick foxes jump")
query = BooleanQuery.new(small, tokenizer)

chk.eq("small postings", small.doc_ids_for("fox"), [9001, 9002, 9003, 9004])
chk.eq("small document frequency", %w[quick dog sleep cat].map { |term| small.document_frequency(term) }, [4, 3, 1, 0])
chk.eq("phrase: quick brown fox", small.phrase("quick brown fox"), [9001])
chk.eq("phrase: lazy dog", small.phrase("lazy dog"), [9001, 9004])
chk.eq("phrase: quick fox", small.phrase("quick fox"), [9003, 9004])
chk.eq("phrase: brown dog", small.phrase("the brown dog"), [9002])
chk.eq("phrase: no match", small.phrase("dog brown"), [])
chk.eq("boolean AND", query.evaluate("fox AND dog"), [9001, 9002, 9004])
chk.eq("boolean NOT", query.evaluate("fox NOT dog"), [9003])
chk.eq("boolean OR with parentheses", query.evaluate("(jump OR sleeps) AND lazy"), [9001, 9004])
chk.eq("boolean precedence", query.evaluate("outpaces OR sleeps AND fox"), [9002, 9004])
chk.eq("boolean empty result", query.evaluate("quick AND brown NOT fox"), [])
chk.eq("ranking prefers the short document", small.rank("brown fox").first[0], 9003)
chk.eq("ranking orders all matches", small.rank("sleeping dog").map(&:first), [9004, 9002, 9001])
chk.eq("completion", small.complete("o"), ["outpac", "over"])
chk.eq("suggestion", small.suggest("quik"), ["quick", "jump", "dog"])

errors = ["fox AND", "(fox OR dog", "fox ) dog", "AND fox"].map do |text|
  begin
    query.evaluate(text)
    "no error"
  rescue ArgumentError => e
    e.message
  end
end
chk.eq("query syntax errors", errors,
       ["unexpected end of query", "missing ')'", "unexpected token ')'", "unexpected token 'AND'"])

# --- generated corpus ---------------------------------------------------------
rng = Lcg.new(5_551_212)
vocabulary = build_vocabulary(rng, 450)
index = InvertedIndex.new(tokenizer)
documents = Array.new(900) do |id|
  words = Array.new(30 + rng.next_int(70)) { skewed_pick(rng, vocabulary) }
  { id: id, title: words.first(3).join(" "), body: words.join(" ") }
end
documents.each { |doc| index.add(doc[:id], doc[:title], doc[:body]) }
search = BooleanQuery.new(index, tokenizer)

chk.eq("corpus documents", index.doc_count, 900)
chk.eq("corpus tokens", index.token_count, documents.sum { |doc| doc[:body].split.length + 3 })
chk.eq("corpus token count", index.token_count, 60575)
chk.eq("corpus vocabulary", index.vocabulary_size, 337)
chk.near("corpus average length", index.average_length, 67.30555555555556, 1e-9)

common, medium, rare = vocabulary[0], vocabulary[5], vocabulary[300]
frequencies = [common, medium, rare].map { |term| index.document_frequency(term) }
chk.eq("document frequencies", frequencies, [862, 370, 121])
chk.eq("frequencies follow the skew", frequencies == frequencies.sort.reverse, true)

ids_common = index.doc_ids_for(common)
ids_medium = index.doc_ids_for(medium)
ids_rare = index.doc_ids_for(rare)
chk.eq("AND matches Array#&", search.evaluate("#{common} AND #{medium}"), ids_common & ids_medium)
chk.eq("OR matches Array#|", search.evaluate("#{medium} OR #{rare}"), (ids_medium | ids_rare).sort)
chk.eq("NOT matches Array#-", search.evaluate("#{common} NOT #{medium}"), ids_common - ids_medium)
nested = search.evaluate("(#{common} AND #{medium}) OR (#{rare} NOT #{common})")
chk.eq("nested query", nested, ((ids_common & ids_medium) | (ids_rare - ids_common)).sort)
chk.eq("nested query checksum", id_checksum(nested), 880828721)

top_ids = []
best_score = 0.0
60.times do
  terms = Array.new(3) { skewed_pick(rng, vocabulary) }
  results = index.rank(terms.join(" "), 5)
  top_ids.concat(results.map(&:first))
  best_score = results.first[1] if results.first[1] > best_score
end
chk.eq("ranked result count", top_ids.length, 300)
chk.eq("ranked results checksum", id_checksum(top_ids), 647114106)
chk.near("best BM25 score", best_score, 7.115881820724013, 1e-9)

scores = index.rank("#{common} #{rare}", 25).map { |_, score| score }
chk.eq("scores are sorted", scores == scores.sort.reverse, true)

phrase_hits = documents.first(40).sum do |doc|
  words = doc[:body].split
  index.phrase(words[10, 3].join(" ")).include?(doc[:id]) ? 1 : 0
end
chk.eq("every document matches its own phrase", phrase_hits, 40)
chk.eq("phrase result checksum", id_checksum(index.phrase("#{common} #{common}")), 275288687)

chk.eq("completion on the corpus", index.complete("sha", 4), ["shafennim", "shagravel", "shaka", "shakami"])
chk.eq("completion with no match", index.complete("zzz"), [])
chk.eq("suggestion on the corpus", index.suggest(rare[0...-1] + "x"), ["paxmi", "paxlo", "paxtu"])

puts "indexed #{index.doc_count} documents, #{index.token_count} tokens, #{index.vocabulary_size} terms"
puts "top hit for '#{common} #{rare}': doc #{index.rank("#{common} #{rare}").first[0]}"
chk.finish

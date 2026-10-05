# Ordered key-value store
#
# A B-tree (insert with preemptive splits, delete with borrowing and
# merging, range scans, structural validation) fronted by an LRU cache built
# on a doubly linked list, with transactions that roll back through an undo
# log. The workload replays tens of thousands of random operations and
# compares every answer with a plain Hash acting as the reference model.
#
# Self-checking: the store must agree with the model at every step, the
# tree must stay structurally valid, the rest is compared against values
# verified with the reference Ruby implementation, and the first mismatch
# raises.

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
end

# A B-tree of minimum degree t: every node except the root holds between
# t - 1 and 2t - 1 keys, and all leaves sit at the same depth.
class BTree
  class Node
    attr_accessor :keys, :values, :children

    def initialize
      @keys = []
      @values = []
      @children = []
    end

    def leaf?
      @children.empty?
    end
  end

  attr_reader :size

  def initialize(min_degree = 8)
    @t = min_degree
    @root = Node.new
    @size = 0
  end

  def get(key)
    node = @root
    loop do
      index = lower_bound(node.keys, key)
      return node.values[index] if index < node.keys.length && node.keys[index] == key
      return nil if node.leaf?
      node = node.children[index]
    end
  end

  def put(key, value)
    if @root.keys.length == 2 * @t - 1
      new_root = Node.new
      new_root.children << @root
      split_child(new_root, 0)
      @root = new_root
    end
    insert_non_full(@root, key, value)
  end

  # Removes the key; returns whether it was present.
  def delete(key)
    removed = delete_from(@root, key)
    @root = @root.children.first if @root.keys.empty? && !@root.leaf?
    @size -= 1 if removed
    removed
  end

  def each(node = @root, &block)
    node.keys.each_index do |index|
      each(node.children[index], &block) unless node.leaf?
      block.call(node.keys[index], node.values[index])
    end
    each(node.children.last, &block) unless node.leaf?
  end

  def to_a
    pairs = []
    each { |key, value| pairs << [key, value] }
    pairs
  end

  # Yields every pair with low <= key <= high, in key order.
  def each_in_range(low, high, node = @root, &block)
    index = lower_bound(node.keys, low)
    loop do
      each_in_range(low, high, node.children[index], &block) unless node.leaf?
      break if index >= node.keys.length || node.keys[index] > high
      block.call(node.keys[index], node.values[index])
      index += 1
    end
  end

  def height
    levels = 1
    node = @root
    until node.leaf?
      node = node.children.first
      levels += 1
    end
    levels
  end

  def valid?
    leaf_depths = []
    check_node(@root, nil, nil, 1, leaf_depths) && leaf_depths.uniq.length <= 1
  end

  private

  # Index of the first key that is >= the given key.
  def lower_bound(keys, key)
    low = 0
    high = keys.length
    while low < high
      middle = (low + high) / 2
      if keys[middle] < key
        low = middle + 1
      else
        high = middle
      end
    end
    low
  end

  # Splits the full child at `index`, moving its median key up into `parent`.
  def split_child(parent, index)
    child = parent.children[index]
    sibling = Node.new
    median_key = child.keys[@t - 1]
    median_value = child.values[@t - 1]
    sibling.keys = child.keys[@t..]
    sibling.values = child.values[@t..]
    child.keys = child.keys[0, @t - 1]
    child.values = child.values[0, @t - 1]
    unless child.leaf?
      sibling.children = child.children[@t..]
      child.children = child.children[0, @t]
    end
    parent.keys.insert(index, median_key)
    parent.values.insert(index, median_value)
    parent.children.insert(index + 1, sibling)
  end

  def insert_non_full(node, key, value)
    loop do
      index = lower_bound(node.keys, key)
      if index < node.keys.length && node.keys[index] == key
        node.values[index] = value
        return
      end
      if node.leaf?
        node.keys.insert(index, key)
        node.values.insert(index, value)
        @size += 1
        return
      end
      if node.children[index].keys.length == 2 * @t - 1
        split_child(node, index)
        if key == node.keys[index]
          node.values[index] = value
          return
        end
        index += 1 if key > node.keys[index]
      end
      node = node.children[index]
    end
  end

  def delete_from(node, key)
    index = lower_bound(node.keys, key)
    if index < node.keys.length && node.keys[index] == key
      if node.leaf?
        node.keys.delete_at(index)
        node.values.delete_at(index)
      elsif node.children[index].keys.length >= @t
        replacement = rightmost_entry(node.children[index])
        node.keys[index], node.values[index] = replacement
        delete_from(node.children[index], replacement[0])
      elsif node.children[index + 1].keys.length >= @t
        replacement = leftmost_entry(node.children[index + 1])
        node.keys[index], node.values[index] = replacement
        delete_from(node.children[index + 1], replacement[0])
      else
        merge_children(node, index)
        delete_from(node.children[index], key)
      end
      return true
    end
    return false if node.leaf?
    index = fill_child(node, index) if node.children[index].keys.length < @t
    delete_from(node.children[index], key)
  end

  def rightmost_entry(node)
    node = node.children.last until node.leaf?
    [node.keys.last, node.values.last]
  end

  def leftmost_entry(node)
    node = node.children.first until node.leaf?
    [node.keys.first, node.values.first]
  end

  # Makes sure children[index] has at least t keys before descending into
  # it; returns the index of the child to descend into afterwards.
  def fill_child(node, index)
    if index > 0 && node.children[index - 1].keys.length >= @t
      borrow_from_left(node, index)
      index
    elsif index < node.children.length - 1 && node.children[index + 1].keys.length >= @t
      borrow_from_right(node, index)
      index
    elsif index < node.children.length - 1
      merge_children(node, index)
      index
    else
      merge_children(node, index - 1)
      index - 1
    end
  end

  def borrow_from_left(node, index)
    child = node.children[index]
    left = node.children[index - 1]
    child.keys.unshift(node.keys[index - 1])
    child.values.unshift(node.values[index - 1])
    node.keys[index - 1] = left.keys.pop
    node.values[index - 1] = left.values.pop
    child.children.unshift(left.children.pop) unless left.leaf?
  end

  def borrow_from_right(node, index)
    child = node.children[index]
    right = node.children[index + 1]
    child.keys << node.keys[index]
    child.values << node.values[index]
    node.keys[index] = right.keys.shift
    node.values[index] = right.values.shift
    child.children << right.children.shift unless right.leaf?
  end

  # Folds keys[index] and children[index + 1] into children[index].
  def merge_children(node, index)
    left = node.children[index]
    right = node.children[index + 1]
    left.keys << node.keys.delete_at(index)
    left.values << node.values.delete_at(index)
    left.keys.concat(right.keys)
    left.values.concat(right.values)
    left.children.concat(right.children)
    node.children.delete_at(index + 1)
  end

  def check_node(node, low, high, depth, leaf_depths)
    count = node.keys.length
    return false if count > 2 * @t - 1
    return false if depth > 1 && count < @t - 1
    return false unless node.keys.each_cons(2).all? { |a, b| a < b }
    return false if low && count > 0 && node.keys.first <= low
    return false if high && count > 0 && node.keys.last >= high
    if node.leaf?
      leaf_depths << depth
      return true
    end
    return false unless node.children.length == count + 1
    node.children.each_with_index.all? do |child, index|
      child_low = index.zero? ? low : node.keys[index - 1]
      child_high = index == count ? high : node.keys[index]
      check_node(child, child_low, child_high, depth + 1, leaf_depths)
    end
  end
end

# Least-recently-used cache: a Hash for lookup plus a doubly linked list
# that keeps the entries in order of use.
class LruCache
  Entry = Struct.new(:key, :value, :older, :newer)

  attr_reader :hits, :misses, :evictions

  def initialize(capacity)
    @capacity = capacity
    @entries = {}
    @oldest = nil
    @newest = nil
    @hits = 0
    @misses = 0
    @evictions = 0
  end

  def size
    @entries.size
  end

  def get(key)
    entry = @entries[key]
    if entry.nil?
      @misses += 1
      return nil
    end
    @hits += 1
    touch(entry)
    entry.value
  end

  def put(key, value)
    entry = @entries[key]
    if entry
      entry.value = value
      touch(entry)
      return
    end
    entry = Entry.new(key, value, nil, nil)
    @entries[key] = entry
    append(entry)
    evict if @entries.size > @capacity
  end

  def delete(key)
    entry = @entries.delete(key)
    unlink(entry) if entry
  end

  def keys_oldest_first
    keys = []
    entry = @oldest
    while entry
      keys << entry.key
      entry = entry.newer
    end
    keys
  end

  private

  def touch(entry)
    return if entry.equal?(@newest)
    unlink(entry)
    append(entry)
  end

  def append(entry)
    entry.older = @newest
    entry.newer = nil
    @newest.newer = entry if @newest
    @newest = entry
    @oldest ||= entry
  end

  def unlink(entry)
    if entry.older
      entry.older.newer = entry.newer
    else
      @oldest = entry.newer
    end
    if entry.newer
      entry.newer.older = entry.older
    else
      @newest = entry.older
    end
  end

  def evict
    victim = @oldest
    unlink(victim)
    @entries.delete(victim.key)
    @evictions += 1
  end
end

class Rollback < StandardError
end

class KeyValueStore
  attr_reader :tree, :cache

  def initialize(cache_capacity:)
    @tree = BTree.new(8)
    @cache = LruCache.new(cache_capacity)
    @undo = nil
  end

  def size
    @tree.size
  end

  def get(key)
    cached = @cache.get(key)
    return cached unless cached.nil?
    value = @tree.get(key)
    @cache.put(key, value) unless value.nil?
    value
  end

  def put(key, value)
    @undo << [key, @tree.get(key)] if @undo
    @tree.put(key, value)
    @cache.put(key, value)
  end

  def delete(key)
    @undo << [key, @tree.get(key)] if @undo
    @cache.delete(key)
    @tree.delete(key)
  end

  def range(low, high)
    pairs = []
    @tree.each_in_range(low, high) { |key, value| pairs << [key, value] }
    pairs
  end

  # Runs the block atomically. Raising Rollback inside it restores every key
  # the block touched; returns whether the transaction committed.
  def transaction
    raise ArgumentError, "transactions cannot be nested" if @undo
    @undo = []
    begin
      yield self
      true
    rescue Rollback
      log = @undo
      @undo = nil
      log.reverse_each { |key, old_value| old_value.nil? ? delete(key) : put(key, old_value) }
      false
    ensure
      @undo = nil
    end
  end
end

def pair_checksum(pairs)
  pairs.reduce(7) { |hash, (key, value)| (hash * 131 + key * 7 + value) % 1_000_000_007 }
end

chk = Checker.new("btree_kv_store")

# --- b-tree on its own --------------------------------------------------------
tree = BTree.new(2)
[50, 20, 80, 10, 30, 70, 90, 60, 40, 100, 25, 35].each { |key| tree.put(key, key * 10) }
chk.eq("small tree order", tree.to_a.map(&:first), [10, 20, 25, 30, 35, 40, 50, 60, 70, 80, 90, 100])
chk.eq("small tree lookup", [tree.get(35), tree.get(100), tree.get(55)], [350, 1000, nil])
chk.eq("small tree shape", [tree.size, tree.height, tree.valid?], [12, 3, true])
tree.put(30, -1)
chk.eq("overwrite keeps the size", [tree.get(30), tree.size], [-1, 12])
in_range = []
tree.each_in_range(25, 60) { |key, _| in_range << key }
chk.eq("small tree range", in_range, [25, 30, 35, 40, 50, 60])
chk.eq("delete results", [tree.delete(50), tree.delete(55), tree.delete(10)], [true, false, true])
chk.eq("after deletes", [tree.to_a.map(&:first), tree.valid?], [[20, 25, 30, 35, 40, 60, 70, 80, 90, 100], true])
tree.to_a.each { |key, _| tree.delete(key) }
chk.eq("emptied tree", [tree.size, tree.height, tree.to_a, tree.valid?], [0, 1, [], true])

sequential = BTree.new(8)
5000.times { |key| sequential.put(key, key * 2) }
chk.eq("sequential inserts", [sequential.size, sequential.valid?], [5000, true])
chk.eq("sequential height", sequential.height, 4)
(0...5000).step(2) { |key| sequential.delete(key) }
chk.eq("after deleting the even keys", [sequential.size, sequential.valid?, sequential.get(2468), sequential.get(2469)],
       [2500, true, nil, 4938])
chk.eq("remaining keys are odd", sequential.to_a.map(&:first) == (1...5000).step(2).to_a, true)
4999.downto(0) { |key| sequential.delete(key) }
chk.eq("descending deletes empty the tree", [sequential.size, sequential.height, sequential.valid?], [0, 1, true])

# --- lru cache ----------------------------------------------------------------
cache = LruCache.new(3)
cache.put(:a, 1)
cache.put(:b, 2)
cache.put(:c, 3)
cache.get(:a)
cache.put(:d, 4)
chk.eq("lru evicts the least recent", cache.keys_oldest_first, [:c, :a, :d])
chk.eq("lru lookups", [cache.get(:b), cache.get(:c), cache.get(:a)], [nil, 3, 1])
cache.put(:d, 40)
cache.delete(:c)
chk.eq("lru after update and delete", [cache.keys_oldest_first, cache.size], [[:a, :d], 2])
chk.eq("lru statistics", [cache.hits, cache.misses, cache.evictions], [3, 1, 1])

# --- randomized comparison against a Hash -------------------------------------
rng = Lcg.new(1_234_567)
store = KeyValueStore.new(cache_capacity: 256)
model = {}
mismatches = 0
operations = Hash.new(0)
48_000.times do |step|
  key = rng.next_int(3000)
  case rng.next_int(10)
  when 0..4
    value = rng.next_int(1_000_000)
    store.put(key, value)
    model[key] = value
    operations[:put] += 1
  when 5..7
    mismatches += 1 unless store.get(key) == model[key]
    operations[:get] += 1
  else
    mismatches += 1 unless store.delete(key) == model.key?(key)
    model.delete(key)
    operations[:delete] += 1
  end
  mismatches += 1 if step % 3000 == 0 && !store.tree.valid?
end
chk.eq("operation mix", operations, {put: 23881, get: 14463, delete: 9656})
chk.eq("store agrees with the model", mismatches, 0)
chk.eq("final size", store.size, model.size)
chk.eq("final size value", store.size, 2164)
chk.eq("final contents", store.tree.to_a == model.sort, true)
chk.eq("final tree is valid", store.tree.valid?, true)
chk.eq("final height", store.tree.height, 4)
chk.eq("contents checksum", pair_checksum(store.tree.to_a), 32610883)
chk.eq("range scan", store.range(1000, 1100), model.select { |key, _| key.between?(1000, 1100) }.sort)
chk.eq("empty range", store.range(5000, 6000), [])
chk.eq("cache stays within capacity", store.cache.size <= 256, true)
chk.eq("cache statistics", [store.cache.hits, store.cache.misses, store.cache.evictions], [1233, 13230, 29008])

# --- transactions -------------------------------------------------------------
before = store.tree.to_a
committed = store.transaction do |tx|
  tx.put(9001, 1)
  tx.put(9002, 2)
  tx.delete(before.first[0])
end
chk.eq("commit returns true", committed, true)
chk.eq("commit is visible", [store.get(9001), store.get(9002), store.get(before.first[0]), store.size],
       [1, 2, nil, before.length + 1])

snapshot = store.tree.to_a
rolled_back = store.transaction do |tx|
  400.times do
    key = rng.next_int(3200)
    rng.next_int(3).zero? ? tx.delete(key) : tx.put(key, rng.next_int(1000))
  end
  raise Rollback, "abort after #{tx.size} keys"
end
chk.eq("rollback returns false", rolled_back, false)
chk.eq("rollback restores every key", store.tree.to_a == snapshot, true)
chk.eq("rollback keeps the tree valid", store.tree.valid?, true)
chk.eq("rollback keeps the cache honest", snapshot.first(300).all? { |key, value| store.get(key) == value }, true)

begin
  store.transaction { |tx| tx.transaction { |inner| inner.put(1, 1) } }
  outcome = "no error"
rescue ArgumentError => e
  outcome = e.message
end
chk.eq("nested transactions are rejected", outcome, "transactions cannot be nested")
chk.eq("a failed transaction releases the lock", store.transaction { |tx| tx.put(9003, 3) }, true)

puts "store: #{store.size} keys, height #{store.tree.height}"
puts "cache: #{store.cache.hits} hits, #{store.cache.misses} misses, #{store.cache.evictions} evictions"
chk.finish

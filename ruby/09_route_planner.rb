# Route planner: a graph algorithm toolkit
#
# Dijkstra with a binary heap, Bellman-Ford, Floyd-Warshall, A* on a
# weighted grid, Kruskal (union-find) and Prim minimum spanning trees,
# Tarjan's strongly connected components, Kahn's topological sort and
# Edmonds-Karp maximum flow. The workload runs them on generated graphs and
# makes independent algorithms agree with each other.
#
# Self-checking: textbook examples are embedded, different algorithms for
# the same problem must agree, the rest is compared against values verified
# with the reference Ruby implementation, and the first mismatch raises.

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

INFINITY = Float::INFINITY

# A binary min-heap of [priority, value] pairs.
class PriorityQueue
  def initialize
    @items = []
  end

  def empty?
    @items.empty?
  end

  def size
    @items.length
  end

  def push(priority, value)
    @items << [priority, value]
    index = @items.length - 1
    while index > 0
      parent = (index - 1) / 2
      break if @items[parent][0] <= @items[index][0]
      @items[parent], @items[index] = @items[index], @items[parent]
      index = parent
    end
  end

  def pop
    top = @items.first
    last = @items.pop
    return top if @items.empty?
    @items[0] = last
    index = 0
    loop do
      left = 2 * index + 1
      right = left + 1
      smallest = index
      smallest = left if left < @items.length && @items[left][0] < @items[smallest][0]
      smallest = right if right < @items.length && @items[right][0] < @items[smallest][0]
      break if smallest == index
      @items[index], @items[smallest] = @items[smallest], @items[index]
      index = smallest
    end
    top
  end
end

class UnionFind
  attr_reader :components

  def initialize(size)
    @parent = (0...size).to_a
    @rank = Array.new(size, 0)
    @components = size
  end

  def find(node)
    root = node
    root = @parent[root] until @parent[root] == root
    until @parent[node] == root
      next_node = @parent[node]
      @parent[node] = root
      node = next_node
    end
    root
  end

  def union(a, b)
    root_a = find(a)
    root_b = find(b)
    return false if root_a == root_b
    root_a, root_b = root_b, root_a if @rank[root_a] < @rank[root_b]
    @parent[root_b] = root_a
    @rank[root_a] += 1 if @rank[root_a] == @rank[root_b]
    @components -= 1
    true
  end
end

class NegativeCycleError < StandardError
end

class Graph
  attr_reader :node_count, :edges

  def initialize(node_count, directed: false)
    @node_count = node_count
    @directed = directed
    @adjacency = Array.new(node_count) { [] }
    @edges = []
  end

  def add_edge(from, to, weight = 1)
    @adjacency[from] << [to, weight]
    @adjacency[to] << [from, weight] unless @directed
    @edges << [from, to, weight]
    self
  end

  def neighbors(node)
    @adjacency[node]
  end

  # Shortest distances and predecessor links from one source.
  def dijkstra(source)
    distance = Array.new(@node_count, INFINITY)
    previous = Array.new(@node_count)
    distance[source] = 0
    queue = PriorityQueue.new
    queue.push(0, source)
    until queue.empty?
      cost, node = queue.pop
      next if cost > distance[node]
      @adjacency[node].each do |neighbor, weight|
        candidate = cost + weight
        next unless candidate < distance[neighbor]
        distance[neighbor] = candidate
        previous[neighbor] = node
        queue.push(candidate, neighbor)
      end
    end
    [distance, previous]
  end

  def self.path(previous, target)
    path = [target]
    path.unshift(previous[path.first]) while previous[path.first]
    path
  end

  def bellman_ford(source)
    distance = Array.new(@node_count, INFINITY)
    distance[source] = 0
    relaxations = @directed ? @edges : @edges + @edges.map { |from, to, weight| [to, from, weight] }
    (@node_count - 1).times do
      changed = false
      relaxations.each do |from, to, weight|
        next unless distance[from] + weight < distance[to]
        distance[to] = distance[from] + weight
        changed = true
      end
      return distance unless changed
    end
    relaxations.each do |from, to, weight|
      raise NegativeCycleError, "negative cycle through node #{to}" if distance[from] + weight < distance[to]
    end
    distance
  end

  def floyd_warshall
    distance = Array.new(@node_count) { |i| Array.new(@node_count) { |j| i == j ? 0 : INFINITY } }
    @adjacency.each_with_index do |edges, from|
      edges.each { |to, weight| distance[from][to] = weight if weight < distance[from][to] }
    end
    @node_count.times do |via|
      via_row = distance[via]
      @node_count.times do |from|
        row = distance[from]
        through = row[via]
        next if through == INFINITY
        @node_count.times do |to|
          candidate = through + via_row[to]
          row[to] = candidate if candidate < row[to]
        end
      end
    end
    distance
  end

  def kruskal
    forest = UnionFind.new(@node_count)
    chosen = @edges.sort_by { |from, to, weight| [weight, from, to] }.select { |from, to, _| forest.union(from, to) }
    [chosen.sum { |_, _, weight| weight }, chosen.length]
  end

  def prim(start = 0)
    visited = Array.new(@node_count, false)
    queue = PriorityQueue.new
    queue.push(0, start)
    total = 0
    count = 0
    until queue.empty?
      weight, node = queue.pop
      next if visited[node]
      visited[node] = true
      total += weight
      count += 1
      @adjacency[node].each { |neighbor, cost| queue.push(cost, neighbor) unless visited[neighbor] }
    end
    [total, count - 1]
  end

  # Tarjan's algorithm. Components come out in reverse topological order.
  def strongly_connected_components
    index_of = Array.new(@node_count)
    low = Array.new(@node_count, 0)
    on_stack = Array.new(@node_count, false)
    stack = []
    components = []
    counter = 0

    visit = lambda do |node|
      index_of[node] = counter
      low[node] = counter
      counter += 1
      stack.push(node)
      on_stack[node] = true
      @adjacency[node].each do |neighbor, _|
        if index_of[neighbor].nil?
          visit.call(neighbor)
          low[node] = [low[node], low[neighbor]].min
        elsif on_stack[neighbor]
          low[node] = [low[node], index_of[neighbor]].min
        end
      end
      if low[node] == index_of[node]
        component = []
        loop do
          member = stack.pop
          on_stack[member] = false
          component << member
          break if member == node
        end
        components << component.sort
      end
    end

    @node_count.times { |node| visit.call(node) if index_of[node].nil? }
    components
  end

  # Kahn's algorithm; nil when the graph has a cycle.
  def topological_order
    indegree = Array.new(@node_count, 0)
    @edges.each { |_, to, _| indegree[to] += 1 }
    ready = (0...@node_count).select { |node| indegree[node].zero? }
    order = []
    until ready.empty?
      node = ready.shift
      order << node
      @adjacency[node].each do |neighbor, _|
        indegree[neighbor] -= 1
        ready << neighbor if indegree[neighbor].zero?
      end
    end
    order.length == @node_count ? order : nil
  end
end

# Edmonds-Karp on a dense capacity matrix.
class FlowNetwork
  def initialize(node_count)
    @node_count = node_count
    @capacity = Array.new(node_count) { Array.new(node_count, 0) }
  end

  def add_edge(from, to, capacity)
    @capacity[from][to] += capacity
  end

  def max_flow(source, sink)
    @residual = @capacity.map(&:dup)
    total = 0
    loop do
      parent = augmenting_path(source, sink)
      break if parent.nil?
      bottleneck = INFINITY
      node = sink
      until node == source
        bottleneck = [bottleneck, @residual[parent[node]][node]].min
        node = parent[node]
      end
      node = sink
      until node == source
        @residual[parent[node]][node] -= bottleneck
        @residual[node][parent[node]] += bottleneck
        node = parent[node]
      end
      total += bottleneck
    end
    total
  end

  # Capacity crossing from the source side of the residual graph to the rest.
  def min_cut_capacity(source)
    reachable = Array.new(@node_count, false)
    reachable[source] = true
    frontier = [source]
    until frontier.empty?
      node = frontier.shift
      @node_count.times do |other|
        next if reachable[other] || @residual[node][other] <= 0
        reachable[other] = true
        frontier << other
      end
    end
    total = 0
    @node_count.times do |from|
      @node_count.times do |to|
        total += @capacity[from][to] if reachable[from] && !reachable[to]
      end
    end
    total
  end

  private

  def augmenting_path(source, sink)
    parent = Array.new(@node_count)
    parent[source] = source
    frontier = [source]
    until frontier.empty?
      node = frontier.shift
      @node_count.times do |other|
        next unless parent[other].nil? && @residual[node][other] > 0
        parent[other] = node
        return parent if other == sink
        frontier << other
      end
    end
    nil
  end
end

class GridMap
  STEPS = [[0, 1], [1, 0], [0, -1], [-1, 0]].freeze

  attr_reader :width, :height

  # Each open cell has an entry cost of 1..9; nil marks a wall.
  def initialize(width, height, rng)
    @width = width
    @height = height
    @cells = Array.new(height) do |y|
      Array.new(width) do |x|
        corner = (x.zero? && y.zero?) || (x == width - 1 && y == height - 1)
        !corner && rng.next_int(100) < 22 ? nil : 1 + rng.next_int(9)
      end
    end
  end

  def cost(x, y)
    @cells[y][x]
  end

  def open_neighbors(x, y)
    STEPS.map { |dx, dy| [x + dx, y + dy] }
         .select { |nx, ny| nx.between?(0, @width - 1) && ny.between?(0, @height - 1) && @cells[ny][nx] }
  end

  # A* with the Manhattan distance, admissible because every step costs >= 1.
  def astar(start, goal)
    best = { start => 0 }
    came_from = {}
    queue = PriorityQueue.new
    queue.push(0, start)
    expanded = 0
    until queue.empty?
      _, current = queue.pop
      expanded += 1
      return [best[current], Graph.path(came_from, current), expanded] if current == goal
      open_neighbors(current[0], current[1]).each do |neighbor|
        candidate = best[current] + cost(neighbor[0], neighbor[1])
        next if best.key?(neighbor) && candidate >= best[neighbor]
        best[neighbor] = candidate
        came_from[neighbor] = current
        heuristic = (goal[0] - neighbor[0]).abs + (goal[1] - neighbor[1]).abs
        queue.push(candidate + heuristic, neighbor)
      end
    end
    nil
  end

  def to_graph
    graph = Graph.new(@width * @height, directed: true)
    @height.times do |y|
      @width.times do |x|
        next unless @cells[y][x]
        open_neighbors(x, y).each { |nx, ny| graph.add_edge(y * @width + x, ny * @width + nx, cost(nx, ny)) }
      end
    end
    graph
  end
end

def checksum(values)
  values.reduce(7) { |hash, value| (hash * 131 + value) % 1_000_000_007 }
end

chk = Checker.new("route_planner")

# --- building blocks ----------------------------------------------------------
queue = PriorityQueue.new
[[5, "e"], [1, "a"], [4, "d"], [2, "b"], [3, "c"], [1, "a2"]].each { |priority, value| queue.push(priority, value) }
chk.eq("priority queue order", Array.new(queue.size) { queue.pop[0] }, [1, 1, 2, 3, 4, 5])

sets = UnionFind.new(8)
[[0, 1], [2, 3], [1, 3], [5, 6]].each { |a, b| sets.union(a, b) }
chk.eq("union-find components", sets.components, 4)
chk.eq("union-find membership", [sets.find(0) == sets.find(2), sets.find(4) == sets.find(5), sets.union(3, 0)], [true, false, false])

# --- textbook shortest paths --------------------------------------------------
city = Graph.new(6)
[[0, 1, 7], [0, 2, 9], [0, 5, 14], [1, 2, 10], [1, 3, 15], [2, 3, 11], [2, 5, 2], [3, 4, 6], [4, 5, 9]].each do |from, to, weight|
  city.add_edge(from, to, weight)
end
distance, previous = city.dijkstra(0)
chk.eq("dijkstra distances", distance, [0, 7, 9, 20, 20, 11])
chk.eq("dijkstra path", Graph.path(previous, 4), [0, 2, 5, 4])
chk.eq("bellman-ford agrees", city.bellman_ford(0), distance)
chk.eq("floyd-warshall row", city.floyd_warshall[0], distance)
chk.eq("kruskal", city.kruskal, [33, 5])
chk.eq("prim", city.prim, [33, 5])

arbitrage = Graph.new(4, directed: true)
[[0, 1, 4], [1, 2, -6], [2, 3, 1], [3, 1, 2]].each { |from, to, weight| arbitrage.add_edge(from, to, weight) }
begin
  arbitrage.bellman_ford(0)
  outcome = "no error"
rescue NegativeCycleError => e
  outcome = e.message
end
chk.eq("negative cycle detected", outcome.start_with?("negative cycle"), true)
negative = Graph.new(4, directed: true)
[[0, 1, 4], [0, 2, 5], [1, 3, -2], [2, 1, -3]].each { |from, to, weight| negative.add_edge(from, to, weight) }
chk.eq("negative edges without a cycle", negative.bellman_ford(0), [0, 2, 5, 0])

# --- generated road network ---------------------------------------------------
rng = Lcg.new(424_242)
roads = Graph.new(1200)
1199.times { |node| roads.add_edge(node, node + 1, 1 + rng.next_int(40)) }
4200.times do
  from = rng.next_int(1200)
  to = rng.next_int(1200)
  roads.add_edge(from, to, 1 + rng.next_int(60)) unless from == to
end
road_distance, road_previous = roads.dijkstra(0)
chk.eq("road network edges", roads.edges.length, 5398)
chk.eq("road dijkstra equals bellman-ford", road_distance == roads.bellman_ford(0), true)
chk.eq("road distance checksum", checksum(road_distance), 893200644)
farthest = road_distance.each_with_index.max[1]
route = Graph.path(road_previous, farthest)
route_cost = route.each_cons(2).sum do |from, to|
  roads.neighbors(from).select { |neighbor, _| neighbor == to }.map { |_, weight| weight }.min
end
chk.eq("farthest node", [farthest, road_distance[farthest]], [1145, 76])
chk.eq("route starts at the source", route.first, 0)
chk.eq("route cost equals its distance", route_cost, road_distance[farthest])
chk.eq("kruskal equals prim", roads.kruskal, roads.prim)
chk.eq("spanning tree weight", roads.kruskal, [9119, 1199])

district = Graph.new(100)
99.times { |node| district.add_edge(node, node + 1, 1 + rng.next_int(30)) }
400.times do
  from = rng.next_int(100)
  to = rng.next_int(100)
  district.add_edge(from, to, 1 + rng.next_int(50)) unless from == to
end
all_pairs = district.floyd_warshall
chk.eq("floyd-warshall equals dijkstra from every node", (0...100).all? { |node| all_pairs[node] == district.dijkstra(node)[0] }, true)
chk.eq("all-pairs is symmetric", all_pairs == all_pairs.transpose, true)
chk.eq("district diameter", all_pairs.flatten.max, 63)
chk.eq("all-pairs checksum", checksum(all_pairs.flatten), 944888175)

# --- directed graphs ----------------------------------------------------------
web = Graph.new(300, directed: true)
520.times { web.add_edge(rng.next_int(300), rng.next_int(300)) }
components = web.strongly_connected_components
chk.eq("components cover every node", components.flatten.sort, (0...300).to_a)
chk.eq("component count", components.length, 150)
chk.eq("largest component", components.map(&:length).max, 151)
component_of = {}
components.each_with_index { |members, id| members.each { |node| component_of[node] = id } }
condensed = Graph.new(components.length, directed: true)
web.edges.map { |from, to, _| [component_of[from], component_of[to]] }.uniq.each do |from, to|
  condensed.add_edge(from, to) unless from == to
end
order = condensed.topological_order
chk.eq("condensation is acyclic", order.nil?, false)
rank = {}
order.each_with_index { |node, position| rank[node] = position }
chk.eq("topological order respects every edge", condensed.edges.all? { |from, to, _| rank[from] < rank[to] }, true)
chk.eq("tarjan emits reverse topological order", condensed.edges.all? { |from, to, _| from > to }, true)
chk.eq("a cycle has no topological order", web.topological_order, nil)

build = Graph.new(6, directed: true)
[[5, 2], [5, 0], [4, 0], [4, 1], [2, 3], [3, 1]].each { |from, to| build.add_edge(from, to) }
chk.eq("topological sort example", build.topological_order, [4, 5, 2, 0, 3, 1])

# --- maximum flow -------------------------------------------------------------
pipes = FlowNetwork.new(6)
[[0, 1, 16], [0, 2, 13], [1, 3, 12], [2, 1, 4], [2, 4, 14], [3, 2, 9], [3, 5, 20], [4, 3, 7], [4, 5, 4]].each do |from, to, capacity|
  pipes.add_edge(from, to, capacity)
end
chk.eq("max flow example", pipes.max_flow(0, 5), 23)
chk.eq("min cut example", pipes.min_cut_capacity(0), 23)

grid_flow = FlowNetwork.new(40)
220.times do
  from = rng.next_int(39)
  to = 1 + rng.next_int(39)
  grid_flow.add_edge(from, to, 1 + rng.next_int(25)) unless from == to
end
flow = grid_flow.max_flow(0, 39)
chk.eq("max flow equals min cut", flow, grid_flow.min_cut_capacity(0))
chk.eq("generated max flow", flow, 16)

# --- grid pathfinding ---------------------------------------------------------
grid = GridMap.new(48, 36, Lcg.new(2718))
goal = [47, 35]
cost, steps, expanded = grid.astar([0, 0], goal)
grid_distance, = grid.to_graph.dijkstra(0)
chk.eq("a-star equals dijkstra", cost, grid_distance[35 * 48 + 47])
chk.eq("a-star cost", cost, 293)
chk.eq("a-star path length", steps.length, 83)
chk.eq("a-star path endpoints", [steps.first, steps.last], [[0, 0], goal])
chk.eq("a-star path is contiguous", steps.each_cons(2).all? { |a, b| (a[0] - b[0]).abs + (a[1] - b[1]).abs == 1 }, true)
chk.eq("a-star path cost", steps.drop(1).sum { |x, y| grid.cost(x, y) }, cost)
chk.eq("a-star expands fewer nodes than the grid holds", expanded < 48 * 36, true)
reachable = grid_distance.count { |value| value != INFINITY }
chk.eq("reachable cells", reachable, 1369)

puts "road network: #{roads.edges.length} roads, farthest node #{farthest} at distance #{road_distance[farthest]}"
puts "web graph: #{components.length} strongly connected components, largest #{components.map(&:length).max}"
puts "grid: cost #{cost} over #{steps.length - 1} steps, #{expanded} nodes expanded"
chk.finish

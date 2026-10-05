# Discrete-event simulation of a service centre
#
# Customers arrive at random intervals, wait in a priority line (VIPs
# first, otherwise first come first served) and are handled by a pool of
# servers. A binary-heap event queue drives the clock. The simulation
# reports waiting-time percentiles, queue lengths and server utilization
# for several staffing levels, the way a capacity planner would use it.
# Time is kept in integer ticks so every run is exactly reproducible.
#
# Self-checking: conservation laws are asserted on every run, the rest is
# compared against values verified with the reference Ruby implementation,
# and the first mismatch raises.

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

module Statistics
  def mean(values)
    values.empty? ? 0.0 : values.sum.to_f / values.length
  end

  # Nearest-rank percentile.
  def percentile(values, percent)
    return 0 if values.empty?
    sorted = values.sort
    rank = (percent * sorted.length / 100.0).ceil
    sorted[[rank, 1].max - 1]
  end

  def histogram(values, bucket_width)
    buckets = Hash.new(0)
    values.each { |value| buckets[value / bucket_width * bucket_width] += 1 }
    buckets.sort.to_h
  end
end

Event = Struct.new(:time, :sequence, :kind, :subject) do
  include Comparable

  def <=>(other)
    time == other.time ? sequence <=> other.sequence : time <=> other.time
  end
end

Customer = Struct.new(:id, :vip, :arrival, :service_time, :start, :finish, :server_id) do
  def wait
    start - arrival
  end
end

class EventQueue
  def initialize
    @heap = []
    @sequence = 0
  end

  def empty?
    @heap.empty?
  end

  def schedule(time, kind, subject)
    @sequence += 1
    @heap << Event.new(time, @sequence, kind, subject)
    index = @heap.length - 1
    while index > 0
      parent = (index - 1) / 2
      break if @heap[parent] <= @heap[index]
      @heap[parent], @heap[index] = @heap[index], @heap[parent]
      index = parent
    end
  end

  def next_event
    top = @heap.first
    last = @heap.pop
    return top if @heap.empty?
    @heap[0] = last
    index = 0
    loop do
      left = 2 * index + 1
      right = left + 1
      smallest = index
      smallest = left if left < @heap.length && @heap[left] < @heap[smallest]
      smallest = right if right < @heap.length && @heap[right] < @heap[smallest]
      break if smallest == index
      @heap[index], @heap[smallest] = @heap[smallest], @heap[index]
      index = smallest
    end
    top
  end
end

class Server
  attr_reader :id, :busy_time, :served
  attr_accessor :customer

  def initialize(id)
    @id = id
    @busy_time = 0
    @served = 0
    @customer = nil
  end

  def idle?
    @customer.nil?
  end

  def begin_service(customer, now)
    @customer = customer
    customer.start = now
    customer.server_id = @id
    customer.finish = now + customer.service_time
  end

  def end_service
    finished = @customer
    @busy_time += finished.service_time
    @served += 1
    @customer = nil
    finished
  end
end

class ServiceCentre
  include Statistics

  attr_reader :customers, :servers, :clock, :longest_line, :line_area

  def initialize(server_count:, customer_count:, seed:, mean_gap: 6, mean_service: 20, vip_percent: 10)
    @servers = Array.new(server_count) { |id| Server.new(id) }
    @customer_count = customer_count
    @rng = Lcg.new(seed)
    @mean_gap = mean_gap
    @mean_service = mean_service
    @vip_percent = vip_percent
    @events = EventQueue.new
    @vip_line = []
    @regular_line = []
    @customers = []
    @clock = 0
    @longest_line = 0
    @line_area = 0
  end

  def run
    schedule_arrival(0)
    until @events.empty?
      event = @events.next_event
      @line_area += line_length * (event.time - @clock)
      @clock = event.time
      case event.kind
      when :arrival then handle_arrival(event.subject)
      when :departure then handle_departure(event.subject)
      end
    end
    self
  end

  def waits
    @customers.map(&:wait)
  end

  def report
    all = waits
    {
      served: @customers.count(&:finish),
      makespan: @clock,
      mean_wait: mean(all).round(3),
      median_wait: percentile(all, 50),
      p90_wait: percentile(all, 90),
      p99_wait: percentile(all, 99),
      max_wait: all.max,
      vip_mean_wait: mean(@customers.select(&:vip).map(&:wait)).round(3),
      longest_line: @longest_line,
      mean_line: (@line_area.to_f / @clock).round(3),
      utilization: (100.0 * @servers.sum(&:busy_time) / (@servers.length * @clock)).round(2)
    }
  end

  private

  def line_length
    @vip_line.length + @regular_line.length
  end

  # Uniform on 1..(2 * mean - 1), so the average is `mean`.
  def draw(mean)
    1 + @rng.next_int(2 * mean - 1)
  end

  def schedule_arrival(now)
    return if @customers.length >= @customer_count
    arrival = now + draw(@mean_gap)
    customer = Customer.new(@customers.length, @rng.next_int(100) < @vip_percent, arrival, draw(@mean_service))
    @customers << customer
    @events.schedule(arrival, :arrival, customer)
  end

  def handle_arrival(customer)
    schedule_arrival(@clock)
    server = @servers.find(&:idle?)
    if server
      start_service(server, customer)
    else
      (customer.vip ? @vip_line : @regular_line) << customer
      @longest_line = line_length if line_length > @longest_line
    end
  end

  def handle_departure(server)
    server.end_service
    waiting = @vip_line.shift || @regular_line.shift
    start_service(server, waiting) if waiting
  end

  def start_service(server, customer)
    server.begin_service(customer, @clock)
    @events.schedule(customer.finish, :departure, server)
  end
end

def simulate(server_count, customer_count)
  ServiceCentre.new(server_count: server_count, customer_count: customer_count, seed: 77_077).run
end

# True when no server ever handled two customers at once.
def servers_never_overlap?(centre)
  centre.customers.group_by(&:server_id).all? do |_, handled|
    handled.sort_by(&:start).each_cons(2).all? { |earlier, later| later.start >= earlier.finish }
  end
end

def text_checksum(text)
  hash = 7
  text.each_byte { |byte| hash = (hash * 131 + byte) % 1_000_000_007 }
  hash
end

chk = Checker.new("event_simulation")
stats = Object.new.extend(Statistics)

# --- building blocks ----------------------------------------------------------
chk.eq("mean", stats.mean([2, 4, 4, 4, 5, 5, 7, 9]), 5.0)
chk.eq("mean of nothing", stats.mean([]), 0.0)
chk.eq("percentiles", [50, 90, 99, 100].map { |p| stats.percentile((1..20).to_a.reverse, p) }, [10, 18, 20, 20])
chk.eq("histogram", stats.histogram([0, 3, 9, 10, 11, 25, 29, 30], 10), { 0 => 3, 10 => 2, 20 => 2, 30 => 1 })

events = EventQueue.new
[[30, :c], [10, :a], [20, :b], [10, :a2], [5, :first]].each { |time, kind| events.schedule(time, kind, nil) }
drained = []
drained << events.next_event.kind until events.empty?
chk.eq("events fire in time order, ties by schedule order", drained, [:first, :a, :a2, :b, :c])
chk.eq("events are comparable", Event.new(5, 2, :x, nil) > Event.new(5, 1, :y, nil), true)

# --- a queue small enough to follow by hand ------------------------------------
tiny = ServiceCentre.new(server_count: 1, customer_count: 5, seed: 12, mean_gap: 3, mean_service: 4, vip_percent: 0).run
chk.eq("tiny arrivals", tiny.customers.map(&:arrival), [3, 8, 9, 11, 14])
chk.eq("tiny service times", tiny.customers.map(&:service_time), [5, 6, 4, 5, 5])
chk.eq("tiny starts", tiny.customers.map(&:start), [3, 8, 14, 18, 23])
chk.eq("tiny is first come first served", tiny.customers.map(&:start), tiny.customers.map(&:start).sort)
chk.eq("tiny single server is back to back",
       tiny.customers.each_cons(2).all? { |a, b| b.start == [a.finish, b.arrival].max }, true)

# --- staffing scenarios -------------------------------------------------------
customer_count = 6000
scenarios = {}
[3, 4, 5, 6].each do |server_count|
  centre = simulate(server_count, customer_count)
  scenarios[server_count] = centre
  chk.eq("#{server_count} servers: everyone is served", centre.customers.count(&:finish), customer_count)
  chk.eq("#{server_count} servers: nobody starts before arriving", centre.customers.all? { |c| c.start >= c.arrival }, true)
  chk.eq("#{server_count} servers: service takes its drawn time",
         centre.customers.all? { |c| c.finish - c.start == c.service_time }, true)
  chk.eq("#{server_count} servers: no server double-books", servers_never_overlap?(centre), true)
  chk.eq("#{server_count} servers: busy time is conserved",
         centre.servers.sum(&:busy_time), centre.customers.sum(&:service_time))
  chk.eq("#{server_count} servers: served counts add up", centre.servers.sum(&:served), customer_count)
  chk.eq("#{server_count} servers: line area equals total waiting", centre.line_area, centre.waits.sum)
end

arrivals = scenarios.values.map { |centre| centre.customers.map(&:arrival) }
chk.eq("every scenario sees the same arrivals", arrivals.uniq.length, 1)

reports = scenarios.transform_values(&:report)
mean_waits = reports.values.map { |report| report[:mean_wait] }
chk.eq("more servers never wait longer", mean_waits, mean_waits.sort.reverse)
chk.eq("vips wait less when the line is long", reports[3][:vip_mean_wait] < reports[3][:mean_wait], true)
chk.eq("report with 3 servers", reports[3], {served: 6000, makespan: 40251, mean_wait: 2127.469, median_wait: 2017, p90_wait: 4174, p99_wait: 4216, max_wait: 4243, vip_mean_wait: 6.713, longest_line: 619, mean_line: 317.13, utilization: 99.92})
chk.eq("report with 4 servers", reports[4], {served: 6000, makespan: 36041, mean_wait: 5.987, median_wait: 0, p90_wait: 19, p99_wait: 44, max_wait: 91, vip_mean_wait: 2.393, longest_line: 16, mean_line: 0.997, utilization: 83.7})
chk.eq("report with 5 servers", reports[5], {served: 6000, makespan: 36041, mean_wait: 0.851, median_wait: 0, p90_wait: 3, p99_wait: 13, max_wait: 30, vip_mean_wait: 0.59, longest_line: 6, mean_line: 0.142, utilization: 66.96})
chk.eq("report with 6 servers", reports[6], {served: 6000, makespan: 36041, mean_wait: 0.15, median_wait: 0, p90_wait: 0, p99_wait: 5, max_wait: 19, vip_mean_wait: 0.123, longest_line: 3, mean_line: 0.025, utilization: 55.8})

busiest = scenarios[4]
chk.eq("wait histogram with 4 servers", stats.histogram(busiest.waits, 20).first(6), [[0, 5435], [20, 461], [40, 78], [60, 23], [80, 3]])
chk.eq("customers per server with 4 servers", busiest.servers.map(&:served), [1598, 1594, 1517, 1291])

# --- printed report -----------------------------------------------------------
lines = [format("%-8s %10s %8s %8s %8s %8s %12s", "servers", "mean wait", "median", "p90", "p99", "line", "utilization")]
reports.each do |server_count, report|
  lines << format("%-8d %10.3f %8d %8d %8d %8d %11.2f%%", server_count, report[:mean_wait], report[:median_wait],
                  report[:p90_wait], report[:p99_wait], report[:longest_line], report[:utilization])
end
bar_scale = busiest.waits.length / 40
stats.histogram(busiest.waits, 20).first(8).each do |bucket, count|
  lines << format("%4d-%-4d %s %d", bucket, bucket + 19, "#" * (count / bar_scale), count)
end
table = lines.join("\n")
chk.eq("report checksum", text_checksum(table), 894904467)

puts table
chk.finish

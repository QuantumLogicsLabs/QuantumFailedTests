# Sales data pipeline and report
#
# An end-to-end reporting job: generate orders, export them to CSV (with
# quoted fields, embedded commas and doubled quotes), parse the CSV back
# with a hand-written state machine, then aggregate -- revenue by region,
# best products and customers, a region x quarter pivot, month-over-month
# growth, a moving average and percentiles -- and print a formatted report.
# Dates use a small proleptic Gregorian calendar; money is integer cents.
#
# Self-checking: totals must agree across every aggregation, the rest is
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

  def pick(items)
    items[next_int(items.length)]
  end
end

module Csv
  # Splits CSV text into rows of fields. Quoted fields may contain commas,
  # line breaks and doubled quotes.
  def self.parse(text)
    rows = []
    row = []
    field = String.new
    in_quotes = false
    index = 0
    while index < text.length
      ch = text[index]
      if in_quotes
        if ch != '"'
          field << ch
        elsif text[index + 1] == '"'
          field << '"'
          index += 1
        else
          in_quotes = false
        end
      elsif ch == '"'
        in_quotes = true
      elsif ch == ","
        row << field
        field = String.new
      elsif ch == "\n"
        row << field
        rows << row
        row = []
        field = String.new
      elsif ch != "\r"
        field << ch
      end
      index += 1
    end
    raise ArgumentError, "unterminated quoted field" if in_quotes
    unless field.empty? && row.empty?
      row << field
      rows << row
    end
    rows
  end

  def self.escape(value)
    text = value.to_s
    text.match?(/[",\n]/) ? "\"#{text.gsub('"', '""')}\"" : text
  end

  def self.generate(rows)
    rows.map { |row| row.map { |value| escape(value) }.join(",") + "\n" }.join
  end
end

module Calendar
  DAYS_BEFORE_MONTH = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334].freeze
  MONTH_LENGTHS = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31].freeze
  WEEKDAYS = %w[Mon Tue Wed Thu Fri Sat Sun].freeze

  def self.leap?(year)
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
  end

  # Days since 1970-01-01.
  def self.day_number(year, month, day)
    prior = year - 1
    days = prior * 365 + prior / 4 - prior / 100 + prior / 400
    days += DAYS_BEFORE_MONTH[month - 1] + day
    days += 1 if month > 2 && leap?(year)
    days - 719_163
  end

  # [year, month, day] for a day number on or after 1970-01-01.
  def self.civil(day_number)
    year = 1970
    loop do
      length = leap?(year) ? 366 : 365
      break if day_number < length
      day_number -= length
      year += 1
    end
    month = 1
    loop do
      length = MONTH_LENGTHS[month - 1] + (month == 2 && leap?(year) ? 1 : 0)
      break if day_number < length
      day_number -= length
      month += 1
    end
    [year, month, day_number + 1]
  end

  def self.iso(day_number)
    format("%04d-%02d-%02d", *civil(day_number))
  end

  def self.parse(text)
    year, month, day = text.split("-").map(&:to_i)
    day_number(year, month, day)
  end

  def self.weekday(day_number)
    WEEKDAYS[(day_number + 3) % 7]
  end

  def self.month_key(day_number)
    year, month, = civil(day_number)
    format("%04d-%02d", year, month)
  end

  def self.quarter(day_number)
    year, month, = civil(day_number)
    "#{year}-Q#{(month - 1) / 3 + 1}"
  end
end

module Money
  def self.format_cents(cents)
    whole = (cents / 100).to_s.reverse.scan(/\d{1,3}/).join(",").reverse
    format("$%s.%02d", whole, cents % 100)
  end

  def self.to_decimal(cents)
    format("%d.%02d", cents / 100, cents % 100)
  end

  def self.parse_decimal(text)
    whole, fraction = text.split(".")
    whole.to_i * 100 + fraction.to_i
  end
end

Order = Struct.new(:id, :day, :region, :product, :quantity, :unit_cents, :customer) do
  def total
    quantity * unit_cents
  end

  def to_row
    [id, Calendar.iso(day), region, product, quantity, Money.to_decimal(unit_cents), customer]
  end

  def self.from_row(row)
    new(row[0].to_i, Calendar.parse(row[1]), row[2], row[3], row[4].to_i, Money.parse_decimal(row[5]), row[6])
  end
end

HEADER = %w[order_id date region product quantity unit_price customer].freeze
REGIONS = %w[North South East West].freeze
PRICES = {
  "Widget" => 1299, "Gadget" => 2450, "Gizmo" => 799,
  "Doohickey" => 4999, "Thingamajig" => 15_900, 'Sprocket 3"' => 350
}.freeze
FIRST_NAMES = %w[Ada Grace Alan Edsger Barbara Donald Linus Margaret].freeze
LAST_NAMES = ["Lovelace", "Hopper", "Turing", "Dijkstra", "Liskov", "Knuth", "Torvalds", "O'Neil", "van Rossum"].freeze

def build_orders(rng, count)
  first_day = Calendar.day_number(2023, 1, 1)
  products = PRICES.keys
  Array.new(count) do |index|
    product = rng.pick(products)
    discount = rng.next_int(4) * 5
    unit_cents = PRICES[product] * (100 - discount) / 100
    customer = "#{rng.pick(LAST_NAMES)}, #{rng.pick(FIRST_NAMES)}"
    Order.new(index + 1, first_day + rng.next_int(731), rng.pick(REGIONS), product, 1 + rng.next_int(12), unit_cents, customer)
  end
end

class SalesReport
  def initialize(orders)
    @orders = orders
  end

  def total_revenue
    @orders.sum(&:total)
  end

  def revenue_by(&key)
    totals = Hash.new(0)
    @orders.each { |order| totals[key.call(order)] += order.total }
    totals
  end

  def top_products(limit)
    rows = @orders.group_by(&:product).map do |product, orders|
      units = orders.sum(&:quantity)
      revenue = orders.sum(&:total)
      { product: product, orders: orders.length, units: units, revenue: revenue, average_cents: revenue / units }
    end
    rows.sort_by { |row| [-row[:revenue], row[:product]] }.first(limit)
  end

  def top_customers(limit)
    revenue_by(&:customer).sort_by { |customer, revenue| [-revenue, customer] }.first(limit)
  end

  # region -> quarter -> revenue
  def pivot
    table = Hash.new { |hash, region| hash[region] = Hash.new(0) }
    @orders.each { |order| table[order.region][Calendar.quarter(order.day)] += order.total }
    table
  end

  # [[month, revenue, growth_percent], ...]; the first month has no growth.
  def monthly_growth
    months = revenue_by { |order| Calendar.month_key(order.day) }.sort
    months.each_with_index.map do |(month, revenue), index|
      previous = index.zero? ? nil : months[index - 1][1]
      growth = previous ? ((revenue - previous) * 100.0 / previous).round(1) : nil
      [month, revenue, growth]
    end
  end

  # The best `window`-day stretch: [last_day_iso, average_daily_cents].
  def peak_moving_average(window)
    daily = revenue_by(&:day)
    first_day, last_day = daily.keys.minmax
    series = (first_day..last_day).map { |day| daily[day] }
    sums = series.each_cons(window).map(&:sum)
    best_sum, best_index = sums.each_with_index.max_by { |sum, index| [sum, -index] }
    [Calendar.iso(first_day + best_index + window - 1), best_sum / window]
  end

  def weekday_counts
    counts = @orders.map { |order| Calendar.weekday(order.day) }.tally
    Calendar::WEEKDAYS.to_h { |name| [name, counts.fetch(name, 0)] }
  end

  def order_value_percentile(percent)
    values = @orders.map(&:total).sort
    values[((percent * values.length / 100.0).ceil - 1).clamp(0, values.length - 1)]
  end

  def render
    lines = ["SALES REPORT  #{@orders.length} orders  #{Money.format_cents(total_revenue)}", ""]
    lines << "Revenue by region"
    revenue_by(&:region).sort_by { |region, revenue| [-revenue, region] }.each do |region, revenue|
      share = 100.0 * revenue / total_revenue
      lines << "  #{region.ljust(8)}#{Money.format_cents(revenue).rjust(16)}#{format('%7.2f%%', share)}"
    end
    lines << "" << "Top products"
    top_products(5).each_with_index do |row, rank|
      lines << format("  %d. %-14s %5d units %16s  avg %s", rank + 1, row[:product], row[:units],
                      Money.format_cents(row[:revenue]), Money.format_cents(row[:average_cents]))
    end
    quarters = pivot.values.flat_map(&:keys).uniq.sort
    lines << "" << "Region by quarter"
    lines << "  #{'region'.ljust(8)}#{quarters.map { |quarter| quarter.rjust(15) }.join}"
    pivot.sort.each do |region, by_quarter|
      lines << "  #{region.ljust(8)}#{quarters.map { |quarter| Money.format_cents(by_quarter[quarter]).rjust(15) }.join}"
    end
    lines << "" << "Monthly revenue"
    monthly_growth.each do |month, revenue, growth|
      change = growth.nil? ? "" : format("%+.1f%%", growth)
      lines << "  #{month}#{Money.format_cents(revenue).rjust(16)}#{change.rjust(9)}"
    end
    lines.join("\n")
  end
end

def text_checksum(text)
  hash = 7
  text.each_byte { |byte| hash = (hash * 131 + byte) % 1_000_000_007 }
  hash
end

chk = Checker.new("data_pipeline_report")

# --- csv ----------------------------------------------------------------------
chk.eq("csv quoted fields", Csv.parse(%(a,"b,c","say ""hi""",,d\n)), [["a", "b,c", 'say "hi"', "", "d"]])
chk.eq("csv embedded newline", Csv.parse(%("line one\nline two",x\r\nlast,row)), [["line one\nline two", "x"], ["last", "row"]])
chk.eq("csv escape", ["plain", "a,b", 'q"q', "two\nlines", 42].map { |value| Csv.escape(value) },
       ["plain", '"a,b"', '"q""q"', "\"two\nlines\"", "42"])
tricky = [["id", "note"], ["1", 'He said "no, thanks"'], ["2", ""], ["3", "multi\nline, with comma"]]
chk.eq("csv round trip", Csv.parse(Csv.generate(tricky)), tricky)
begin
  Csv.parse(%(a,"never closed\n))
  outcome = "no error"
rescue ArgumentError => e
  outcome = e.message
end
chk.eq("csv unterminated quote", outcome, "unterminated quoted field")

# --- calendar -----------------------------------------------------------------
chk.eq("leap years", [1900, 2000, 2023, 2024, 2100].map { |year| Calendar.leap?(year) }, [false, true, false, true, false])
chk.eq("day numbers", [[1970, 1, 1], [2000, 3, 1], [2024, 1, 1], [2024, 2, 29]].map { |date| Calendar.day_number(*date) },
       [0, 11_017, 19_723, 19_782])
chk.eq("civil dates", [0, 59, 11_016, 19_782, 19_783].map { |day| Calendar.iso(day) },
       ["1970-01-01", "1970-03-01", "2000-02-29", "2024-02-29", "2024-03-01"])
chk.eq("weekdays", [0, 19_723, 19_782].map { |day| Calendar.weekday(day) }, ["Thu", "Mon", "Thu"])
chk.eq("quarters", ["2023-01-15", "2023-06-30", "2024-10-01"].map { |date| Calendar.quarter(Calendar.parse(date)) },
       ["2023-Q1", "2023-Q2", "2024-Q4"])
span = (Calendar.day_number(2023, 1, 1)..Calendar.day_number(2024, 12, 31)).to_a
chk.eq("two years of days", span.length, 731)
chk.eq("calendar round trip", span.all? { |day| Calendar.parse(Calendar.iso(day)) == day }, true)

# --- money --------------------------------------------------------------------
chk.eq("money formatting", [0, 5, 99_999, 100_000, 123_456_789].map { |cents| Money.format_cents(cents) },
       ["$0.00", "$0.05", "$999.99", "$1,000.00", "$1,234,567.89"])
chk.eq("money decimal round trip", [0, 7, 1299, 15_900].map { |cents| Money.parse_decimal(Money.to_decimal(cents)) }, [0, 7, 1299, 15_900])

# --- export and import --------------------------------------------------------
rng = Lcg.new(19_990_101)
orders = build_orders(rng, 5000)
csv_text = Csv.generate([HEADER] + orders.map(&:to_row))
parsed = Csv.parse(csv_text)
imported = parsed.drop(1).map { |row| Order.from_row(row) }
chk.eq("csv header", parsed.first, HEADER)
chk.eq("csv row count", parsed.length, 5001)
chk.eq("import equals export", imported == orders, true)
chk.eq("csv size", csv_text.length, 282011)
chk.eq("csv checksum", text_checksum(csv_text), 380500246)
chk.eq("first csv line", csv_text.lines[1].chomp, "1,2023-06-07,North,Thingamajig,8,151.05,\"Dijkstra, Ada\"")
chk.eq("quoted product survives", imported.count { |order| order.product == 'Sprocket 3"' }, 839)

# --- aggregation --------------------------------------------------------------
report = SalesReport.new(imported)
total = report.total_revenue
chk.eq("total revenue", total, 126379757)
chk.eq("regions add up", report.revenue_by(&:region).values.sum, total)
chk.eq("months add up", report.monthly_growth.sum { |_, revenue, _| revenue }, total)
chk.eq("pivot adds up", report.pivot.values.sum { |by_quarter| by_quarter.values.sum }, total)
chk.eq("weekdays add up", report.weekday_counts.values.sum, 5000)
chk.eq("products add up", report.top_products(99).sum { |row| row[:revenue] }, total)
chk.eq("revenue by region", report.revenue_by(&:region).sort.to_h, {"East" => 32575644, "North" => 31184788, "South" => 30586227, "West" => 32033098})
chk.eq("top product", report.top_products(1).first, {product: "Thingamajig", orders: 825, units: 5188, revenue: 76486950, average_cents: 14743})
chk.eq("top customers", report.top_customers(3), [["O'Neil, Alan", 2960274], ["Liskov, Margaret", 2586559], ["O'Neil, Margaret", 2566731]])
chk.eq("pivot quarters", report.pivot["North"].keys.sort, %w[2023-Q1 2023-Q2 2023-Q3 2023-Q4 2024-Q1 2024-Q2 2024-Q3 2024-Q4])
chk.eq("month count", report.monthly_growth.length, 24)
chk.eq("first month has no growth", report.monthly_growth.first[2], nil)
chk.eq("growth figures", report.monthly_growth.drop(1).first(4).map(&:last), [28.9, -7.2, -13.5, 1.3])
chk.eq("peak week", report.peak_moving_average(7), ["2023-02-04", 329098])
chk.eq("weekday counts", report.weekday_counts, {"Mon" => 718, "Tue" => 754, "Wed" => 743, "Thu" => 698, "Fri" => 687, "Sat" => 708, "Sun" => 692})
chk.eq("order value percentiles", [50, 90, 99].map { |percent| report.order_value_percentile(percent) }, [9352, 75525, 171720])

rendered = report.render
chk.eq("report line count", rendered.lines.length, 47)
chk.eq("report checksum", text_checksum(rendered), 866806949)

puts rendered
chk.finish

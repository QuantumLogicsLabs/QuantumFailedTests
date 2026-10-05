# Arbitrary-precision integer calculator
#
# BigNum stores a signed integer as base-10000 limbs and implements
# addition, subtraction, schoolbook and Karatsuba multiplication, short
# division, exponentiation and ordering. Limbs are kept small on purpose so
# no intermediate value exceeds 2**53. BigMath builds factorials, Fibonacci
# numbers and the digits of pi (Machin's formula) on top of it.
#
# Self-checking: well-known constants are embedded, the rest is compared
# against values verified with the reference Ruby implementation, and the
# first mismatch raises.

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

class BigNum
  include Comparable

  BASE = 10_000
  BASE_DIGITS = 4
  KARATSUBA_THRESHOLD = 24

  attr_reader :limbs

  # limbs are little-endian; zero is the empty list.
  def initialize(limbs, negative = false)
    trimmed = BigNum.trim(limbs.dup)
    @limbs = trimmed.freeze
    @negative = negative && !trimmed.empty?
  end

  def self.from_i(value)
    negative = value < 0
    value = value.abs
    limbs = []
    while value > 0
      limbs << value % BASE
      value /= BASE
    end
    new(limbs, negative)
  end

  def self.parse(text)
    digits = text.strip
    negative = digits.start_with?("-")
    digits = digits[1..] if negative || digits.start_with?("+")
    raise ArgumentError, "invalid number: #{text}" unless digits.match?(/\A\d+\z/)
    limbs = []
    finish = digits.length
    while finish > 0
      start = [finish - BASE_DIGITS, 0].max
      limbs << digits[start...finish].to_i
      finish = start
    end
    new(limbs, negative)
  end

  def self.coerce_operand(value)
    value.is_a?(BigNum) ? value : from_i(value)
  end

  def zero?
    @limbs.empty?
  end

  def negative?
    @negative
  end

  def digit_count
    return 1 if zero?
    (@limbs.length - 1) * BASE_DIGITS + @limbs.last.to_s.length
  end

  def to_s
    return "0" if zero?
    groups = @limbs.reverse.each_with_index.map do |limb, index|
      index.zero? ? limb.to_s : limb.to_s.rjust(BASE_DIGITS, "0")
    end
    @negative ? "-#{groups.join}" : groups.join
  end

  def -@
    BigNum.new(@limbs, !@negative)
  end

  def abs
    BigNum.new(@limbs, false)
  end

  def <=>(other)
    other = BigNum.coerce_operand(other)
    return (@negative ? -1 : 1) if @negative != other.negative?
    order = BigNum.compare_magnitude(@limbs, other.limbs)
    @negative ? -order : order
  end

  def +(other)
    other = BigNum.coerce_operand(other)
    if @negative == other.negative?
      BigNum.new(BigNum.add_magnitude(@limbs, other.limbs), @negative)
    else
      case BigNum.compare_magnitude(@limbs, other.limbs)
      when 0 then BigNum.new([])
      when 1 then BigNum.new(BigNum.sub_magnitude(@limbs, other.limbs), @negative)
      else BigNum.new(BigNum.sub_magnitude(other.limbs, @limbs), other.negative?)
      end
    end
  end

  def -(other)
    self + -BigNum.coerce_operand(other)
  end

  def *(other)
    other = BigNum.coerce_operand(other)
    BigNum.new(BigNum.mul_magnitude(@limbs, other.limbs), @negative != other.negative?)
  end

  # Short division of the magnitude by a small positive Integer.
  # Returns [quotient, remainder].
  def divmod_small(divisor)
    raise ZeroDivisionError, "divided by 0" if divisor.zero?
    raise ArgumentError, "divisor out of range" unless divisor.between?(1, 100_000_000)
    quotient = Array.new(@limbs.length, 0)
    remainder = 0
    (@limbs.length - 1).downto(0) do |index|
      current = remainder * BASE + @limbs[index]
      quotient[index] = current / divisor
      remainder = current % divisor
    end
    [BigNum.new(quotient, @negative), remainder]
  end

  def **(exponent)
    raise ArgumentError, "negative exponent" if exponent < 0
    result = BigNum.from_i(1)
    base = self
    while exponent > 0
      result *= base if exponent.odd?
      exponent /= 2
      base *= base if exponent > 0
    end
    result
  end

  def self.trim(limbs)
    limbs.pop while !limbs.empty? && limbs.last.zero?
    limbs
  end

  def self.compare_magnitude(a, b)
    return a.length <=> b.length if a.length != b.length
    (a.length - 1).downto(0) do |index|
      return a[index] <=> b[index] if a[index] != b[index]
    end
    0
  end

  def self.add_magnitude(a, b)
    a, b = b, a if a.length < b.length
    result = []
    carry = 0
    a.each_with_index do |limb, index|
      total = limb + (b[index] || 0) + carry
      if total >= BASE
        result << total - BASE
        carry = 1
      else
        result << total
        carry = 0
      end
    end
    result << carry if carry > 0
    result
  end

  # Requires |a| >= |b|.
  def self.sub_magnitude(a, b)
    result = []
    borrow = 0
    a.each_with_index do |limb, index|
      difference = limb - (b[index] || 0) - borrow
      if difference < 0
        difference += BASE
        borrow = 1
      else
        borrow = 0
      end
      result << difference
    end
    trim(result)
  end

  def self.mul_schoolbook(a, b)
    return [] if a.empty? || b.empty?
    result = Array.new(a.length + b.length, 0)
    a.each_with_index do |x, i|
      next if x.zero?
      carry = 0
      b.each_with_index do |y, j|
        current = result[i + j] + x * y + carry
        result[i + j] = current % BASE
        carry = current / BASE
      end
      k = i + b.length
      while carry > 0
        current = result[k] + carry
        result[k] = current % BASE
        carry = current / BASE
        k += 1
      end
    end
    trim(result)
  end

  def self.mul_magnitude(a, b)
    return mul_schoolbook(a, b) if a.length < KARATSUBA_THRESHOLD || b.length < KARATSUBA_THRESHOLD
    half = [a.length, b.length].max / 2
    a_low = trim(a[0, half])
    a_high = a[half..] || []
    b_low = trim(b[0, half])
    b_high = b[half..] || []
    low = mul_magnitude(a_low, b_low)
    high = mul_magnitude(a_high, b_high)
    cross = mul_magnitude(add_magnitude(a_low, a_high), add_magnitude(b_low, b_high))
    middle = sub_magnitude(sub_magnitude(cross, low), high)
    result = Array.new(a.length + b.length + 1, 0)
    accumulate(result, low, 0)
    accumulate(result, middle, half)
    accumulate(result, high, half * 2)
    trim(result)
  end

  def self.accumulate(target, part, offset)
    carry = 0
    index = 0
    while index < part.length || carry > 0
      total = target[offset + index] + (part[index] || 0) + carry
      if total >= BASE
        target[offset + index] = total - BASE
        carry = 1
      else
        target[offset + index] = total
        carry = 0
      end
      index += 1
    end
  end
end

module BigMath
  def self.factorial(n)
    (2..n).reduce(BigNum.from_i(1)) { |product, factor| product * factor }
  end

  def self.fibonacci(n)
    a = BigNum.from_i(0)
    b = BigNum.from_i(1)
    n.times { a, b = b, a + b }
    a
  end

  # Index of the first Fibonacci number with at least `digits` digits.
  def self.first_fibonacci_with_digits(digits)
    a = BigNum.from_i(1)
    b = BigNum.from_i(1)
    index = 1
    while a.digit_count < digits
      a, b = b, a + b
      index += 1
    end
    index
  end

  # arctan(1/x) scaled by `scale`, from the alternating Taylor series.
  def self.arctan_inverse(x, scale)
    term = scale.divmod_small(x).first
    total = term
    x_squared = x * x
    k = 1
    until term.zero?
      term = term.divmod_small(x_squared).first
      k += 2
      piece = term.divmod_small(k).first
      total = (k / 2).odd? ? total - piece : total + piece
    end
    total
  end

  # "3" followed by `digits` decimals: pi = 16 atan(1/5) - 4 atan(1/239).
  def self.pi_digits(digits)
    guard = 10
    scale = BigNum.from_i(10)**(digits + guard)
    pi = arctan_inverse(5, scale) * 16 - arctan_inverse(239, scale) * 4
    pi.to_s[0, digits + 1]
  end
end

def digit_sum(text)
  text.each_char.sum { |ch| ch.ord - 48 }
end

def text_checksum(text)
  hash = 7
  text.each_byte { |byte| hash = (hash * 131 + byte) % 1_000_000_007 }
  hash
end

def random_bignum(rng, digits)
  text = (1 + rng.next_int(9)).to_s
  (digits - 1).times { text << rng.next_int(10).to_s }
  BigNum.parse(text)
end

chk = Checker.new("bigint_calculator")

# --- primitives ---------------------------------------------------------------
chk.eq("from_i / to_s", BigNum.from_i(1_234_567_890_123).to_s, "1234567890123")
chk.eq("limbs are little-endian", BigNum.from_i(1_234_567_890_123).limbs, [123, 6789, 2345, 1])
chk.eq("parse / to_s", BigNum.parse("-000120000000000000000000000045").to_s, "-120000000000000000000000045")
chk.eq("zero normalizes", BigNum.parse("-0000").to_s, "0")
chk.eq("carry chain", (BigNum.parse("99999999999999999999") + 1).to_s, "100000000000000000000")
chk.eq("borrow chain", (BigNum.parse("100000000000000000000") - 1).to_s, "99999999999999999999")
chk.eq("mixed signs", (BigNum.from_i(5) - BigNum.from_i(12)).to_s, "-7")
chk.eq("cancellation", (BigNum.parse("-777777777777") + BigNum.parse("777777777777")).zero?, true)
chk.eq("signed product", (BigNum.from_i(-12_345_678) * BigNum.from_i(87_654_321)).to_s, "-1082152022374638")
quotient, remainder = BigNum.parse("1000000000000000000000").divmod_small(7)
chk.eq("short division", [quotient.to_s, remainder], ["142857142857142857142", 6])
ordered = [BigNum.from_i(3), BigNum.parse("-40"), BigNum.parse("123456789012345678901234567890"), BigNum.from_i(0)].sort
chk.eq("ordering", ordered.map(&:to_s), ["-40", "0", "3", "123456789012345678901234567890"])
chk.eq("comparable helpers", BigNum.from_i(50).between?(BigNum.from_i(-1), BigNum.parse("1000000000000")), true)
chk.eq("digit count", BigNum.parse("10000000000000000").digit_count, 17)

# --- well-known constants -----------------------------------------------------
chk.eq("2**64", (BigNum.from_i(2)**64).to_s, "18446744073709551616")
chk.eq("30!", BigMath.factorial(30).to_s, "265252859812191058636308480000000")
chk.eq("fibonacci(100)", BigMath.fibonacci(100).to_s, "354224848179261915075")
chk.eq("digit sum of 2**1000", digit_sum((BigNum.from_i(2)**1000).to_s), 1366)
chk.eq("digit sum of 100!", digit_sum(BigMath.factorial(100).to_s), 648)

# --- large factorial ----------------------------------------------------------
factorial = BigMath.factorial(450).to_s
chk.eq("450! digit count", factorial.length, 1001)
chk.eq("450! trailing zeros", factorial.length - factorial.sub(/0+\z/, "").length, 450 / 5 + 450 / 25 + 450 / 125)
chk.eq("450! leading digits", factorial[0, 12], "173336873311")
chk.eq("450! checksum", text_checksum(factorial), 863831495)

# --- Fibonacci ----------------------------------------------------------------
chk.eq("first 1000-digit fibonacci", BigMath.first_fibonacci_with_digits(1000), 4782)
fib = BigMath.fibonacci(1500).to_s
chk.eq("fibonacci(1500) digit count", fib.length, 314)
chk.eq("fibonacci(1500) checksum", text_checksum(fib), 902685314)

# --- Karatsuba against schoolbook --------------------------------------------
rng = Lcg.new(987_654_321)
x = random_bignum(rng, 620)
y = random_bignum(rng, 584)
fast = BigNum.mul_magnitude(x.limbs, y.limbs)
slow = BigNum.mul_schoolbook(x.limbs, y.limbs)
chk.eq("karatsuba matches schoolbook", fast == slow, true)
product = (x * y).to_s
chk.eq("product digit count", product.length, 1203)
chk.eq("product checksum", text_checksum(product), 499705159)
chk.eq("difference of squares", ((x + y) * (x - y)) == (x * x - y * y), true)
chk.eq("distributive law", (x * (y + 12_345)) == (x * y + x * 12_345), true)
chk.eq("square is positive", ((-x) * (-x)) == x * x, true)

# --- pi -----------------------------------------------------------------------
pi = BigMath.pi_digits(800)
chk.eq("pi length", pi.length, 801)
chk.eq("pi first 50 decimals", pi[0, 51], "314159265358979323846264338327950288419716939937510")
chk.eq("pi Feynman point", pi[762, 6], "999999")
chk.eq("pi digit sum", digit_sum(pi), 3597)
chk.eq("pi checksum", text_checksum(pi), 806960178)

puts "450! has #{factorial.length} digits"
puts "fibonacci(1500) has #{fib.length} digits"
puts "pi = #{pi[0]}.#{pi[1, 60]}..."
chk.finish

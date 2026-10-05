# Linear algebra: exact fractions and dense matrices
#
# Fraction is an exact rational number with operator overloading and
# ordering. Matrix runs Gauss-Jordan elimination with partial pivoting over
# either Fractions or Floats, giving determinants, inverses and linear
# solves. The workload inverts a Hilbert matrix exactly, recovers polynomial
# coefficients, solves a 60x60 system and estimates an eigenvalue.
#
# Self-checking: closed-form results are embedded, the rest is compared
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

class Fraction
  include Comparable

  attr_reader :num, :den

  def initialize(num, den = 1)
    raise ZeroDivisionError, "fraction with a zero denominator" if den.zero?
    if den < 0
      num = -num
      den = -den
    end
    divisor = num.gcd(den)
    @num = num / divisor
    @den = den / divisor
  end

  def self.lift(value)
    value.is_a?(Fraction) ? value : Fraction.new(value)
  end

  def +(other)
    other = Fraction.lift(other)
    common = @den.lcm(other.den)
    Fraction.new(@num * (common / @den) + other.num * (common / other.den), common)
  end

  def -(other)
    self + -Fraction.lift(other)
  end

  def -@
    Fraction.new(-@num, @den)
  end

  # Cross-reduces before multiplying to keep the intermediates small.
  def *(other)
    other = Fraction.lift(other)
    g1 = @num.gcd(other.den)
    g2 = other.num.gcd(@den)
    Fraction.new((@num / g1) * (other.num / g2), (@den / g2) * (other.den / g1))
  end

  def /(other)
    other = Fraction.lift(other)
    raise ZeroDivisionError, "division by a zero fraction" if other.zero?
    self * Fraction.new(other.den, other.num)
  end

  def <=>(other)
    other = Fraction.lift(other)
    (@num * other.den) <=> (other.num * @den)
  end

  def zero?
    @num.zero?
  end

  def integer?
    @den == 1
  end

  def abs
    Fraction.new(@num.abs, @den)
  end

  def to_f
    @num.to_f / @den
  end

  def to_s
    @den == 1 ? @num.to_s : "#{@num}/#{@den}"
  end
end

class SingularMatrixError < StandardError
end

class Matrix
  attr_reader :rows, :size

  def initialize(rows)
    @rows = rows
    @size = rows.length
  end

  def self.build(size)
    new(Array.new(size) { |i| Array.new(size) { |j| yield(i, j) } })
  end

  def self.identity(size, zero, one)
    build(size) { |i, j| i == j ? one : zero }
  end

  def [](row, col)
    @rows[row][col]
  end

  def *(other)
    Matrix.build(@size) do |i, j|
      sum = @rows[i][0] * other[0, j]
      (1...@size).each { |k| sum += @rows[i][k] * other[k, j] }
      sum
    end
  end

  def apply(vector)
    @rows.map { |row| row.zip(vector).map { |a, b| a * b }.reduce(:+) }
  end

  def transpose
    Matrix.new(@rows.transpose)
  end

  # Gauss-Jordan elimination with partial pivoting on the augmented system
  # [self | right]. Returns [reduced_right, determinant].
  def eliminate(right)
    left = @rows.map(&:dup)
    right = right.map(&:dup)
    determinant = nil
    swaps = 0
    @size.times do |col|
      pivot = (col...@size).max_by { |row| left[row][col].abs }
      raise SingularMatrixError, "matrix is singular (column #{col})" if left[pivot][col].zero?
      if pivot != col
        left[col], left[pivot] = left[pivot], left[col]
        right[col], right[pivot] = right[pivot], right[col]
        swaps += 1
      end
      pivot_value = left[col][col]
      determinant = determinant.nil? ? pivot_value : determinant * pivot_value
      left[col] = left[col].map { |value| value / pivot_value }
      right[col] = right[col].map { |value| value / pivot_value }
      @size.times do |row|
        next if row == col
        factor = left[row][col]
        next if factor.zero?
        left[row] = left[row].each_with_index.map { |value, c| value - factor * left[col][c] }
        right[row] = right[row].each_with_index.map { |value, c| value - factor * right[col][c] }
      end
    end
    [right, swaps.even? ? determinant : -determinant]
  end

  def determinant
    eliminate(Array.new(@size) { [] }).last
  rescue SingularMatrixError
    @rows[0][0] * 0
  end

  def inverse(zero, one)
    Matrix.new(eliminate(Matrix.identity(@size, zero, one).rows).first)
  end

  def solve(vector)
    eliminate(vector.map { |value| [value] }).first.map(&:first)
  end

  def max_deviation_from_identity
    deviation = 0.0
    @rows.each_with_index do |row, i|
      row.each_with_index do |value, j|
        error = (value - (i == j ? 1.0 : 0.0)).abs
        deviation = error if error > deviation
      end
    end
    deviation
  end
end

def hilbert(size)
  Matrix.build(size) { |i, j| Fraction.new(1, i + j + 1) }
end

def tridiagonal(size)
  Matrix.build(size) do |i, j|
    if i == j
      2.0
    elsif (i - j).abs == 1
      -1.0
    else
      0.0
    end
  end
end

# Largest eigenvalue by power iteration, using the Rayleigh quotient.
def dominant_eigenvalue(matrix, iterations)
  vector = Array.new(matrix.size) { |i| 1.0 + i * 0.01 }
  eigenvalue = 0.0
  iterations.times do
    image = matrix.apply(vector)
    eigenvalue = image.zip(vector).sum { |a, b| a * b } / vector.sum { |v| v * v }
    norm = Math.sqrt(image.sum { |v| v * v })
    vector = image.map { |v| v / norm }
  end
  eigenvalue
end

chk = Checker.new("matrix_solver")

# --- fractions ----------------------------------------------------------------
half = Fraction.new(1, 2)
third = Fraction.new(1, 3)
chk.eq("fraction reduces", Fraction.new(84, -36).to_s, "-7/3")
chk.eq("fraction add", (half + third).to_s, "5/6")
chk.eq("fraction subtract", (third - half).to_s, "-1/6")
chk.eq("fraction multiply", (Fraction.new(3, 4) * Fraction.new(8, 9)).to_s, "2/3")
chk.eq("fraction divide", (Fraction.new(3, 4) / Fraction.new(9, 8)).to_s, "2/3")
chk.eq("fraction with integer", (half * 6 + 1).to_s, "4")
chk.eq("fraction ordering", [half, third, Fraction.new(-1, 7), Fraction.new(2, 5)].sort.map(&:to_s), ["-1/7", "1/3", "2/5", "1/2"])
chk.eq("fraction equality", Fraction.new(2, 4) == half, true)
chk.eq("fraction clamp", Fraction.new(9, 4).clamp(third, half).to_s, "1/2")
telescoping = (1..60).reduce(Fraction.new(0)) { |sum, k| sum + Fraction.new(1, k * (k + 1)) }
chk.eq("telescoping series", telescoping.to_s, "60/61")
harmonic = (1..18).reduce(Fraction.new(0)) { |sum, k| sum + Fraction.new(1, k) }
chk.eq("harmonic number H18", harmonic.to_s, "14274301/4084080")

begin
  outcome = (half / Fraction.new(0)).to_s
rescue ZeroDivisionError => e
  outcome = e.message
end
chk.eq("fraction division by zero", outcome, "division by a zero fraction")

# --- exact Hilbert matrix -----------------------------------------------------
zero = Fraction.new(0)
one = Fraction.new(1)
h5 = hilbert(5)
h5_inverse = h5.inverse(zero, one)
chk.eq("hilbert determinant", h5.determinant.to_s, "1/266716800000")
chk.eq("hilbert inverse is integral", h5_inverse.rows.flatten.all?(&:integer?), true)
chk.eq("hilbert inverse first row", h5_inverse.rows[0].map(&:to_s), ["25", "-300", "1050", "-1400", "630"])
chk.eq("hilbert inverse entry sum", h5_inverse.rows.flatten.reduce(:+).to_s, "25")
chk.eq("hilbert times inverse", (h5 * h5_inverse).rows == Matrix.identity(5, zero, one).rows, true)
chk.eq("hilbert inverse is symmetric", h5_inverse.transpose.rows == h5_inverse.rows, true)

# --- exact polynomial interpolation -------------------------------------------
# p(x) = 3x^4 - 2x^3 + 7x - 5 sampled at x = 0..4, recovered from a Vandermonde system.
polynomial = ->(x) { 3 * x**4 - 2 * x**3 + 7 * x - 5 }
vandermonde = Matrix.build(5) { |i, j| Fraction.new(i**j) }
samples = (0...5).map { |x| Fraction.new(polynomial.call(x)) }
chk.eq("interpolated coefficients", vandermonde.solve(samples).map(&:to_s), ["-5", "7", "0", "-2", "3"])

singular = Matrix.new([[1, 2, 3], [2, 4, 6], [1, 0, 1]].map { |row| row.map { |v| Fraction.new(v) } })
chk.eq("singular determinant", singular.determinant.to_s, "0")
begin
  singular.inverse(zero, one)
  outcome = "no error"
rescue SingularMatrixError => e
  outcome = e.message
end
chk.eq("singular inverse raises", outcome, "matrix is singular (column 2)")

# --- floating point -----------------------------------------------------------
chk.near("tridiagonal determinant", tridiagonal(50).determinant, 51.0, 1e-7)
chk.near("dominant eigenvalue", dominant_eigenvalue(tridiagonal(12), 400), 2 + 2 * Math.cos(Math::PI / 13), 1e-9)

rng = Lcg.new(31_337)
size = 60
dense = Matrix.build(size) do |i, j|
  noise = (rng.next_int(2001) - 1000) / 250.0
  i == j ? noise + 40.0 : noise
end
unknowns = Array.new(size) { |i| (i % 7) - 3 + i / 10.0 }
right_hand_side = dense.apply(unknowns)
solution = dense.solve(right_hand_side)
worst_error = solution.zip(unknowns).map { |got, want| (got - want).abs }.max
chk.eq("dense solve recovers the unknowns", worst_error < 1e-9, true)

dense_inverse = dense.inverse(0.0, 1.0)
chk.eq("dense inverse", (dense * dense_inverse).max_deviation_from_identity < 1e-9, true)
chk.near("dense determinant of a 6x6 block", Matrix.build(6) { |i, j| dense[i, j] }.determinant, 4292128732.6497965, 1e-3)
chk.near("dense solution sum", solution.sum, unknowns.sum, 1e-8)
chk.near("dense inverse trace", (0...size).sum { |i| dense_inverse[i, i] }, 1.495998874831627, 1e-9)

# --- least squares line through noisy samples ---------------------------------
points = (0...40).map { |x| [x.to_f, 3.0 * x + 2.0 + (rng.next_int(201) - 100) / 100.0] }
normal = Matrix.new([
  [points.sum { |x, _| x * x }, points.sum { |x, _| x }],
  [points.sum { |x, _| x }, points.length.to_f]
])
slope, intercept = normal.solve([points.sum { |x, y| x * y }, points.sum { |_, y| y }])
chk.near("least squares slope", slope, 2.9970506566604125, 1e-9)
chk.near("least squares intercept", intercept, 1.9690121951219588, 1e-9)
chk.eq("least squares is close to the true line", (slope - 3.0).abs < 0.05 && (intercept - 2.0).abs < 0.5, true)

puts "det(H5) = #{h5.determinant}"
puts "H5 inverse row 0 = #{h5_inverse.rows[0].map(&:to_s).join(', ')}"
puts "fit: y = #{slope.round(4)}x + #{intercept.round(4)}"
chk.finish

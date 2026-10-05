# Puzzle and constraint solvers
#
# Four backtracking searches: a Sudoku solver that tracks candidates in
# bitmasks and always branches on the most constrained cell, an N-Queens
# counter driven by bit tricks, a knight's tour ordered by Warnsdorff's
# rule, and a column-by-column cryptarithm solver.
#
# Self-checking: every solution is validated against the puzzle rules, the
# well-known answers are embedded, and the first mismatch raises.

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

class Sudoku
  ALL_DIGITS = 0x1FF
  POPCOUNT = Array.new(512) { |mask| mask.to_s(2).count("1") }.freeze

  attr_reader :nodes

  def initialize(text)
    raise ArgumentError, "a puzzle needs 81 cells, got #{text.length}" unless text.length == 81
    @cells = Array.new(81, 0)
    @rows = Array.new(9, 0)
    @cols = Array.new(9, 0)
    @boxes = Array.new(9, 0)
    @nodes = 0
    text.each_char.with_index do |ch, index|
      next if ch == "." || ch == "0"
      digit = ch.to_i
      raise ArgumentError, "conflicting given #{digit} at cell #{index}" if (candidates(index) & (1 << (digit - 1))).zero?
      place(index, digit)
    end
  end

  def solve
    index, mask = most_constrained
    return true if index.nil?
    return false if mask.zero?
    @nodes += 1
    (1..9).each do |digit|
      next if (mask & (1 << (digit - 1))).zero?
      place(index, digit)
      return true if solve
      remove(index, digit)
    end
    false
  end

  def to_s
    @cells.join
  end

  def valid_solution?
    units = []
    9.times do |i|
      units << (0...9).map { |j| @cells[i * 9 + j] }
      units << (0...9).map { |j| @cells[j * 9 + i] }
      units << (0...9).map { |j| @cells[(i / 3) * 27 + (i % 3) * 3 + (j / 3) * 9 + j % 3] }
    end
    units.all? { |unit| unit.sort == [1, 2, 3, 4, 5, 6, 7, 8, 9] }
  end

  private

  def box_of(index)
    (index / 27) * 3 + (index % 9) / 3
  end

  def candidates(index)
    ALL_DIGITS & ~(@rows[index / 9] | @cols[index % 9] | @boxes[box_of(index)])
  end

  def place(index, digit)
    bit = 1 << (digit - 1)
    @cells[index] = digit
    @rows[index / 9] |= bit
    @cols[index % 9] |= bit
    @boxes[box_of(index)] |= bit
  end

  def remove(index, digit)
    bit = 1 << (digit - 1)
    @cells[index] = 0
    @rows[index / 9] &= ~bit
    @cols[index % 9] &= ~bit
    @boxes[box_of(index)] &= ~bit
  end

  # The empty cell with the fewest candidates, as [index, candidate_mask].
  def most_constrained
    best_index = nil
    best_mask = 0
    best_count = 10
    @cells.each_with_index do |digit, index|
      next unless digit.zero?
      mask = candidates(index)
      count = POPCOUNT[mask]
      next unless count < best_count
      best_index = index
      best_mask = mask
      best_count = count
      break if count <= 1
    end
    [best_index, best_mask]
  end
end

module Queens
  # Counts every placement, one row at a time, with three occupancy masks.
  def self.count(size, columns = 0, left_diagonals = 0, right_diagonals = 0, row = 0)
    return 1 if row == size
    total = 0
    available = ((1 << size) - 1) & ~(columns | left_diagonals | right_diagonals)
    while available != 0
      bit = available & -available
      available ^= bit
      total += count(size, columns | bit, (left_diagonals | bit) << 1, (right_diagonals | bit) >> 1, row + 1)
    end
    total
  end

  # The lexicographically first placement, as the column used in each row.
  def self.first_solution(size, placed = [])
    return placed if placed.length == size
    row = placed.length
    size.times do |column|
      safe = placed.each_with_index.none? do |other, other_row|
        other == column || (other - column).abs == row - other_row
      end
      next unless safe
      solution = first_solution(size, placed + [column])
      return solution if solution
    end
    nil
  end
end

class KnightTour
  MOVES = [[1, 2], [2, 1], [2, -1], [1, -2], [-1, -2], [-2, -1], [-2, 1], [-1, 2]].freeze

  def initialize(size)
    @size = size
    @board = Array.new(size) { Array.new(size, -1) }
  end

  # Returns the board of visit numbers, or nil when no tour exists.
  def solve(row, col)
    @board[row][col] = 0
    extend_tour(row, col, 1) ? @board : nil
  end

  def self.valid?(board)
    size = board.length
    squares = {}
    board.each_with_index do |cells, row|
      cells.each_with_index { |step, col| squares[step] = [row, col] }
    end
    return false unless squares.keys.sort == (0...size * size).to_a
    (1...size * size).all? do |step|
      row_gap = (squares[step][0] - squares[step - 1][0]).abs
      col_gap = (squares[step][1] - squares[step - 1][1]).abs
      [row_gap, col_gap].sort == [1, 2]
    end
  end

  private

  def onward(row, col)
    MOVES.map { |row_step, col_step| [row + row_step, col + col_step] }
         .select { |r, c| r.between?(0, @size - 1) && c.between?(0, @size - 1) && @board[r][c] == -1 }
  end

  # Warnsdorff's rule: try the squares with the fewest onward moves first.
  def extend_tour(row, col, step)
    return true if step == @size * @size
    ordered = onward(row, col).sort_by.with_index { |(r, c), index| [onward(r, c).length, index] }
    ordered.each do |r, c|
      @board[r][c] = step
      return true if extend_tour(r, c, step + 1)
      @board[r][c] = -1
    end
    false
  end
end

class Cryptarithm
  attr_reader :nodes

  def initialize(addends, total)
    @words = addends + [total]
    @addends = addends.map(&:reverse)
    @total = total.reverse
    @leading = @words.map { |word| word[0] }.uniq
    @letters = []
    @total.length.times do |column|
      (@addends + [@total]).each do |word|
        letter = word[column]
        @letters << letter if letter && !@letters.include?(letter)
      end
    end
    @assignment = {}
    @used = Array.new(10, false)
    @nodes = 0
  end

  def solve
    search(0) ? @assignment.dup : nil
  end

  def value_of(word)
    word.each_char.reduce(0) { |number, letter| number * 10 + @assignment[letter] }
  end

  private

  def search(position)
    return consistent? if position == @letters.length
    letter = @letters[position]
    10.times do |digit|
      next if @used[digit]
      next if digit.zero? && @leading.include?(letter)
      @nodes += 1
      @assignment[letter] = digit
      @used[digit] = true
      return true if consistent? && search(position + 1)
      @used[digit] = false
      @assignment.delete(letter)
    end
    false
  end

  # Checks the columns, right to left, for as long as they are fully assigned.
  def consistent?
    carry = 0
    @total.length.times do |column|
      digits = @addends.map { |word| word[column] }.compact.map { |letter| @assignment[letter] }
      result = @assignment[@total[column]]
      return true if result.nil? || digits.include?(nil)
      sum = digits.sum + carry
      return false unless sum % 10 == result
      carry = sum / 10
    end
    carry.zero?
  end
end

chk = Checker.new("puzzle_solvers")

# --- sudoku -------------------------------------------------------------------
easy = Sudoku.new("003020600900305001001806400008102900700000008006708200002609500800203009005010300")
chk.eq("easy sudoku solves", easy.solve, true)
chk.eq("easy sudoku is valid", easy.valid_solution?, true)
chk.eq("easy sudoku solution", easy.to_s,
       "483921657967345821251876493548132976729564138136798245372689514814253769695417382")
chk.eq("easy sudoku needs no guessing", easy.nodes, 49)

puzzles = {
  "escargot" => "1....7.9..3..2...8..96..5....53..9...1..8...26....4...3......1..4......7..7...3..",
  "inkala" => "8..........36......7..9.2...5...7.......457.....1...3...1....68..85...1..9....4..",
  "sparse" => "4.....8.5.3..........7......2.....6.....8.4......1.......6.3.7.5..2.....1.4......"
}
solved = {}
puzzles.each do |name, givens|
  puzzle = Sudoku.new(givens)
  chk.eq("#{name} solves", puzzle.solve, true)
  chk.eq("#{name} is valid", puzzle.valid_solution?, true)
  kept = givens.each_char.with_index.all? { |ch, index| ch == "." || ch == puzzle.to_s[index] }
  chk.eq("#{name} keeps its givens", kept, true)
  solved[name] = puzzle
end
chk.eq("escargot solution", solved["escargot"].to_s, "162857493534129678789643521475312986913586742628794135356478219241935867897261354")
chk.eq("inkala solution", solved["inkala"].to_s,
       "812753649943682175675491283154237896369845721287169534521974368438526917796318452")
chk.eq("sparse solution", solved["sparse"].to_s,
       "417369825632158947958724316825437169791586432346912758289643571573291684164875293")
chk.eq("search nodes", solved.values.map(&:nodes), [211, 12888, 656])

begin
  Sudoku.new("55" + "." * 79)
  outcome = "no error"
rescue ArgumentError => e
  outcome = e.message
end
chk.eq("conflicting givens are rejected", outcome, "conflicting given 5 at cell 1")
chk.eq("an impossible grid has no solution", Sudoku.new("12345678." + "........9" + "." * 63).solve, false)

# --- n-queens -----------------------------------------------------------------
chk.eq("queens counts", (1..9).map { |size| Queens.count(size) }, [1, 0, 0, 2, 10, 4, 40, 92, 352])
chk.eq("queens first solution", Queens.first_solution(8), [0, 4, 7, 5, 2, 6, 1, 3])
chk.eq("queens impossible board", Queens.first_solution(3), nil)

# --- knight's tour ------------------------------------------------------------
tour = KnightTour.new(8).solve(0, 0)
chk.eq("knight's tour is valid", KnightTour.valid?(tour), true)
chk.eq("knight's tour first row", tour[0], [0, 3, 56, 19, 40, 5, 42, 21])
chk.eq("knight's tour on 5x5", KnightTour.valid?(KnightTour.new(5).solve(0, 0)), true)
chk.eq("knight's tour impossible on 4x4", KnightTour.new(4).solve(0, 0), nil)
chk.eq("a broken tour is detected", KnightTour.valid?(tour.map(&:reverse).rotate), false)

# --- cryptarithms -------------------------------------------------------------
send_more = Cryptarithm.new(%w[SEND MORE], "MONEY")
chk.eq("SEND + MORE = MONEY", send_more.solve,
       { "D" => 7, "E" => 5, "Y" => 2, "N" => 6, "R" => 8, "O" => 0, "S" => 9, "M" => 1 })
chk.eq("SEND + MORE adds up", send_more.value_of("SEND") + send_more.value_of("MORE"), send_more.value_of("MONEY"))
chk.eq("MONEY", send_more.value_of("MONEY"), 10_652)

base_ball = Cryptarithm.new(%w[BASE BALL], "GAMES")
base_ball.solve
chk.eq("BASE + BALL = GAMES", %w[BASE BALL GAMES].map { |word| base_ball.value_of(word) }, [7483, 7455, 14_938])
chk.eq("an unsolvable cryptarithm", Cryptarithm.new(%w[AB AB], "AB").solve, nil)
chk.eq("cryptarithm search nodes", [send_more.nodes, base_ball.nodes], [5741, 465])

puts "sudoku nodes: #{solved.map { |name, puzzle| "#{name}=#{puzzle.nodes}" }.join(', ')}"
puts "queens(9) = #{Queens.count(9)}"
puts "SEND + MORE = MONEY -> #{send_more.value_of('SEND')} + #{send_more.value_of('MORE')} = #{send_more.value_of('MONEY')}"
chk.finish

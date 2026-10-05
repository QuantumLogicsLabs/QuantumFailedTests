# A compiler and virtual machine for a small language
#
# "Tiny" has integers, booleans, variables, arithmetic, comparisons,
# short-circuit logic, if/else, while loops and recursive functions. The
# pipeline is a hand-written lexer, a precedence-climbing parser producing
# an AST, a compiler that resolves variables to stack slots and patches
# jump targets, and a stack-based virtual machine with call frames.
#
# Self-checking: each Tiny program is cross-checked against the same
# algorithm written directly in Ruby, the executed-instruction count is
# compared against the reference implementation, and the first mismatch
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

class TinyError < StandardError
end

Token = Struct.new(:type, :text, :line)

class Lexer
  KEYWORDS = %w[fn let if else while return print and or not true false].freeze
  SYMBOLS = %w[== != <= >= ( ) { } , ; + - * / % < > =].freeze

  def initialize(source)
    @source = source
  end

  def tokens
    result = []
    line = 1
    position = 0
    while position < @source.length
      ch = @source[position]
      if ch == "\n"
        line += 1
        position += 1
      elsif ch == " " || ch == "\t" || ch == "\r"
        position += 1
      elsif ch == "#"
        position += 1 while position < @source.length && @source[position] != "\n"
      elsif ch.match?(/[0-9]/)
        start = position
        position += 1 while position < @source.length && @source[position].match?(/[0-9]/)
        result << Token.new(:number, @source[start...position], line)
      elsif ch.match?(/[A-Za-z_]/)
        start = position
        position += 1 while position < @source.length && @source[position].match?(/[A-Za-z0-9_]/)
        word = @source[start...position]
        result << Token.new(KEYWORDS.include?(word) ? :keyword : :identifier, word, line)
      else
        symbol = SYMBOLS.find { |candidate| @source[position, candidate.length] == candidate }
        raise TinyError, "line #{line}: unexpected character '#{ch}'" if symbol.nil?
        result << Token.new(:symbol, symbol, line)
        position += symbol.length
      end
    end
    result << Token.new(:eof, "end of input", line)
  end
end

# AST nodes are plain arrays tagged with a symbol:
#   [:number, 7]  [:variable, "x"]  [:binary, "+", left, right]  [:call, "f", [args]]
#   [:let, "x", expr]  [:if, cond, then_block, else_block]  [:fn, "f", [params], block]
class Parser
  PRECEDENCE = {
    "or" => 1, "and" => 2, "==" => 3, "!=" => 3, "<" => 4, "<=" => 4, ">" => 4, ">=" => 4,
    "+" => 5, "-" => 5, "*" => 6, "/" => 6, "%" => 6
  }.freeze

  def initialize(tokens)
    @tokens = tokens
    @position = 0
  end

  def parse_program
    statements = []
    statements << parse_statement until peek.type == :eof
    statements
  end

  private

  def peek
    @tokens[@position]
  end

  def advance
    token = @tokens[@position]
    @position += 1
    token
  end

  def operator?(token)
    token.type == :symbol || token.type == :keyword
  end

  def check?(text)
    operator?(peek) && peek.text == text
  end

  def match?(text)
    return false unless check?(text)
    @position += 1
    true
  end

  def expect(text)
    return advance if check?(text)
    raise TinyError, "line #{peek.line}: expected '#{text}' but found '#{peek.text}'"
  end

  def expect_name
    raise TinyError, "line #{peek.line}: expected a name but found '#{peek.text}'" unless peek.type == :identifier
    advance.text
  end

  def parse_block
    expect("{")
    statements = []
    statements << parse_statement until check?("}") || peek.type == :eof
    expect("}")
    statements
  end

  def parse_statement
    if match?("fn")
      name = expect_name
      expect("(")
      params = []
      unless check?(")")
        params << expect_name
        params << expect_name while match?(",")
      end
      expect(")")
      [:fn, name, params, parse_block]
    elsif match?("let")
      name = expect_name
      expect("=")
      finish_statement([:let, name, parse_expression])
    elsif match?("if")
      condition = parse_expression
      consequent = parse_block
      alternative = match?("else") ? parse_block : []
      [:if, condition, consequent, alternative]
    elsif match?("while")
      condition = parse_expression
      [:while, condition, parse_block]
    elsif match?("return")
      finish_statement([:return, parse_expression])
    elsif match?("print")
      finish_statement([:print, parse_expression])
    elsif peek.type == :identifier && @tokens[@position + 1].text == "="
      name = advance.text
      advance
      finish_statement([:assign, name, parse_expression])
    else
      finish_statement([:expression, parse_expression])
    end
  end

  def finish_statement(node)
    expect(";")
    node
  end

  def parse_expression(minimum = 1)
    left = parse_unary
    loop do
      token = peek
      precedence = operator?(token) ? PRECEDENCE[token.text] : nil
      break if precedence.nil? || precedence < minimum
      advance
      left = [:binary, token.text, left, parse_expression(precedence + 1)]
    end
    left
  end

  def parse_unary
    return [:unary, "-", parse_unary] if match?("-")
    return [:unary, "not", parse_unary] if match?("not")
    parse_primary
  end

  def parse_primary
    token = advance
    case token.type
    when :number
      [:number, token.text.to_i]
    when :identifier
      return [:variable, token.text] unless match?("(")
      arguments = []
      unless check?(")")
        arguments << parse_expression
        arguments << parse_expression while match?(",")
      end
      expect(")")
      [:call, token.text, arguments]
    else
      case token.text
      when "true" then [:boolean, true]
      when "false" then [:boolean, false]
      when "("
        inner = parse_expression
        expect(")")
        inner
      else
        raise TinyError, "line #{token.line}: unexpected '#{token.text}'"
      end
    end
  end
end

CompiledFunction = Struct.new(:name, :arity, :code, :local_count)

class Compiler
  BINARY_OPS = {
    "+" => :add, "-" => :sub, "*" => :mul, "/" => :div, "%" => :mod,
    "<" => :lt, "<=" => :le, ">" => :gt, ">=" => :ge, "==" => :eq, "!=" => :ne
  }.freeze

  # Returns the compiled top-level code; functions are reachable through :call.
  def compile(program)
    @functions = {}
    declarations, body = program.partition { |statement| statement[0] == :fn }
    declarations.each do |_, name, params, _|
      raise TinyError, "function '#{name}' is already defined" if @functions.key?(name)
      @functions[name] = CompiledFunction.new(name, params.length, [], 0)
    end
    declarations.each { |_, name, params, block| compile_function(@functions[name], params, block) }
    compile_function(CompiledFunction.new("main", 0, [], 0), [], body)
  end

  def function(name)
    @functions.fetch(name)
  end

  private

  def compile_function(function, params, block)
    @code = function.code
    @slots = {}
    params.each { |param| declare(param) }
    block.each { |statement| compile_statement(statement) }
    emit(:push, 0)
    emit(:return)
    function.local_count = @slots.length
    function
  end

  def declare(name)
    raise TinyError, "variable '#{name}' is already declared" if @slots.key?(name)
    @slots[name] = @slots.length
  end

  def slot(name)
    @slots.fetch(name) { raise TinyError, "undefined variable '#{name}'" }
  end

  def emit(op, argument = nil)
    @code << [op, argument]
    @code.length - 1
  end

  def patch(instruction)
    @code[instruction][1] = @code.length
  end

  def compile_statement(statement)
    case statement[0]
    when :let
      compile_expression(statement[2])
      emit(:store, declare(statement[1]))
    when :assign
      compile_expression(statement[2])
      emit(:store, slot(statement[1]))
    when :print
      compile_expression(statement[1])
      emit(:print)
    when :return
      compile_expression(statement[1])
      emit(:return)
    when :expression
      compile_expression(statement[1])
      emit(:pop)
    when :if
      compile_expression(statement[1])
      skip_consequent = emit(:jump_if_false)
      statement[2].each { |inner| compile_statement(inner) }
      skip_alternative = emit(:jump)
      patch(skip_consequent)
      statement[3].each { |inner| compile_statement(inner) }
      patch(skip_alternative)
    when :while
      loop_start = @code.length
      compile_expression(statement[1])
      exit_jump = emit(:jump_if_false)
      statement[2].each { |inner| compile_statement(inner) }
      emit(:jump, loop_start)
      patch(exit_jump)
    when :fn
      raise TinyError, "function '#{statement[1]}' must be declared at the top level"
    end
  end

  def compile_expression(node)
    case node[0]
    when :number, :boolean
      emit(:push, node[1])
    when :variable
      emit(:load, slot(node[1]))
    when :unary
      compile_expression(node[2])
      emit(node[1] == "-" ? :negate : :not)
    when :binary
      compile_binary(node[1], node[2], node[3])
    when :call
      callee = @functions.fetch(node[1]) { raise TinyError, "undefined function '#{node[1]}'" }
      unless callee.arity == node[2].length
        raise TinyError, "#{node[1]} expects #{callee.arity} argument(s), got #{node[2].length}"
      end
      node[2].each { |argument| compile_expression(argument) }
      emit(:call, callee)
    end
  end

  def compile_binary(operator, left, right)
    compile_expression(left)
    case operator
    when "and"
      short_circuit = emit(:jump_if_false)
      compile_expression(right)
      done = emit(:jump)
      patch(short_circuit)
      emit(:push, false)
      patch(done)
    when "or"
      try_right = emit(:jump_if_false)
      emit(:push, true)
      done = emit(:jump)
      patch(try_right)
      compile_expression(right)
      patch(done)
    else
      compile_expression(right)
      emit(BINARY_OPS.fetch(operator))
    end
  end
end

class Machine
  Frame = Struct.new(:function, :pc, :base)
  MAX_DEPTH = 400

  attr_reader :output, :executed

  def initialize
    @output = []
    @executed = 0
  end

  def run(main)
    stack = Array.new(main.local_count, 0)
    frames = [Frame.new(main, 0, 0)]
    frame = frames.last
    code = main.code
    loop do
      op, argument = code[frame.pc]
      frame.pc += 1
      @executed += 1
      case op
      when :push then stack << argument
      when :load then stack << stack[frame.base + argument]
      when :store then stack[frame.base + argument] = stack.pop
      when :pop then stack.pop
      when :negate then stack << -stack.pop
      when :not then stack << !truthy?(stack.pop)
      when :jump then frame.pc = argument
      when :jump_if_false then frame.pc = argument unless truthy?(stack.pop)
      when :print then @output << stack.pop
      when :call
        raise TinyError, "stack overflow in #{argument.name}" if frames.length >= MAX_DEPTH
        base = stack.length - argument.arity
        (argument.local_count - argument.arity).times { stack << 0 }
        frame = Frame.new(argument, 0, base)
        frames << frame
        code = argument.code
      when :return
        value = stack.pop
        finished = frames.pop
        stack.pop(stack.length - finished.base)
        return @output if frames.empty?
        stack << value
        frame = frames.last
        code = frame.function.code
      else
        right = stack.pop
        left = stack.pop
        stack << binary(op, left, right)
      end
    end
  end

  private

  def truthy?(value)
    value != false && value != 0
  end

  def binary(op, left, right)
    case op
    when :add then left + right
    when :sub then left - right
    when :mul then left * right
    when :div
      raise TinyError, "division by zero" if right.zero?
      left / right
    when :mod
      raise TinyError, "division by zero" if right.zero?
      left % right
    when :lt then left < right
    when :le then left <= right
    when :gt then left > right
    when :ge then left >= right
    when :eq then left == right
    when :ne then left != right
    else raise TinyError, "unknown instruction #{op}"
    end
  end
end

module Tiny
  def self.compile(source)
    compiler = Compiler.new
    [compiler.compile(Parser.new(Lexer.new(source).tokens).parse_program), compiler]
  end

  def self.run(source)
    main, = compile(source)
    machine = Machine.new
    machine.run(main)
    machine
  end

  def self.disassemble(function)
    function.code.map do |op, argument|
      case argument
      when nil then op.to_s
      when CompiledFunction then "#{op} #{argument.name}"
      else "#{op} #{argument}"
      end
    end
  end

  # The error message a program fails with, or "no error".
  def self.error_of(source)
    run(source)
    "no error"
  rescue TinyError => e
    e.message
  end
end

PROGRAM = <<~TINY
  # Benchmarks for the Tiny virtual machine.
  fn fib(n) {
    if n < 2 { return n; }
    return fib(n - 1) + fib(n - 2);
  }

  fn gcd(a, b) {
    while b != 0 {
      let t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  fn gcd_sum(limit) {
    let total = 0;
    let i = 1;
    while i <= limit {
      total = total + gcd(i, 360);
      i = i + 1;
    }
    return total;
  }

  fn is_prime(n) {
    if n < 2 { return false; }
    let d = 2;
    while d * d <= n {
      if n % d == 0 { return false; }
      d = d + 1;
    }
    return true;
  }

  fn count_primes(limit) {
    let count = 0;
    let n = 2;
    while n < limit {
      if is_prime(n) { count = count + 1; }
      n = n + 1;
    }
    return count;
  }

  fn collatz_steps(n) {
    let steps = 0;
    while n != 1 {
      if n % 2 == 0 { n = n / 2; } else { n = 3 * n + 1; }
      steps = steps + 1;
    }
    return steps;
  }

  fn longest_collatz(limit) {
    let best = 1;
    let best_steps = 0;
    let n = 1;
    while n < limit {
      let s = collatz_steps(n);
      if s > best_steps { best = n; best_steps = s; }
      n = n + 1;
    }
    return best * 1000 + best_steps;
  }

  fn power_mod(base, exponent, modulus) {
    let result = 1;
    base = base % modulus;
    while exponent > 0 {
      if exponent % 2 == 1 { result = result * base % modulus; }
      base = base * base % modulus;
      exponent = exponent / 2;
    }
    return result;
  }

  print fib(20);
  print gcd_sum(1000);
  print count_primes(2000);
  print longest_collatz(600);
  print power_mod(7, 222, 1000007);
  print 2 + 3 * 4 - (10 - 4) / 2;
  print -3 * -(2 + 5) % 4;
  print not (1 < 2) or 3 >= 3 and 5 != 6;
  print 1 > 2 and 1 / 0 == 0;
TINY

def native_fib(n)
  n < 2 ? n : native_fib(n - 1) + native_fib(n - 2)
end

def native_count_primes(limit)
  (2...limit).count { |n| (2..Integer.sqrt(n)).none? { |d| (n % d).zero? } }
end

def native_collatz_steps(n)
  steps = 0
  until n == 1
    n = n.even? ? n / 2 : 3 * n + 1
    steps += 1
  end
  steps
end

def native_longest_collatz(limit)
  best = (1...limit).max_by { |n| [native_collatz_steps(n), -n] }
  best * 1000 + native_collatz_steps(best)
end

chk = Checker.new("mini_language_vm")

# --- lexer and parser ---------------------------------------------------------
tokens = Lexer.new("let x1 = 40 + 2; # note\nprint x1 >= 42;").tokens
chk.eq("token texts", tokens.map(&:text), ["let", "x1", "=", "40", "+", "2", ";", "print", "x1", ">=", "42", ";", "end of input"])
chk.eq("token types", tokens.map(&:type).tally,
       { keyword: 2, identifier: 2, symbol: 5, number: 3, eof: 1 })
chk.eq("token lines", tokens.map(&:line).uniq, [1, 2])

tree = Parser.new(Lexer.new("print 1 + 2 * 3 < 10 and not false;").tokens).parse_program
chk.eq("operator precedence", tree,
       [[:print, [:binary, "and",
                  [:binary, "<", [:binary, "+", [:number, 1], [:binary, "*", [:number, 2], [:number, 3]]], [:number, 10]],
                  [:unary, "not", [:boolean, false]]]]])
chk.eq("left associativity", Parser.new(Lexer.new("print 10 - 4 - 3;").tokens).parse_program,
       [[:print, [:binary, "-", [:binary, "-", [:number, 10], [:number, 4]], [:number, 3]]]])

# --- compiler -----------------------------------------------------------------
_, compiler = Tiny.compile("fn add(a, b) { return a + b; } fn twice(n) { let m = add(n, n); return m; } print twice(4);")
chk.eq("compiled add", Tiny.disassemble(compiler.function("add")), ["load 0", "load 1", "add", "return", "push 0", "return"])
chk.eq("compiled twice", Tiny.disassemble(compiler.function("twice")),
       ["load 0", "load 0", "call add", "store 1", "load 1", "return", "push 0", "return"])
chk.eq("local slots", [compiler.function("add").local_count, compiler.function("twice").local_count], [2, 2])

loop_main, = Tiny.compile("let i = 0; while i < 3 { i = i + 1; } print i;")
chk.eq("compiled loop", Tiny.disassemble(loop_main),
       ["push 0", "store 0", "load 0", "push 3", "lt", "jump_if_false 11", "load 0", "push 1", "add", "store 0",
        "jump 2", "load 0", "print", "push 0", "return"])

# --- small programs -----------------------------------------------------------
chk.eq("arithmetic", Tiny.run("print 7 / 2; print 7 % 2; print 2 * 3 + 4; print -(5 - 9);").output, [3, 1, 10, 4])
chk.eq("branches", Tiny.run("let x = 5; if x > 3 { print 1; } else { print 2; } if x > 9 { print 3; }").output, [1])
chk.eq("recursion", Tiny.run("fn fact(n) { if n <= 1 { return 1; } return n * fact(n - 1); } print fact(12);").output, [479_001_600])
chk.eq("functions return 0 by default", Tiny.run("fn noop() { } print noop();").output, [0])

# --- error reporting ----------------------------------------------------------
chk.eq("errors",
       [
         Tiny.error_of("print 1 / 0;"),
         Tiny.error_of("print x;"),
         Tiny.error_of("print foo(1);"),
         Tiny.error_of("fn f(a) { return a; } print f(1, 2);"),
         Tiny.error_of("let a = 1 let b = 2;"),
         Tiny.error_of("let a = 1;\nprint a +;\n"),
         Tiny.error_of("let a = 3 $ 4;"),
         Tiny.error_of("let a = 1; let a = 2;"),
         Tiny.error_of("fn f(n) { return f(n + 1); } print f(0);"),
         Tiny.error_of("if true { print 1;")
       ],
       [
         "division by zero",
         "undefined variable 'x'",
         "undefined function 'foo'",
         "f expects 1 argument(s), got 2",
         "line 1: expected ';' but found 'let'",
         "line 2: unexpected ';'",
         "line 1: unexpected character '$'",
         "variable 'a' is already declared",
         "stack overflow in f",
         "line 1: expected '}' but found 'end of input'"
       ])

# --- benchmark program --------------------------------------------------------
machine = Tiny.run(PROGRAM)
expected = [
  native_fib(20),
  (1..1000).sum { |i| i.gcd(360) },
  native_count_primes(2000),
  native_longest_collatz(600),
  7.pow(222, 1_000_007),
  11,
  1,
  true,
  false
]
chk.eq("benchmark matches native Ruby", machine.output, expected)
chk.eq("benchmark output", machine.output, [6765, 10318, 303, 327143, 302138, 11, 1, true, false])
chk.eq("instructions executed", machine.executed, 1245886)

puts "output: #{machine.output.join(' ')}"
puts "executed #{machine.executed} instructions"
chk.finish

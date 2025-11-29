import Std.Internal.Parsec
import Arrangement

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/------------------------------------------------------------------------
 Parsing stuff
 ------------------------------------------------------------------------/


/- Legal Scheme identifier symbols -/
def isSymbol (c : Char) : Bool :=
  Option.isSome (("!#$%&|*+-/:<=>?@^_~".toList).find? (· == c))
def symbol : Parser Char := satisfy isSymbol

/- Run a parser on the input, report on matches -/
def readExpr : String → String := fun input =>
  let result := Parser.run symbol input
  match result with
  | Except.ok c => s!"Found match: {c}"
  | Except.error e => s!"No match: {e}"


/------------------------------------------------------------------------
 Main
 ------------------------------------------------------------------------/

-- CLI greeting
def mainArgs (args: List String) : IO Unit := do
  let stdout <- IO.getStdout
  if h : args.length > 0 then
    let name := args[0]'h
    stdout.putStrLn s!"Hello, {name}"
  else
    stdout.putStrLn s!"Hello, anonymous"
  return ()

-- knock, knock
def mainInteractive : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Who is it?"
  let name <- stdin.getLine
  stdout.putStrLn s!"Hello, {name}"
  return ()

-- sums two args only, reporting parse and arg list errors
def main2Args (args: List String) : IO Unit := do
  let stdout <- IO.getStdout
  if h : args.length > 1 then
    have h0 : 0 < args.length := Nat.zero_lt_of_lt h
    let arg0 := args[0]'h0
    let arg1 := args[1]'h
    let n0 := arg0.toInt?
    let n1 := arg1.toInt?
    match n0, n1 with
    | some x, some y =>
      let sum := x + y
      stdout.putStrLn s!"Your sum is {sum}"
    | _, _ => stdout.putStrLn s!"Error: could not parse two numbers"
  else
    stdout.putStrLn s!"Error: too few arguments"
  return ()

-- sums any number of arguments, reporting unparseable args at the end
def mainAnyArgs (args: List String) : IO Unit := do
  let stdout <- IO.getStdout
  let f (s : String) (acc : Option Int) : Option Int := do
    let n <- s.toInt?  -- yolo
    let acc' <- acc
    pure (acc' + n)
  let sum := args.foldr f (some 0)
  match sum with
  | some m => stdout.putStrLn s!"Your sum is {m}"
  | none => stdout.putStrLn s!"Your sum could not be computed! An arg could not be parsed as an Int"
  return ()

/-
$ lake exe arrangement "!foobar"
Found match: !

$ lake exe arrangement foobar
No match: offset 0: condition not satisfied
-/
def main (args: List String) : IO Unit := do
  let stdout ← IO.getStdout
  if h : 0 < args.length then
    let input := args[0]'h
    stdout.putStrLn (readExpr input)
  else
    stdout.putStrLn "Usage: lake exe arrangement <text_to_parse>"



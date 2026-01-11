import Arrangement.Ast
import Arrangement.Eval
import Arrangement.Parser

------------------------------------------------------------------------
-- Main
------------------------------------------------------------------------

-- CLI greeting; just testing out main and args parsing
def mainArgs (args: List String) : IO Unit := do
  let stdout <- IO.getStdout
  if h : args.length > 0 then
    let name := args[0]'h
    stdout.putStrLn s!"Hello, {name}"
  else
    stdout.putStrLn s!"Hello, anonymous"

-- knock, knock
def mainInteractive : IO Unit := do
  let stdin <- IO.getStdin
  let stdout <- IO.getStdout
  stdout.putStrLn s!"Who is it?"
  let name <- stdin.getLine
  stdout.putStrLn s!"Hello, {name}"

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

------------------------------------------------------------------------
-- Real Main and helper functions
------------------------------------------------------------------------

def flushStr (s : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr s
  stdout.flush

def readPrompt (prompt : String) : IO String := do
  flushStr prompt
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  pure input.trim

/-- Evaluate an expression and trap errors -/
def evalString (expr : String) : IO String :=
    pure $ extractValue ∘ trapError $ do  -- ThrowsError monad
      let e ← readExpr expr
      let v ← eval e
      pure ∘ toString $ v

def evalAndPrint (expr : String) : IO Unit := do
  let stdout ← IO.getStdout
  evalString expr >>= stdout.putStrLn

/-- Execute a prompt then based on the result perform the action or return -/
partial def until_ {α : Type} {M : Type → Type} [Monad M] (pred : α → Bool) (prompt : M α) (action : α → M Unit) : M Unit := do
  let result ← prompt
  if pred result then
    pure ()
  else
    action result
    until_ pred prompt action

def runRepl : IO Unit := until_ (· == "quit") (readPrompt "Scheme>>> ") evalAndPrint

/--
$ lake exe arrangement
Scheme>>> (+ 2 3)
5
Scheme>>> (cons this '())
(this)                     -- TODO: this should throw `Unrecognized special form: this`
Scheme>>> (cons 'this '())
(this)
Scheme>>> (cons 2 3)
(2 . 3)
Scheme>>> quit
$
-/
def main (args: List String) : IO Unit := do
  let stdout ← IO.getStdout
  match h : args.length with
  | 0 => runRepl
  | 1 => evalAndPrint args[0]  -- automatically proved in bounds by `h` annotation
  | _ => stdout.putStrLn "Program takes only 0 or 1 argument"

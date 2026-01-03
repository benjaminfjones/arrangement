import Arrangement.Ast
import Arrangement.Error
import Arrangement.Parser

open LispVal


------------------------------------------------------------------------
-- Evaluation: Code data type to Data data type
------------------------------------------------------------------------

def unwrapNumber : LispVal → ThrowsError Nat
  | .number n => pure n
  | notNum => throwError $ LispError.typeMismatch "number" notNum

def numericBinop (op : Nat → Nat → Nat) (args : List LispVal) : ThrowsError LispVal :=
  match args with
  | [] => throwError $ LispError.numArgs 2 []
  | singleVal@([_]) => throwError $ LispError.numArgs 2 singleVal
  | hd :: tl => do
    let uhd ← unwrapNumber hd
    let utl ← List.mapM unwrapNumber tl
    pure $ LispVal.number (List.foldl op uhd utl)

def primitives : List (String × (List LispVal -> ThrowsError LispVal)) :=
  [
    ("+", numericBinop (· + ·)),
    ("-", numericBinop (· - ·)),
    ("*", numericBinop (· * ·)),
    ("/", numericBinop (fun x y => Nat.div x y)),
    ("mod", numericBinop (fun x y => Nat.mod x y)),
    -- TODO: remainder?
  ]

def apply (func : String) (args : List LispVal) : ThrowsError LispVal :=
  match primitives.lookup func with
  | none => throwError $ LispError.notFunction "Unrecognized primitive function args" func
  | some f => f args

def eval : LispVal → ThrowsError LispVal
  | val@(.atom _) => pure val
  | val@(.number _) => pure val
  | val@(.string _) => pure val
  | val@(.char _) => pure val
  | val@(.bool _) => pure val
  | .list [LispVal.atom "quote", val] => pure val
  | .list [LispVal.atom "symbol?", val] => pure $ LispVal.bool (symbol? val)
  | .list [LispVal.atom "string?", val] => pure $ LispVal.bool (string? val)
  | .list [LispVal.atom "number?", val] => pure $ LispVal.bool (number? val)
  | .list [LispVal.atom "symbol->string", LispVal.atom name]   => pure $ LispVal.string name
  | .list [LispVal.atom "string->symbol", LispVal.string name] => pure $ LispVal.atom name
  | .list (LispVal.atom func :: args) => List.mapM eval args >>= apply func
  | val => panic! s!"not implemented: eval {val}"

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

/-- Read, Eval, Print; trap errors and convert to strings -/
def rep : String → String := fun input => extractValue ∘ trapError $ do
  let e ← readExpr input
  let v ← eval e
  pure ∘ toString $ v

#guard rep "(+ 2 2)" == "4"
#guard rep "(/ 2 2)" == "1"
#guard rep "(/ 2 0)" == "0"  -- div by zero is 0
#guard rep "(- 1 4)" == "0"  -- Nat subtraction saturates at 0
#guard rep "(- 15 5 3 2)" == "5"
#guard rep "(symbol? 6)" == "#f"
#guard rep "(symbol? horse)" == "#t"
-- #guard rep "(symbol? 'horse)" == "#t"  -- TODO: doesn't eval yet b/c general lists don't
#guard rep "(number? 6)" == "#t"
#guard rep "(number? myNumber)" == "#f"
#guard rep "(string? \"sdfsd\")" == "#t"
#guard rep "'(- 15 5 3 2)" == "(- 15 5 3 2)"
#guard rep "(quote (- 15))" == "(- 15)"
#guard rep "(string->symbol \"flying-fish\")" == "flying-fish"
#guard rep "(symbol->string martin)" == "\"martin\""

-- error handling
#guard rep "(+ 2 \"two\")" == "Invalid type: expected number, found \"two\""
#guard rep "(+ 2)" == "Expected 2 args; found values 2"
#guard rep "(what? 2)" == "Unrecognized primitive function args: what?"

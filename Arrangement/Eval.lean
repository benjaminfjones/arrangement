import Arrangement.Ast
import Arrangement.Parser

open LispVal

------------------------------------------------------------------------
-- Evaluation: Code data type to Data data type
------------------------------------------------------------------------

def unwrapNumber : LispVal → Nat
  | .number n => n
  | _ => 0  -- TODO: placeholder

def numericBinop (op : Nat → Nat → Nat) (args : List LispVal) : LispVal :=
  match args with
  | [] => .number 0  -- TODO: placeholder
  | hd :: tl => LispVal.number $ List.foldl op (unwrapNumber hd) (tl.map unwrapNumber)

def primitives : List (String × (List LispVal -> LispVal)) :=
  [
    ("+", numericBinop (· + ·)),
    ("-", numericBinop (· - ·)),
    ("*", numericBinop (· * ·)),
    ("/", numericBinop (fun x y => Nat.div x y)),
    ("mod", numericBinop (fun x y => Nat.mod x y)),
    -- TODO: remainder?
  ]

def apply (func : String) (args : List LispVal) : LispVal :=
  match primitives.lookup func with
  | none => LispVal.bool false  -- TODO: exception placeholder
  | some f => f args

def eval : LispVal → LispVal
  | val@(.atom _) => val
  | val@(.number _) => val
  | val@(.string _) => val
  | val@(.char _) => val
  | val@(.bool _) => val
  | .list [LispVal.atom "quote", val] => val
  | .list [LispVal.atom "symbol?", val] => LispVal.bool (symbol? val)
  | .list [LispVal.atom "string?", val] => LispVal.bool (string? val)
  | .list [LispVal.atom "number?", val] => LispVal.bool (number? val)
  | .list [LispVal.atom "symbol->string", LispVal.atom name] => LispVal.string name
  | .list [LispVal.atom "string->symbol", LispVal.string name] => LispVal.atom name
  | .list (LispVal.atom func :: args) => apply func $ args.map eval
  | val => panic! s!"not implemented: eval {val}"

------------------------------------------------------------------------
-- Tests
------------------------------------------------------------------------

/-- Read, Eval, Print -/
def rep : String → String := toString ∘ eval ∘ readExpr

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

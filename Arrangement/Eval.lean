import Arrangement.Ast
import Arrangement.Error
import Arrangement.Parser

open LispVal


------------------------------------------------------------------------
-- Evaluation: Code data type to Data data type
------------------------------------------------------------------------

def unwrapNum : LispVal → ThrowsError Nat
  | .number n => pure n
  | notNum => throwError $ LispError.typeMismatch "number" notNum

def unwrapStr : LispVal → ThrowsError String
  | .string s => pure s
  | notNum => throwError $ LispError.typeMismatch "string" notNum

def unwrapBool : LispVal → ThrowsError Bool
  | .bool b => pure b
  | notNum => throwError $ LispError.typeMismatch "bool" notNum

def numericBinop (op : Nat → Nat → Nat) (args : List LispVal) : ThrowsError LispVal :=
  match args with
  | [] => throwError $ LispError.numArgs 2 []
  | singleVal@([_]) => throwError $ LispError.numArgs 2 singleVal
  | hd :: tl => do
    let uhd ← unwrapNum hd
    let utl ← List.mapM unwrapNum tl
    pure $ LispVal.number (List.foldl op uhd utl)

def boolBinop (unpacker : LispVal → ThrowsError a) (op : a → a → Bool) (args : List LispVal) : ThrowsError LispVal :=
  if h : args.length != 2 then
    throwError $ LispError.numArgs 2 args
  else do
    have h0 : args.length > 0 := by grind
    have h1 : args.length > 1 := by grind
    let left ← unpacker (args[0]'h0)
    let right ← unpacker (args[1]'h1)
    pure ∘ LispVal.bool $ op left right

def numBoolBinop : (Nat → Nat → Bool) → List LispVal → ThrowsError LispVal := boolBinop unwrapNum
def boolBoolBinop : (Bool → Bool → Bool) → List LispVal → ThrowsError LispVal := boolBinop unwrapBool
def strBoolBinop : (String → String → Bool) → List LispVal → ThrowsError LispVal := boolBinop unwrapStr

def primitives : List (String × (List LispVal -> ThrowsError LispVal)) :=
  [
    ("+", numericBinop (· + ·)),
    ("-", numericBinop (· - ·)),
    ("*", numericBinop (· * ·)),
    ("/", numericBinop (fun x y => Nat.div x y)),
    ("mod", numericBinop (fun x y => Nat.mod x y)),
    -- TODO: remainder?
    ("=", numBoolBinop (· == ·)),
    ("<", numBoolBinop (· < ·)),
    (">", numBoolBinop (· > ·)),
    ("/=", numBoolBinop (· != ·)),
    (">=", numBoolBinop (· >= ·)),
    ("<=", numBoolBinop (· <= ·)),
    ("&&", boolBoolBinop (· && ·)),
    ("||", boolBoolBinop (· || ·)),
    ("string=?", strBoolBinop (· == ·)),
    ("string<?", strBoolBinop (· < ·)),
    ("string>?", strBoolBinop (· > ·)),
    ("string<=?", strBoolBinop (· <= ·)),
    ("string>=?", strBoolBinop (· >= ·)),
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
  | .list [LispVal.atom "quote", val] => pure val  -- don't eval `val`
  | .list [LispVal.atom "symbol?", val] => eval val >>= pure ∘ LispVal.bool ∘ symbol?
  | .list [LispVal.atom "string?", val] => eval val >>= pure ∘ LispVal.bool ∘ string?
  | .list [LispVal.atom "number?", val] => eval val >>= pure ∘ LispVal.bool ∘ number?
  | .list [LispVal.atom "symbol->string", LispVal.atom name]   => pure $ LispVal.string name
  | .list [LispVal.atom "string->symbol", LispVal.string name] => pure $ LispVal.atom name
  | .list [LispVal.atom "if", cond, conseq, alt] => do
    let result ← eval cond
    match result with
    | .bool false => eval alt
    | _ => eval conseq
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
#guard rep "(symbol? 'horse)" == "#t"  -- was an eval bug here todo w/ not recursively eval'ing arguments
#guard rep "(number? 6)" == "#t"
#guard rep "(number? myNumber)" == "#f"
#guard rep "(string? \"sdfsd\")" == "#t"
#guard rep "'(- 15 5 3 2)" == "(- 15 5 3 2)"
#guard rep "(quote (- 15))" == "(- 15)"
#guard rep "(string->symbol \"flying-fish\")" == "flying-fish"
#guard rep "(symbol->string martin)" == "\"martin\""
#guard rep "(< 2 3)" == "#t"
#guard rep "(> 2 3)" == "#f"
#guard rep "(>= 3 3)" == "#t"
#guard rep "(string=? \"test\" \"test\")" == "#t" -- TODO: extra ws breaks this one
#guard rep "(string<? \"abc\" \"bba\")" == "#t"
#guard rep "(if (> 2 3) \"no\" \"yes\")" == "\"yes\""
#guard rep "(if (= 3 3) (+ 2 3 (- 5 1)) \"you thought the type system was reasonable\")" == "9"

-- error handling
#guard rep "(+ 2 \"two\")" == "Invalid type: expected number, found \"two\""
#guard rep "(+ 2)" == "Expected 2 args; found values 2"
#guard rep "(what? 2)" == "Unrecognized primitive function args: what?"

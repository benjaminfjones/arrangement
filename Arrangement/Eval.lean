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

def car : List LispVal → ThrowsError LispVal
  | [.list (x :: _)] => pure x          -- (car '(a b c)) ===> a, .list [] is handled by last case
  | [.dottedList (x :: _) _] => pure x  -- (car '(a b . c)) ===> a, .dottedList [] _ is last case
  | [badType] => throwError (LispError.typeMismatch "pair" badType)
  | badArgsList => throwError (LispError.numArgs 1 badArgsList)

def cdr : List LispVal → ThrowsError LispVal
  | [.list (_ :: xs)] => pure (.list xs)                  -- (cdr '(a b c)) ===> (b c)
  | [.dottedList [_] x] => pure x                         -- dotted lists are weird
  | [.dottedList (_ :: xs) x] => pure (.dottedList xs x)  -- dotted lists are weird
  | [badType] => throwError (LispError.typeMismatch "pair" badType)
  | badArgsList => throwError (LispError.numArgs 1 badArgsList)

def cons : List LispVal → ThrowsError LispVal
  -- (cons x NIL)
  | [x, .list []] => pure (.list [x])
  -- (cons x rest)
  | [x, .list rest] => pure (.list (x :: rest))
  -- (cons x '(y . z)) ===> (x y . z)
  -- cons with a dotted list preserves the improper tail
  | [x, .dottedList xs tl] => pure (.dottedList (x :: xs) tl)
  -- `x` is anything, even a list itself and `y` is becomes the terminator
  -- (cons p q) ===> (p . q) when `q` is not a list
  | [x, y] => pure (.dottedList [x] y)
  | badArgsList => throwError (LispError.numArgs 2 badArgsList)

-- TODO: eqv: prove termination
mutual
partial def eqvPair : LispVal → LispVal → Bool := fun x y =>
  match eqv [x, y] with
  | Except.ok (LispVal.bool val) => val
  | Except.ok _ => false     -- unreachable
  | Except.error _ => false  -- unreachable

partial def eqvPairAll : List LispVal → List LispVal → Bool
  | [], [] => true
  | (_x :: _), [] => false
  | [], (_x :: _) => false
  | (x :: xs), (y :: ys) => eqvPair x y && eqvPairAll xs ys

partial def eqv : List LispVal → ThrowsError LispVal
  | [.atom arg1, .atom arg2] => pure (LispVal.bool (arg1 == arg2))
  | [.number arg1, .number arg2] => pure (LispVal.bool (arg1 == arg2))
  | [.string arg1, .string arg2] => pure (LispVal.bool (arg1 == arg2))
  | [.char arg1, .char arg2] => pure (LispVal.bool (arg1 == arg2))
  | [.bool arg1, .bool arg2] => pure (LispVal.bool (arg1 == arg2))
  | [.dottedList xs x, .dottedList ys y] => pure (LispVal.bool (eqvPairAll (xs ++ [x]) (ys ++ [y])))
  | [.list arg1, .list arg2] => pure (LispVal.bool (eqvPairAll arg1 arg2))
  | [_, _] => pure (LispVal.bool false)
  | badArgs => throwError (LispError.numArgs 2 badArgs)
end  -- mutual

def primitives : List (String × (List LispVal -> ThrowsError LispVal)) :=
  [
    ("+", numericBinop (· + ·)),
    ("-", numericBinop (· - ·)),
    ("*", numericBinop (· * ·)),
    ("/", numericBinop (fun x y => Nat.div x y)),
    ("mod", numericBinop (fun x y => Nat.mod x y)),
    -- TODO: remainder?
    -- Numerical predicates
    ("=", numBoolBinop (· == ·)),
    ("<", numBoolBinop (· < ·)),
    (">", numBoolBinop (· > ·)),
    ("/=", numBoolBinop (· != ·)),
    (">=", numBoolBinop (· >= ·)),
    ("<=", numBoolBinop (· <= ·)),
    -- Boolean operators
    ("&&", boolBoolBinop (· && ·)),
    ("||", boolBoolBinop (· || ·)),
    -- String predicates
    ("string=?", strBoolBinop (· == ·)),
    ("string<?", strBoolBinop (· < ·)),
    ("string>?", strBoolBinop (· > ·)),
    ("string<=?", strBoolBinop (· <= ·)),
    ("string>=?", strBoolBinop (· >= ·)),
    -- List operations
    ("car", car),
    ("cdr", cdr),
    ("cons", cons),
    -- equality and equivalence
    ("eq?", eqv),
    ("eqv?", eqv),
    -- ("equal?", equal),
  ]

def apply (func : String) (args : List LispVal) : ThrowsError LispVal :=
  match primitives.lookup func with
  | none => throwError $ LispError.notFunction "Unrecognized primitive function args" func
  | some f => f args

-- All functions mutual with `eval`
mutual

/--
A semantically simple version of `cond`. For the full version, see
https://conservatory.scheme.org/schemers/Documents/Standards/R5RS/HTML/r5rs-Z-H-7.html#%_sec_4.2.1

(cond <clause₁> <clause₂> ...)
where
<clause> := (<test> <expression>), or
            (else <expression>)

Evaluation of tests proceeds until a #t is encountered, at which point the
expression is eval'd and returned. The first `else` clause encountered causes
its expression to be eval'd and returned. If all tests are false and there is
no else clause, the value is unspecified (here, #f).
-/
partial def evalCond (clauses : List LispVal) : ThrowsError LispVal :=
  if clauses.length > 0 then
    -- recursive helper that processes clauses, i.e. two-element lists
    let rec aux (cs : List LispVal) : ThrowsError LispVal := match cs with
      -- no more clauses
      | [] => pure (LispVal.bool false)  -- the unspecified value is specified
      | .list [c, e] :: rest => match c with
        | LispVal.atom "else" => eval e  -- semantics are that we immediately eval upon an else
        | t => do
          let result ← eval t
          match result with
          | .bool true => eval e
          | _ => aux rest
      | badArgsList => throwError $ LispError.numArgs 2 badArgsList
    aux clauses
  else
    throwError $ LispError.default "`cond` must have at least one clause"

partial def eval : LispVal → ThrowsError LispVal
  | val@(.atom _) => pure val
  | val@(.number _) => pure val
  | val@(.string _) => pure val
  | val@(.char _) => pure val
  | val@(.bool _) => pure val
  | .list (LispVal.atom "cond" :: clauses) => evalCond clauses
  | .list [LispVal.atom "if", cond, conseq, alt] => do
    let result ← eval cond
    match result with
    | .bool false => eval alt
    | _ => eval conseq
  | .list [LispVal.atom "number?", val] => eval val >>= pure ∘ LispVal.bool ∘ number?
  | .list [LispVal.atom "quote", val] => pure val  -- don't eval `val`
  | .list [LispVal.atom "string->symbol", LispVal.string name] => pure $ LispVal.atom name
  | .list [LispVal.atom "string?", val] => eval val >>= pure ∘ LispVal.bool ∘ string?
  | .list [LispVal.atom "symbol->string", LispVal.atom name]   => pure $ LispVal.string name
  | .list [LispVal.atom "symbol?", val] => eval val >>= pure ∘ LispVal.bool ∘ symbol?
  | .list (LispVal.atom func :: args) => List.mapM eval args >>= apply func
  | val => panic! s!"not implemented: eval {val}"

end  -- mutuals with `eval`

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
#guard rep "(cons 2 '(3 4))" == "(2 3 4)"
#guard rep "(car '(3 4))" == "3"
#guard rep "(cdr '(3 4))" == "(4)"

#guard rep "(eqv? 3 3)" == "#t"
#guard rep "(eqv? 1 3)" == "#f"
#guard rep "(eqv? 'atom 'atom)" == "#t"
#guard rep "(eqv? 1 'atom)" == "#f"
#guard rep "(eqv? '(1 2) '(1 2))" == "#t"
#guard rep "(eqv? '(1 2) '(1 23))" == "#f"
#guard rep "(eqv? '(1) '(1 2))" == "#f"
#guard rep "(eqv? '(\"1\") '(1))" == "#f"  -- eqv? is not weak typed
#guard rep "(eqv? '(1 . 2) '(1 . 2))" == "#t"
#guard rep "(eqv? '(1 3 . 2) '(1 . 2))" == "#f"
#guard rep "(eqv? '(1 3 . 2) '(1 . 3))" == "#f"

#guard rep "(cond ((> 3 2) 'greater) ((< 3 2) 'less))" == "greater"
#guard rep "(cond ((> 1 1) 'greater) ((< 1 1) 'less))" == "#f"  -- the unspecified value
#guard rep "(cond ((> 3 3) 'greater) ((< 3 3) 'less) (else 'equal))" == "equal"

-- error handling
#guard rep "(+ 2 \"two\")" == "Invalid type: expected number, found \"two\""
#guard rep "(+ 2)" == "Expected 2 args; found values 2"
#guard rep "(what? 2)" == "Unrecognized primitive function args: what?"
#guard rep "(eqv? 1 'atom 'bomb)" == "Expected 2 args; found values 1 atom bomb"

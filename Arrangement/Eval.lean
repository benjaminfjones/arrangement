import Arrangement.Ast

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
  | .list [LispVal.string "quote", val] => val
  | .list (LispVal.atom func :: args) => apply func $ args.map eval
  | val => panic! s!"not implemented: eval {val}"

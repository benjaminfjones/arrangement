
------------------------------------------------------------------------
-- Lisp AST
------------------------------------------------------------------------

inductive LispVal where
  | atom : String → LispVal                        -- abc
  | list : List LispVal → LispVal                  -- (a b c)
  | dottedList : List LispVal → LispVal → LispVal  -- (a b . c)
  | number : Nat → LispVal                         -- 6
  | string : String → LispVal                      -- "foo"
  | char : Char → LispVal                          -- #\a #\space #\newline
  | bool : Bool → LispVal                          -- true
  deriving Repr

def unwords : List String → String := fun xs => String.intercalate " " xs

mutual
-- Note: This match is used instead of unwords ∘ map toString to ensure termination
-- automatically.
def toStringList : List LispVal → String
  | [] => ""
  | hd :: [] => lispValToString hd
  | hd :: tl => lispValToString hd ++ " " ++ toStringList tl

def lispValToString : LispVal → String
  | .atom name => name
  | .list xs => "(" ++ toStringList xs ++ ")"
  | .dottedList head rest => "(" ++ toStringList head ++ " . " ++ lispValToString rest ++ ")"
  | .number x => s!"{x}"
  | .string s => "\"" ++ s ++ "\""
  | .char c => "'" ++ c.toString ++ "'"
  | .bool true => "#t"
  | .bool false => "#f"
end  -- mutual

instance : ToString LispVal where
  toString := lispValToString

#guard toString (LispVal.atom "mosquito") == "mosquito"
#guard toString (LispVal.string "mosquito") == "\"mosquito\""
#guard toString (LispVal.number 6) == "6"
#guard toString (LispVal.list [LispVal.atom "mayfly", LispVal.number 7]) == "(mayfly 7)"

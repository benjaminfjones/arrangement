
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

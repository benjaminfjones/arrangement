import Arrangement.Ast

------------------------------------------------------------------------
-- Errors
------------------------------------------------------------------------

inductive LispError where
  | numArgs : Nat → List LispVal → LispError
  | typeMismatch : String → LispVal → LispError
  | parser : String → LispError  -- TODO: replace String w/ ParseError
  | badSpecialForm : String → LispVal → LispError
  | notFunction : String → String → LispError
  | unboundVar : String → String → LispError
  | default : String → LispError
  deriving Inhabited, Repr

open LispError

def showError : LispError -> String
  | unboundVar message varname  => message ++ ": " ++ varname
  | badSpecialForm message form => message ++ ": " ++ toString form
  | notFunction message func    => message ++ ": " ++ func
  | numArgs expected found      => "Expected " ++ toString expected ++ " args; found values " ++ toStringList found
  | typeMismatch expected found => "Invalid type: expected " ++ expected ++ ", found " ++ toString found
  | parser parseErr             => "Parse error at " ++ parseErr
  | LispError.default message   => "Error: " ++ message

instance : ToString LispError where toString := showError

/-- `ThrowsError α` is a LispError or a value of type α -/
abbrev ThrowsError : Type → Type := Except LispError

def throwError : LispError → ThrowsError α := Except.error

/-- Map underlying errors into strings; the result always has a valid right content -/
def trapError (action : ThrowsError String) : ThrowsError String := tryCatch action (pure ∘ toString)
def extractValue {α : Type} [Inhabited α] : ThrowsError α → α
  | Except.ok v => v
  | Except.error _ => panic! "assertion error"

import Std.Internal.Parsec
import Arrangement

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/------------------------------------------------------------------------
 Lisp AST
 ------------------------------------------------------------------------/

inductive LispVal where
  | atom : String → LispVal                        -- abc
  | list : List LispVal → LispVal                  -- (a b c)
  | dottedList : List LispVal → LispVal → LispVal  -- (a b . c)
  | number : Nat → LispVal                         -- 6
  | string : String → LispVal                      -- "foo"
  | char : Char → LispVal                          -- #\a #\space #\newline
  | bool : Bool → LispVal                          -- true
  deriving Repr

/------------------------------------------------------------------------
 Parsing stuff
 ------------------------------------------------------------------------/


def oneOf (cs: String) : Parser Char :=
  satisfy fun c => Option.isSome (cs.toList.find? (· == c))
def noneOf (cs: String) : Parser Char :=
  satisfy fun c => Option.isNone (cs.toList.find? (· == c))
/- Parse one whitespace character -/
def consumeWs : Parser Char := oneOf " \n▸→"
def sepBy1 {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep >>= fun _ => p)
  pure (first :: rest.toList)
def sepBy {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  tryCatch (sepBy1 p sep) (fun a => pure a) (fun _ => pure [])
def endBy1 {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  let first ← p
  let rest ← tryCatch (many1 consumeWs)
                      (fun _ => many (do
                        let r ← p
                        let _ ← sep
                        pure r))
                      (fun _ => pure #[])
  pure (first :: rest.toList)
def endBy {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  tryCatch (endBy1 p sep) (fun a => pure a) (fun _ => pure [])

/- Parser a legal Scheme identifier symbol -/
def symbol : Parser Char := oneOf "!#$%&|*+-/:<=>?@^_~"
/- Parse any whitespace followed by a symbol -/
def wsSymbol : Parser Char :=
  many1 consumeWs >>= fun _ => symbol
  /- let _ ← ws  -- note: `many1 ws` loops infinitely since `ws` skips and always succeeds -/

def parseSpaceChar : Parser Char := do
  pstring "#\\space" >>= fun _ => pure ' '
def parseNewlineChar : Parser Char := do
  pstring "#\\newline" >>= fun _ => pure '\n'
def parseOtherChar : Parser Char := do
  pstring "#\\" >>= fun _ => asciiLetter
/- Parse a character literal, e.g. #\a or #\space -/
def parseChar : Parser LispVal := do
  let c ← parseSpaceChar <|> parseNewlineChar <|> parseOtherChar
  pure $ LispVal.char c

/- Parser a string literal; escaped quotes are supported -/
def parseString : Parser LispVal := do
  let _ ← satisfy (· == '"')
  let nonQuote := satisfy (· != '"')
  let escQuote := do
    let _ ← pchar '\\'
    let q ← pchar '"'
    pure q
  let innerStr : Parser Char := nonQuote <|> escQuote
  let s ← many innerStr
  let _ ← satisfy (· == '"')
  pure (LispVal.string (String.mk (s.toList)))

/- Parse a LispVal atom -/
def parseAtom : Parser LispVal := do
  let first ← asciiLetter.orElse fun () => symbol
  /- let rest ← many (asciiLetter.orElse fun () => (digit.orElse fun () => symbol)) -/
  let rest ← many (asciiLetter <|> digit <|> symbol)
  let cs := first :: rest.toList
  let atom := match String.mk cs with
    | "#t" => LispVal.bool true
    | "#f" => LispVal.bool false
    | s => LispVal.atom s
  pure atom

/- Parse a Lisp number which must be a Nat, negative integers are (- n) -/
def parseNumber : Parser LispVal := do
  let digitArray ← many digit
  match String.toNat? ∘ String.mk ∘ Array.toList $ digitArray with
  | some n => pure (LispVal.number n)
  | none => fail "could not parse a number"

def parseExpr : Parser LispVal := parseChar <|> parseAtom <|> parseString <|> parseNumber

def parseList : Parser LispVal := do
  let _ ← pchar '('
  let seq ← sepBy parseExpr consumeWs
  let _ ← pchar ')'
  pure (LispVal.list seq)

def parseDottedList : Parser LispVal := do
  let _ ← pchar '('
  let first ← endBy parseExpr consumeWs
  let _ ← pchar '.'
  let _ ← many1 consumeWs
  let rest ← parseExpr
  pure (LispVal.dottedList first rest)


/- Simple parser tests -/
#guard (Parser.run parseExpr "#\\a").isOk     -- matches char 'a'
#guard (Parser.run parseExpr "#\\space").isOk -- matches char ' '
#guard (Parser.run parseExpr "a").isOk        -- matches atom a
#guard (Parser.run parseExpr "!x").isOk       -- matches atom !x
#guard (Parser.run parseExpr "6!x").isOk      -- matches number 6
#guard !(Parser.run parseExpr " 6!x").isOk    -- doesn't match leading ws
#guard (Parser.run parseExpr "\"foo\"").isOk  -- matches string "foo"
#guard (Parser.run (sepBy1 parseExpr (many1 consumeWs)) "6 7  8").isOk
#guard (Parser.run (sepBy parseExpr (many1 consumeWs)) "6  7 8").isOk
#guard (Parser.run (endBy1 parseExpr (many1 consumeWs)) "6 7 8  ").isOk
#guard (Parser.run parseList "(6 7 8)").isOk
-- #guard (Parser.run parseList "(  6 7 8 )").isOk  -- not currently parseable
#guard (Parser.run parseList "()").isOk
#guard (Parser.run parseDottedList "(. 9)").isOk
#guard (Parser.run parseDottedList "(6 7 8 . 9)").isOk

/- Run a parser on the input, report on matches -/
def readExpr : String → String := fun input =>
  let result := Parser.run parseExpr input
  match result with
  | Except.ok _ => s!"Found value! (can't yet be printed)"
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



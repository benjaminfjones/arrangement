import Arrangement.Ast
import Arrangement.Error
import Std.Internal.Parsec

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/------------------------------------------------------------------------
 Parsing stuff
 ------------------------------------------------------------------------/


def oneOf (cs: String) : Parser Char :=
  satisfy fun c => Option.isSome (cs.toList.find? (· == c))
def noneOf (cs: String) : Parser Char :=
  satisfy fun c => Option.isNone (cs.toList.find? (· == c))
/-- Parse one whitespace character, consuming it -/
def consumeWs : Parser Char := oneOf " \n▸→"
/-- Parse at least one item separated by `sep` -/
def sepBy1 {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep >>= fun _ => p)
  pure (first :: rest.toList)
/-- Parse zero or more items separated by `sep`. Note: `tryCatch` doesn't comsume on failure. -/
def sepBy {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  tryCatch (sepBy1 p sep) (fun a => pure a) (fun _ => pure [])
/-- Parse one or more items with trailing separator `sep`, e.g. `a, b, c,` -/
def endBy1 {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  let first ← p
  let rest ← tryCatch (many1 consumeWs)  -- TODO: consuming WS shouldn't be needed here
                      (fun _ => many (do
                        let r ← p
                        let _ ← sep
                        pure r))
                      (fun _ => pure #[])
  pure (first :: rest.toList)
/-- Parse zero or more items with trailing separator. -/
def endBy {α β: Type} (p: Parser α) (sep: Parser β) : Parser (List α) := do
  tryCatch (endBy1 p sep) (fun a => pure a) (fun _ => pure [])

/- Parse a legal Scheme identifier symbol -/
def symbol : Parser Char := oneOf "!#$%&|*+-/:<=>?@^_~"
/- Parse whitespace followed by a symbol -/
def wsSymbol : Parser Char :=
  many1 consumeWs >>= fun _ => symbol
  -- note: `many1 ws` loops infinitely since `ws` skips and always succeeds

/-- Parse the special '#\space' character -/
def parseSpaceChar : Parser Char := do
  pstring "#\\space" >>= fun _ => pure ' '
/-- Parse the special '#\newline character -/
def parseNewlineChar : Parser Char := do
  pstring "#\\newline" >>= fun _ => pure '\n'
/-- Parse an ascii letter character -/
def parseOtherChar : Parser Char := do
  pstring "#\\" >>= fun _ => asciiLetter
/-- Parse a character literal, e.g. #\a or #\space -/
def parseChar : Parser LispVal := do
  let c ← parseSpaceChar <|> parseNewlineChar <|> parseOtherChar
  pure $ LispVal.char c

/-- Parse a string literal; escaped quotes are supported. -/
def parseString : Parser LispVal := do
  let nonQuote := satisfy (· != '"')
  let escQuote := do  -- parser of escaped quotes
    let _ ← pchar '\\'
    let q ← pchar '"'
    pure q
  let innerStr : Parser Char := nonQuote <|> escQuote  -- parses legal characters strictly inside a string
  -- do the parsing
  let _ ← satisfy (· == '"')
  let s ← many innerStr
  let _ ← satisfy (· == '"')
  pure (LispVal.string (String.mk (s.toList)))

/-- Parse a LispVal atom -/
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

/-- Parse a Lisp number which must be a Nat, negative integers are (- n) -/
def parseNumber : Parser LispVal := do
  let digitArray ← many digit
  match String.toNat? ∘ String.mk ∘ Array.toList $ digitArray with
  | some n => pure (LispVal.number n)
  | none => fail "could not parse a number"

mutual
/-- Parse a list w/o parentheses -/
partial def parseList : Parser LispVal := do
  let seq ← sepBy parseExpr consumeWs
  pure (LispVal.list seq)

/-- Parse a dotted list w/o parentheses -/
partial def parseDottedList : Parser LispVal := do
  let first ← endBy parseExpr consumeWs
  let _ ← pchar '.'
  let _ ← many1 consumeWs
  let rest ← parseExpr
  pure (LispVal.dottedList first rest)

/-- Quote: `'foo` is equivalent to `(quote foo)` -/
partial def parseQuoted : Parser LispVal := do
  let _ ← pchar '\''
  let e ← parseExpr
  pure (LispVal.list [LispVal.atom "quote", e])

/-- Quasiquote: ``foo` is equivalent to `(quasiquote foo)` -/
partial def parseQuasiquoted : Parser LispVal := do
  let _ ← pchar '`'
  let e ← parseExpr
  pure (LispVal.list [LispVal.atom "quasiquote", e])

/-- Unquote: `,foo` is equivalent to `(unquote foo)` -/
partial def parseUnquote : Parser LispVal := do
  let _ ← pchar ','
  let e ← parseExpr
  pure (LispVal.list [LispVal.atom "unquote", e])

/-- Unquote Splicing: `,@foo` is equivalent to `(unquote-splicing foo)` -/
partial def parseUnquoteSplicing : Parser LispVal := do
  let _ ← pstring ",@"
  let e ← parseExpr
  pure (LispVal.list [LispVal.atom "unquote-splicing", e])

/-- Finally, parse a general Lisp expression -/
partial def parseExpr : Parser LispVal :=  parseChar
                               <|> parseAtom
                               <|> parseString
                               <|> parseNumber
                               <|> parseQuoted
                               <|> parseQuasiquoted
                               <|> parseUnquoteSplicing  -- must take precedence over Unquote
                               <|> parseUnquote
                               <|> do
                                   let _ ← pchar '('
                                   let r ← (attempt parseList) <|> parseDottedList
                                   let _ ← pchar ')'
                                   pure r
end  -- mutual


------------------------------------------------------------------------
-- Parsing tests
------------------------------------------------------------------------

def testParseToRepr : String → String := fun s =>
  match Parser.run parseExpr s with
  | Except.ok l => reprStr l
  | Except.error e => panic! s!"could not parse: {e}"

/- Chars -/
#guard testParseToRepr "#\\a" == "LispVal.char 'a'"
#guard (Parser.run parseExpr "#\\a").isOk     -- matches char 'a'
#guard (Parser.run parseExpr "#\\space").isOk -- matches char ' '

/- Atoms -/
#guard (Parser.run parseExpr "a").isOk        -- matches atom a
#guard (Parser.run parseExpr "!x").isOk       -- matches atom !x
#guard ¬ (Parser.run parseExpr " 6!x").isOk    -- doesn't match leading ws
#guard (Parser.run parseExpr "6!x").isOk      -- matches number 6

/- Strings -/
#guard (Parser.run parseExpr "\"bob\"").isOk  -- matches string "bob"
#guard ¬ (Parser.run parseExpr "\"bob").isOk  -- missing end quote
#guard (Parser.run parseExpr "\"fo\\\"o\"").isOk  -- matches string "fo\"o"

/- Lists -/
#guard (Parser.run (sepBy1 parseExpr (many1 consumeWs)) "6 7  8").isOk
#guard (Parser.run (sepBy parseExpr (many1 consumeWs)) "6  7 8").isOk
#guard (Parser.run (endBy1 parseExpr (many1 consumeWs)) "6 7 8  ").isOk
-- #guard (Parser.run parseList "  6 7 8 ").isOk  -- not currently parseable due to whitespace
#guard (Parser.run parseList "a 9").isOk
#guard (Parser.run parseDottedList "a . 9").isOk
#guard (Parser.run parseExpr "(6 7 8)").isOk
#guard (Parser.run parseExpr "()").isOk  -- Exxcept.ok (LispVal.list [])
#guard (Parser.run parseExpr "(a . 9)").isOk
#guard (Parser.run parseExpr "(6 7 8 . 9)").isOk

/- Quotation/Quasiquotation -/
#guard testParseToRepr "'onion" == "LispVal.list [LispVal.atom \"quote\", LispVal.atom \"onion\"]"
#guard testParseToRepr "`pepper" == "LispVal.list [LispVal.atom \"quasiquote\", LispVal.atom \"pepper\"]"
#guard testParseToRepr ",chile" == "LispVal.list [LispVal.atom \"unquote\", LispVal.atom \"chile\"]"
#guard testParseToRepr ",@oil" == "LispVal.list [LispVal.atom \"unquote-splicing\", LispVal.atom \"oil\"]"

/- Larger expressions -/
#guard (Parser.run parseExpr "(a test)").isOk
#guard (Parser.run parseExpr "(a (nested) test)").isOk
#guard (Parser.run parseExpr "(a (dotted . list) test)").isOk
#guard (Parser.run parseExpr "(a '(quoted (dotted . list)) test)").isOk
#guard (Parser.run parseExpr "(a `(quasiquoted (dotted . list)) test)").isOk
#guard ¬ (Parser.run parseExpr "(a '(imbalanced parens)").isOk


/------------------------------------------------------------------------
 Parser execution
 ------------------------------------------------------------------------/

/- Run a parser on the input, report on matches -/
def readExpr : String → ThrowsError LispVal := fun input =>
  let result := Parser.run parseExpr input
  match result with
  | Except.ok l => pure l
  | Except.error e => throwError (LispError.parser e)



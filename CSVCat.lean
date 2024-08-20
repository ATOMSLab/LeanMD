import Lean.Data.Parsec

open Lean Parsec

/-- CSV Parser Definitions -/
abbrev Field_CSV := String
abbrev Record := Array Field_CSV
abbrev Csv := Array Record

/-- Parser: Parsing a comma-separated value -/
def comma : Parsec Char := pchar ','

/-- Parser: Parsing a newline (CRLF, LF, or CR) -/
def crlf : Parsec String := pstring "\r\n" <|> pstring "\n" <|> pstring "\r"

/-- `textData` matches characters that are part of the field, including negative signs, digits, and decimals. -/
def textData : Parsec Char := satisfy fun c =>
  c.isDigit || c == '.' || c == '-' || c == 'e' || c == 'E'

/-- `cr`, `lf`, and `crlf` are parsers for carriage return, line feed, and their combination.-/
def cr : Parsec Char := pchar '\r'   -- Carriage Return (used in older Mac systems)-/
def lf : Parsec Char := pchar '\n'   -- Line Feed (used in Unix/Linux and modern Mac systems)-/


/-- `dQUOTE` matches a double quote character, which is used to escape fields in a Csv file.-/
def dQUOTE : Parsec Char := pchar '\"'

/-- `twoDQUOTE` matches two consecutive double quotes `""`, which represent an escaped double quote within a quoted field.-/
def twoDQUOTE  : Parsec Char := attempt (pchar '"' *> pchar '"')

/-- `escaped` matches fields surrounded by double quotes.
-- It allows for more complex data inside the field, such as commas and newlines.-/
def escaped : Parsec String := attempt
  dQUOTE *>   -- Start with an opening double quote
  manyChars (textData <|> comma <|> cr <|> lf <|> twoDQUOTE) -- Allow special characters
  <* dQUOTE  -- End with a closing double quote

/-- `nonEscaped` is for fields that are not enclosed in double quotes.
  It matches a series of valid characters that do not include special characters like commas or newlines.-/
def nonEscaped: Parsec String := manyChars textData

/-- `field` is a parser that can handle both escaped and non-escaped fields.-
    It uses the `escaped` parser first and if that fails, it tries `nonEscaped`.-/
def field : Parsec Field_CSV := escaped <|> nonEscaped

/--
  `manySep` is a higher-order parser that matches many occurrences of a pattern `p`
  separated by a separator `s`.
  For example, in a CSV file, fields are separated by commas.
  This function returns an array of parsed elements.
-/
def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

/-- `record` parses a single row of CSV, which is a sequence of fields separated by commas.-/
def record : Parsec Record := manySep field comma

/-- `file` parses the entire CSV file, which consists of multiple records separated by newlines.-/
def file : Parsec $ Array Record :=
  manySep record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

/-- `parse` is a function that takes a string (the content of a CSV file) and returns either
    the parsed data successfully or an error message.-/
def parse (s : String) : Except String $ Array $ Array $ String :=
  match file s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res  -- Return the result if successful
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"  -- Return an error message

-- e.g., let's parse a CSV string directly.

#eval parse ("1.0771699,-1.0209881,-1.3482594\n0.1830885,-1.5576982,-1.7824055\n-2.0603462,3.9273783,3.8895551")

/--
  `manyHomoCore` is a parser that ensures all parsed arrays have the same size.
  This is useful for validating that every row in a CSV file has the same number of fields,
  which is often a requirement for properly formatted CSV files.
-/
partial def manyHomoCore (p : Parsec $ Array α) (acc : Array $ Array α) : Parsec $ Array $ Array α :=
  (do
    let first ← p
    if acc.size = 0 then
      manyHomoCore p (acc.push first)  -- If it's the first element, it just adds it
    else
      if acc.back.size = first.size then
        manyHomoCore p (acc.push first)  -- If the sizes match, parsing continues
      else
        fail "expect same size"  -- If sizes don't match, error thrown
  )
  <|> pure acc  -- If parsing fails, it returns the accumulated result

/--
  `manySepHomo` parses many arrays of `p` with the same size separated by `s`.
  It is used to parse a CSV file while making sure that all rows have the same number of fields ensuring uniformity.
-/
def manySepHomo (p : Parsec $ Array α) (s : Parsec β) : Parsec $  Array $ Array α := do
  manyHomoCore (attempt (s *> p)) #[←p]

/-- `file'` is an alternative CSV file parser most likely.
    It ensures each row has the same number of fields.-/
def file' : Parsec $ Array Record := manySepHomo record (crlf <* notFollowedBy eof) <* (optional crlf) <* eof

/-- `parse'` is a function that parses a string with an additional check for homogeneous field counts across records.-/
def parse' (s : String) : Except String $ Array $ Array $ String :=
  match file' s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res  -- Return the result if successful
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"  -- Return an error message

/-This is by me, John Velkey.-/
  /-John's function to handle exceptions -/
/-- This function handles the result of the CSV parsing and returns either the parsed data or an error message.
    If parsing fails, it returns a default error message.-/
def CSVParseExceptHandler (inputParse : Except String (Array (Array String))) : Array $ Array $ String :=
  match inputParse with
  | Except.ok α => α   -- If parsing is successful, return the result
  | Except.error _ => #[#["CSV Parse Error"]]  -- If there's an error, return a default error message


def CSVParseIt : IO Unit := do
  -- Read through of the CSV file
  let fileContent ← IO.FS.readFile "data_for_LJC.csv"

  -- Parse the file using the parse function
  let parsedCSV := parse fileContent

  -- Handles the result using the CSVParseExceptHandler function
  let result := CSVParseExceptHandler parsedCSV

  IO.println result

#eval CSVParseIt

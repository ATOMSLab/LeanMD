/-
Authors: Ejike Ugwuanyi
-/

import Lean

open Lean Parsec IO

/-!
  ## CSV-like data parser (comma-separated floats)
  The CSV parser reads a file of comma-separated floats, parsing each line into a list of floats. It outputs these 
  lines as a list of lists, allowing easy access to each row's numerical data.
-/

/-- Custom `sepBy` function to parse a list of `p` separated by `sep`. -/
def sepBy (p : Parsec α) (sep : Parsec Unit) : Parsec (List α) := do
  let first ← p -- Parse the first item
  let rest ← many (sep *> p) -- Parse the rest, if any
  return first :: rest.toList -- Convert `Array` to `List` and return

/-- Helper function to convert a string representing an integer to a Nat. -/
def stringToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Helper function to convert a string representing a fractional part to a Float. -/
def stringToFrac (s : String) : Float :=
  s.foldr (fun c acc => (acc + (c.toNat.toFloat - '0'.toNat.toFloat)) / 10.0) 0.0

/-- Helper function to convert a string representing an integer to a Float. -/
def stringToFloat (intPart : String) (fracPart : String) (expPart : String) (sign : Float) (expSign : Int) : Float :=
  let intVal := (stringToNat intPart).toFloat -- Convert integer part to Float
  let fracVal := stringToFrac fracPart -- Convert fractional part to Float
  let baseVal := sign * (intVal + fracVal) -- Combine integer and fractional part
  let expVal := if expPart.isEmpty then 1.0 else Float.pow 10.0 (Float.ofInt (expSign * stringToNat expPart)) -- Handle exponent part
  baseVal * expVal

/-- A custom float parser to handle basic float formats and scientific notation. -/
def float : Parsec Float := do
  let sign ← (pchar '-' *> pure (-1.0)) <|> pure 1.0 -- Handle optional negative sign
  let intPart ← manyChars (satisfy Char.isDigit) -- Digits before the decimal point
  let fracPart ← (pchar '.' *> manyChars (satisfy Char.isDigit)) <|> pure "" -- Digits after the decimal point
  let exponent ← optional (pchar 'e' <|> pchar 'E') -- Optional exponent part
  let expSign ← match exponent with
    | some _ => (pchar '-' *> pure (-1)) <|> (pchar '+' *> pure 1) <|> pure 1
    | none => pure 1
  let expDigits ← match exponent with
    | some _ => manyChars (satisfy Char.isDigit)
    | none => pure ""
  let floatValue := stringToFloat intPart fracPart expDigits sign expSign
  return floatValue

/-- Parser for a line of floats separated by commas. -/
def floatLine : Parsec (List Float) := sepBy float (pchar ',' *> pure ())

/-- Parse a single CSV line into a list of floats. -/
def parseLine (line : String) : Except String (List Float) :=
  match floatLine line.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it _  => Except.error s!"offset {it.i.byteIdx}: error parsing line"

/-- Parse the entire CSV content as multiple lines of floats. -/
def parseCSV (lines : Array String) : Except String (List (List Float)) :=
  let results := lines.foldl (fun acc line =>
    match parseLine line with
    | Except.ok floats => floats :: acc
    | Except.error _ => acc) [] -- Skip erroneous lines
  Except.ok results.reverse

/-- Read the CSV file line by line and parse it. -/
def main : IO Unit := do
  let input ← IO.FS.readFile "csv file path"
  let lines := input.splitOn "\n" |>.toArray -- Convert List to Array
  match parseCSV lines with
  | Except.ok res => IO.println s!"{res}"
  | Except.error err => IO.eprintln s!"Error: {err}"

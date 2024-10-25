/-
Author: Ejike Ugwuanyi
-/

import Lean

open Lean Parsec IO

/-!
  ## CSV-like data parser (comma-separated floats)
  Parses each line into a 3-dimensional vector (`Vec3`) and displays it in the format ⟨x, y, z⟩.
-/

/-- Define a structure for 3D vectors. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float

/-- Custom `ToString` for `Vec3` to match ⟨x, y, z⟩ format. -/
instance : ToString Vec3 where
  toString v := s!"⟨{v.x}, {v.y}, {v.z}⟩"

/-- Custom `ToString` for `List Vec3` to print as a list of `Vec3`. -/
instance : ToString (List Vec3) where
  toString vs := "[" ++ String.intercalate ", " (vs.map toString) ++ "]"

/-- Custom `sepBy` function to parse a list of `p` separated by `sep`. -/
def sepBy (p : Parsec α) (sep : Parsec Unit) : Parsec (List α) := do
  let first ← p
  let rest ← many (sep *> p)
  return first :: rest.toList

/-- Helper function to convert a string representing an integer to a Nat. -/
def stringToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Helper function to convert a string representing a fractional part to a Float. -/
def stringToFrac (s : String) : Float :=
  s.foldr (fun c acc => (acc + (c.toNat.toFloat - '0'.toNat.toFloat)) / 10.0) 0.0

/-- Helper function to convert a string representing an integer to a Float. -/
def stringToFloat (intPart : String) (fracPart : String) (expPart : String) (sign : Float) (expSign : Int) : Float :=
  let intVal := (stringToNat intPart).toFloat
  let fracVal := stringToFrac fracPart
  let baseVal := sign * (intVal + fracVal)
  let expVal := if expPart.isEmpty then 1.0 else Float.pow 10.0 (Float.ofInt (expSign * stringToNat expPart))
  baseVal * expVal

/-- A custom float parser to handle basic float formats and scientific notation. -/
def float : Parsec Float := do
  let sign ← (pchar '-' *> pure (-1.0)) <|> pure 1.0
  let intPart ← manyChars (satisfy Char.isDigit)
  let fracPart ← (pchar '.' *> manyChars (satisfy Char.isDigit)) <|> pure ""
  let exponent ← optional (pchar 'e' <|> pchar 'E')
  let expSign ← match exponent with
    | some _ => (pchar '-' *> pure (-1)) <|> (pchar '+' *> pure 1) <|> pure 1
    | none => pure 1
  let expDigits ← match exponent with
    | some _ => manyChars (satisfy Char.isDigit)
    | none => pure ""
  let floatValue := stringToFloat intPart fracPart expDigits sign expSign
  return floatValue

/-- Parser for a line of floats separated by commas. It expects exactly 3 floats for a `Vec3`. -/
def floatLineToVec3 : Parsec Vec3 := do
  let floats ← sepBy float (pchar ',' *> pure ())
  if floats.length == 3 then
    match floats with
    | [x, y, z] => return { x := x, y := y, z := z }
    | _ => fail "Unexpected error while creating Vec3"
  else
    fail "Expected exactly 3 floats per line"

/-- Parse a single CSV line into a `Vec3`. -/
def parseLineToVec3 (line : String) : Except String Vec3 :=
  match floatLineToVec3 line.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it _ => Except.error s!"offset {it.i.byteIdx}: error parsing line"

/-- Parse the entire CSV content as multiple lines of `Vec3`. -/
def parseCSVToVec3s (lines : Array String) : Except String (List Vec3) :=
  let results := lines.foldl (fun acc line =>
    match parseLineToVec3 line with
    | Except.ok vec => vec :: acc
    | Except.error _ => acc) []
  Except.ok results.reverse

/-- Read the CSV file line by line and parse it into `List Vec3`. -/
def main : IO Unit := do
  let input ← IO.FS.readFile "csv file path"
  let lines := input.splitOn "\n" |>.toArray
  match parseCSVToVec3s lines with
  | Except.ok res => IO.println s!"{res}"
  | Except.error err => IO.eprintln s!"Error: {err}"

/- Author: Ejike Ugwuanyi -/

import Lean
open Lean Parsec IO

/-!
  ## CSV-like data parser (comma-separated floats)
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

def simpleFloatParser (input : String) : Option Float :=
  let trimmed := input.trim
  if trimmed.isEmpty then none
  else
    let (sign, rest) :=
      if trimmed.get 0 == '-' then (-1.0, trimmed.drop 1)
      else (1.0, trimmed)

    let parts := rest.splitOn "."
    match parts with
    | [wholePart] =>
      match wholePart.toNat? with
      | some n => some (sign * Float.ofNat n)
      | none => none
    | [wholePart, fractionalPart] =>
      match wholePart.toNat?, fractionalPart.toNat? with
      | some w, some f =>
        let fracValue := (Float.ofNat f) / Float.pow 10.0 fractionalPart.length.toFloat
        some (sign * (Float.ofNat w + fracValue))
      | _, _ => none
    | _ => none


-- Helper function to safely convert a string to a float with a default value
def safeToFloat (input : String) (default : Float) : Float :=
  match simpleFloatParser input with
  | some f => f
  | none => default

-- Function to parse a list of floats from a comma-separated string
def parseListFloat (input : String) : List Float :=
  input.splitOn "," |>.map (fun s => safeToFloat s 1.0)

-- Functions to perform element-wise operations on lists of floats
def ListDiv (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h / L2h) :: (ListDiv L1t L2t)
  | _, _ => []

def ListProd (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h * L2h) :: (ListProd L1t L2t)
  | _, _ => []

def listSub (L1 : List Float) (L2 : List Float) : List Float :=
  match L1, L2 with
  | [], [] => []
  | L1h :: L1t, L2h :: L2t => (L1h - L2h) :: (listSub L1t L2t)
  | _, _ => []

/-- Function to apply periodic boundary conditions (PBC) -/
def apply_pbc (position : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv position cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  listSub position prod_result

/-- Minimum image distance calculation -/
def minimum_image_distance (r_ij : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv r_ij cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  listSub r_ij prod_result

/-- Calculate the norm of a vector -/
def vectorNorm (vector : List Float) : Float :=
  (vector.foldr (λ x acc => x ^ 2 + acc) 0.0).sqrt

/-- Lennard-Jones potential function -/
def lennard_jones_potential (r : Float) (cutoff : Float) (epsilon : Float) (sigma : Float) : Float :=
  if r ≤ cutoff then
    let r6 := (sigma / r) ^ 6
    let r12 := r6 * r6
    4 * epsilon * (r12 - r6)
  else
    0.0

/-- Compute the total energy of the system -/
def compute_energy (positions : List (List Float)) (cell_length : List Float) (cutoff epsilon sigma : Float) : Float :=
  let num_atoms := positions.length
  let rec energy (i : Nat) (j : Nat) (accumulated_energy : Float) : Float :=
    if i = 0 then
      accumulated_energy
    else if j = 0 then
      energy (i - 1) (i - 2) accumulated_energy
    else
      let r_ij := listSub (positions[i - 1]!) (positions[j - 1]!)
      let r_ij1 := apply_pbc r_ij cell_length
      let r_ij2 := minimum_image_distance r_ij1 cell_length
      let distance := vectorNorm r_ij2
      let energy_contrib := lennard_jones_potential distance cutoff epsilon sigma
      energy i (j - 1) (accumulated_energy + energy_contrib)
  energy num_atoms (num_atoms - 1) 0.0

/-- Main function to run the program -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "Enter the number of particles (ignored if positions are predefined):"
  let _ ← stdin.getLine

  stdout.putStrLn "Enter the cell length as comma-separated values (e.g., 10.0,10.0,10.0):"
  let cellLengthStr ← stdin.getLine
  let cell_length := parseListFloat cellLengthStr

  stdout.putStrLn "Enter the cutoff value:"
  let cutoffStr ← stdin.getLine
  let cutoff := safeToFloat cutoffStr 3.0

  stdout.putStrLn "Enter epsilon value:"
  let epsilonStr ← stdin.getLine
  let epsilon := safeToFloat epsilonStr 1.0

  stdout.putStrLn "Enter sigma value:"
  let sigmaStr ← stdin.getLine
  let sigma := safeToFloat sigmaStr 1.0

  stdout.putStrLn "Enter units of distance:"
  let _ ← stdin.getLine

  stdout.putStrLn "Enter units of cell length:"
  let _ ← stdin.getLine

  stdout.putStrLn "Enter units of sigma:"
  let _ ← stdin.getLine

  -- Read the CSV file to get the positions
  stdout.putStrLn "Reading positions from the CSV file..."
  let input ← IO.FS.readFile "csv file path" -- Update with actual path to CSV
  let lines := input.splitOn "\n" |>.toArray -- Convert List to Array
  let positions ← match parseCSV lines with
    | Except.ok res => pure res
    | Except.error err => do stdout.putStrLn s!"Error parsing positions: {err}"; pure []

  -- Check if positions were parsed successfully
  if positions.isEmpty then
    stdout.putStrLn "No valid positions parsed. Exiting program."
  else
    -- Compute and display the total energy
    let totalEnergy := compute_energy positions cell_length cutoff epsilon sigma
    stdout.putStrLn s!"The total internal energy is: {totalEnergy}"

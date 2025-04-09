import Lean.Data.Parsec

open Lean Parsec

/-- Define a CSV field as a string -/
abbrev Field_CSV := String

/-- Define a record (row) in the CSV as an array of fields -/
abbrev Record := Array Field_CSV

/-- Define a CSV file as an array of records -/
abbrev Csv := Array Record

/-- Parser to match a comma-separated value -/
def comma : Parsec Char := pchar ','

/-- Parser to match a newline (CRLF, LF, or CR) -/
def crlf : Parsec String := pstring "\r\n" <|> pstring "\n" <|> pstring "\r"

/-- Parser to match the data within a field, including negative signs, digits, and decimals -/
def textData : Parsec Char := satisfy fun c =>
  c.isDigit || c == '.' || c == '-' || c == 'e' || c == 'E'

/-- Parser for non-escaped fields (i.e., fields without quotes) -/
def nonEscaped : Parsec String := manyChars textData

/-- Parser for a field, assuming all fields are non-escaped for simplicity -/
def field : Parsec Field_CSV := nonEscaped

/-- Parser for a record (row) of fields separated by commas -/
def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

def record : Parsec Record := manySep field comma

/-- Parser for the entire CSV file consisting of multiple records separated by newlines -/
def file : Parsec Csv := manySep record crlf

/-- Function to parse a CSV string into a structured data format -/
def parse (s : String) : Except String Csv :=
  match file s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.byteIdx}: {err}"

def float_parsing (str: String) : Option Float :=
  let parts := str.split (· == '.')
  match parts with
  | [intPart, fracPart] =>
    let fullnum := (intPart ++ fracPart).toNat!
    let plc := fracPart
    some (Float.ofScientific fullnum true plc.length)
  | _ => none

/-- Convert a parsed CSV to a list of lists of floats -/
def parseCsvToFloatLists (csvContent : String) : Option (List (List Float)) :=
  match parse csvContent with
  | Except.ok rows =>
    some (rows.toList.map (fun row =>
      row.toList.map (fun field =>
        match float_parsing field with
        | some f => f
        | none   => 0.0
      )))
  | Except.error _ => none


set_option maxHeartbeats 10000000

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

def apply_pbc (position : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv position cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  listSub position prod_result


def minimum_image_distance (r_ij : List Float) (cell_length : List Float) : List Float :=
  let div_result := ListDiv r_ij cell_length
  let round_result := div_result.map (λ x => Float.round x)
  let prod_result := ListProd cell_length round_result
  let result := listSub r_ij prod_result
  result

def vectorNorm (vector : List Float) : Float :=
  (vector.foldr (λ x acc => x ^ 2 + acc) 0.0).sqrt

def lennard_jones_potential (r : Float) (cutoff : Float) : Float :=
  if r < cutoff then
    let epsilon := 1.0
    let sigma := 1.0
    let r6 := (sigma / r) ^ 6
    let r12 := r6 * r6
    4 * epsilon * (r12 - r6)
  else
    0.0

def energy (positions : List (List Float)) (cell_length : List Float) (cutoff : Float) (i j : Nat) (accumulated_energy : Float) : Float :=
  if i = 0 then
    accumulated_energy
  else if j = 0 then
    energy positions cell_length cutoff (i - 1) (i - 2) accumulated_energy
  else
    let r_ij := listSub (positions[i - 1]!) (positions[j - 1]!)
    let r_ij1 := apply_pbc r_ij cell_length
    let r_ij2 := minimum_image_distance r_ij1 cell_length
    let distance := vectorNorm r_ij2
    let energy_contrib := lennard_jones_potential distance cutoff
    energy positions cell_length cutoff i (j - 1) (accumulated_energy + energy_contrib)

def compute_energy (positions : List (List Float)) (cell_length : List Float) (cutoff : Float := 3.0) : Float :=
  let num_atoms := positions.length
  energy positions cell_length cutoff num_atoms (num_atoms - 1) 0.0

def positions : IO (List (List Float)) := do
  let fileContent ← IO.FS.readFile "data_for_LJC.csv"
  match parseCsvToFloatLists fileContent with
  | some pos => return pos
  | none     => return []


def cell_length : List Float := [8.0, 8.0, 8.0]

def goal : IO Unit := do
  let position ← positions
  IO.println position
  let energy := compute_energy position cell_length
  IO.println s!"Total Energy: {energy}"

#eval goal

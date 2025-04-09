import Lean

/-!
  ## 1. Float Parsing
  A small parser that converts a string to a Float.
-/
def parseFloat? (s : String) : Option Float := Id.run do
  let s := s.trim
  if s.isEmpty then
    return none

  -- Check for a leading negative sign
  let isNeg := s.startsWith "-"
  let s := if isNeg then s.drop 1 else s

  if s.isEmpty then
    return none

  let parts := s.splitOn "."
  match parts with
  | [intStr] =>
    match intStr.toNat? with
    | some intVal =>
      let val := intVal.toFloat
      return if isNeg then some (-val) else some val
    | none => return none

  | [intStr, fracStr] =>
    if intStr.isEmpty && fracStr.isEmpty then
      return none
    let intVal := (intStr.toNat?).getD 0
    let fracVal := (fracStr.toNat?).getD 0
    let fracPow := 10.0 ^ (fracStr.length.toFloat)
    let val := intVal.toFloat + (fracVal.toFloat / fracPow)
    return if isNeg then some (-val) else some val

  | _ => return none

/-- Convert a string to a Float, returning 0.0 if parse fails. -/
def stringToFloat (s : String) : Float :=
  match parseFloat? s with
  | some f => f
  | none   => 0.0


/-!
  ## 2. CSV Parsing for (Fin 3 → Float)
-/

/-- Parse one line of CSV (format: "x,y,z") into a (Fin 3 → Float). -/
def parseLineToFin3 (line : String) : Option (Fin 3 → Float) :=
  let parts := line.splitOn ","
  if parts.length < 3 then
    none
  else
    let xVal := stringToFloat parts[0]!
    let yVal := stringToFloat parts[1]!
    let zVal := stringToFloat parts[2]!
    some (fun i =>
      match i.val with
      | 0 => xVal
      | 1 => yVal
      | 2 => zVal
      | _ => 0.0)

/-- Parse an array of CSV lines into a list of (Fin 3 → Float). -/
def parseCSVToFin3 (lines : Array String) : List (Fin 3 → Float) :=
  let parsed := lines.foldl (fun acc line =>
    match parseLineToFin3 line with
    | some vec => vec :: acc
    | none     => acc
  ) []
  parsed.reverse


/-!
  ## 3. NIST Long-Range Correction
     U_LRC^* = (8π/3) ρ^* [ 1/(3 r_c^9) - 1/(r_c^3) ]

     where ρ^* = N / (Lx^* Ly^* Lz^*)
-/


def pi : Float := 3.141592653589793


/-- Compute the dimensionless tail correction U_LRC* from NIST. -/
def computeULRCStar
  (positions  : List (Fin 3 → Float))
  (boxLength  : Fin 3 → Float)
  (cutoffStar : Float)
: Float :=
  let n       := positions.length.toFloat
  let volume  := (boxLength ⟨0, by decide⟩)
                * (boxLength ⟨1, by decide⟩)
                * (boxLength ⟨2, by decide⟩)
  let rhoStar := n / volume
  (8.0 / 3.0) * pi * rhoStar *
    ( (1.0 / (3.0 * (cutoffStar ^ 9))) - (1.0 / (cutoffStar ^ 3)) )


/-!
  ## 4. Complete `main` Function
  Reads:
    - CSV path
    - dimensionless cutoff r_c^*
    - dimensionless box lengths
  Then computes U_LRC^* and prints it.
-/
def main : IO Unit := do
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin

  -- Prompt for CSV path
  stdout.putStrLn "Enter the path to the CSV file containing *dimensionless* positions:"
  let filePath ← stdin.getLine
  let filePath := filePath.trim

  -- Read file and parse positions
  let input ← IO.FS.readFile filePath
  let lines := input.splitOn "\n" |>.toArray
  let positions := parseCSVToFin3 lines
  if positions.isEmpty then
    stdout.putStrLn "Error: No valid positions found in the CSV file."
    return ()

  let n := positions.length
  stdout.putStrLn s!"Number of positions parsed: {n}"

  -- Prompt for dimensionless cutoff
  stdout.putStrLn "Enter the dimensionless cutoff r_c^* (e.g., 2.5):"
  let cutoffStr := (← stdin.getLine).trim
  let cutoffStar := stringToFloat cutoffStr

  -- Prompt for dimensionless box lengths
  stdout.putStrLn "Enter dimensionless box lengths Lx^*,Ly^*,Lz^* (comma-separated, e.g. 8.0,8.0,8.0):"
  let boxStr := (← stdin.getLine).splitOn ","
  if boxStr.length < 3 then
    stdout.putStrLn "Error: Not enough box-length entries!"
    return ()

  let Lx := stringToFloat boxStr[0]!
  let Ly := stringToFloat boxStr[1]!
  let Lz := stringToFloat boxStr[2]!

  -- Construct box length function
  let boxLength : Fin 3 → Float := fun i =>
    match i.val with
    | 0 => Lx
    | 1 => Ly
    | 2 => Lz
    | _ => 0.0

  -- Compute U_LRC^*
  let n       := positions.length.toFloat
  let ULRCStar := n * computeULRCStar positions boxLength cutoffStar

  -- Output
  stdout.putStrLn ""
  stdout.putStrLn "==========================================="
  stdout.putStrLn s!"Dimensionless Lennard-Jones Tail Correction"
  stdout.putStrLn s!"U_LRC^* = {ULRCStar}"
  stdout.putStrLn "==========================================="

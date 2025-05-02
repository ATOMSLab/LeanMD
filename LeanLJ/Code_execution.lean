import Mathlib
import LeanLJ.CSVParser
import LeanLJ.Functions
import LeanLJ.Definitions
open LeanLJ

def main : IO Unit := do
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin

  stdout.putStrLn "Enter the path to the CSV file containing positions:"
  let filePath ← stdin.getLine
  let input ← IO.FS.readFile filePath.trim
  let lines := input.splitOn "\n" |>.toArray

  let positions := parseCSVToFin3 lines
  if positions.isEmpty then
    stdout.putStrLn "Error: No valid positions found in the CSV file."
  else
    let cutoff ← readSinglePositiveFloat "Enter the cutoff distance (e.g., 3.0):"
    let epsilon ← readSinglePositiveFloat "Enter epsilon value (e.g., 1.0):"
    let sigma ← readSinglePositiveFloat "Enter sigma value (e.g., 1.0):"
    let boxLength ← readBoxLength "Enter box length (comma-separated, e.g., 8.0,8.0,8.0):"
    let totalEnergy := computeTotalEnergy positions box_length cutoff epsilon sigma
    let numAtoms := positions.length

    let boxSide := boxLength ⟨0, by decide⟩
    let density := rho numAtoms.toFloat boxSide
    let Ulrc := numAtoms.toFloat * U_LRC density pi epsilon sigma cutoff

    stdout.putStrLn s!"The internal energy is: {totalEnergy}"

    match getNISTEnergy numAtoms with
    | some nist =>
        stdout.putStrLn s!"NIST reference internal energy: {nist}"
        let error := totalEnergy - nist
        stdout.putStrLn s!"Absolute error: {Float.abs error}"
    | none =>
        stdout.putStrLn s!"No NIST value found for {numAtoms} atoms."

    stdout.putStrLn ""


    stdout.putStrLn s!"The long range correction energy contribution is: {Ulrc}"

    match getNISTEnergy_LRC numAtoms with
    | some nist =>
        stdout.putStrLn s!"NIST reference long range correction: {nist}"
        let error := Ulrc - nist
        stdout.putStrLn s!"Absolute error: {Float.abs error}"
    | none =>
        stdout.putStrLn s!"No NIST value found for {numAtoms} atoms."

    stdout.putStrLn ""

    stdout.putStrLn s!"Number of atoms parsed: {numAtoms}"
    
    stdout.putStrLn s!"The total internal energy including long-range correction is: {totalEnergy + Ulrc}"



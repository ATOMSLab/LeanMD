import Mathlib
import Research.CSVParser
import Research.Functions
open Research


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
    let box_length ← readBoxLength "Enter box length (comma-separated, e.g., 8.0,8.0,8.0):"
    let totalEnergy := Research.compute_total_energy positions box_length cutoff epsilon sigma
    let numAtoms := positions.length
    stdout.putStrLn s!"The total internal energy is: {totalEnergy}"
    stdout.putStrLn s!"Number of atoms parsed: {numAtoms}"

    match getNISTEnergy numAtoms with
    | some nist =>
        stdout.putStrLn s!"NIST reference energy: {nist}"
        let error := totalEnergy - nist
        stdout.putStrLn s!"Absolute error: {Float.abs error}"
    | none =>
        stdout.putStrLn s!"No NIST value found for {numAtoms} atoms."


-- lake env lean Research/Code_execution.lean --run

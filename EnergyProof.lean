/-
Authors: Ejike Ugwuanyi
-/

import Mathlib

noncomputable def pbc (position box_length : ℝ) : ℝ :=
  position - box_length * round (position / box_length)

/-- Compute the “minimum-image” distance (in all dimensions) between two positions under periodic boundary conditions. -/

noncomputable def minImageDistance (box_length posA posB : Fin n → ℝ) : ℝ :=
  let dist := fun i => pbc (posB i - posA i) (box_length i)
  (Finset.univ.sum fun i => (dist i) ^ 2).sqrt

/-- Lennard-Jones potential function. Returns 0 if r > cutoff. -/

noncomputable def Ljp (r cutoff epsilon sigma : ℝ) : ℝ :=
  if r ≤ cutoff then
    let r6 := (sigma / r) ^ 6
    let r12 := r6 ^ 2
    4 * epsilon * (r12 - r6)
  else
    0

noncomputable def total_energy (positions : List (Fin n → ℝ))
  (box_length : Fin n → ℝ) (cutoff epsilon sigma : ℝ) : ℝ :=
  let num_atoms := positions.length
  let rec energy : Nat → Nat → ℝ → ℝ
    | 0, _, acc => acc
    | i+1, 0, acc =>
      -- when j = 0, move to the next i
      energy i i acc
    | i+1, j+1, acc =>
      -- sum over pair (i, j) then decrease j
      let pos_i := positions.get! i
      let pos_j := positions.get! j
      let r := minImageDistance cell_length pos_i pos_j
      energy (i+1) j (acc + Ljp r cutoff epsilon sigma)
  energy num_atoms (num_atoms - 1) 0.0


noncomputable def pairwiseEnergy (positions : List (Fin n → ℝ))
  (cell_length : Fin n → ℝ)
  (cutoff epsilon sigma : ℝ) : ℝ :=
  (List.range positions.length).foldl
    (fun acc i =>
      let pi := positions.get! i
      let innerSum :=
        (List.range i).foldl
          (fun innerAcc j =>
            let pj := positions.get! j
            let r := minImageDistance cell_length pi pj
            innerAcc + Ljp r cutoff epsilon sigma
          )
          0.0
      acc + innerSum
    )
    0.0

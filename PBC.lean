/-
Authors: Ejike Ugwuanyi
-/

import Mathlib

/-! Basic Math Theorems on `round` function. -/
variable [LinearOrderedField α] [FloorRing α]

theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
 rw [round_eq x, show x - 1 / 2 = x + 1 / 2 - 1 by nlinarith]
 exact Int.sub_one_lt_floor (x + 1/2)

theorem round_le_add_half (x : α) : (round x : α) ≤ x + 1 / 2 := by
 rw [round_eq x]
 exact Int.floor_le (x + 1 / 2)

theorem round_sub_one_le_x (x : α) : round x - 1 ≤ x := by
  rw [round_eq x]
  have h1 : ↑⌊x + 1/2⌋ ≤ x + 1/2 := Int.floor_le (x + 1/2)
  have h2 : ↑⌊x + 1/2⌋ - 1 ≤ (x + 1/2) - 1 := by linarith
  have h3 : (x + 1/2) - 1 = x - 1/2 := by ring
  rw [h3] at h2
  have h4 : x - 1/2 ≤ x := by linarith
  exact le_trans h2 h4

theorem abs_diff_round_le_half (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq]
  have h1 : x - 1/2 < ↑⌊x + 1/2⌋ := by
    have h1a : x + 1/2 < ↑⌊x + 1/2⌋ + 1 := by apply Int.lt_floor_add_one
    linarith
  have h2 : ↑⌊x + 1/2⌋ ≤ x + 1/2 := Int.floor_le (x + 1/2)
  have h3 : -(1/2) ≤ x - ↑⌊x + 1/2⌋ ∧ x - ↑⌊x + 1/2⌋ ≤ 1/2 := by
    constructor
    · linarith
    · linarith
  exact abs_le.mpr h3


/- `Periodic boundary conditions (PBCs)` are essential in MD simulations to avoid surface or edge effects 
that can disrupt the bulk behavior of a system. By simulating an `infinite` system, PBCs allow molecules 
that leave one side of the simulation box to re-enter from the opposite side, creating the effect of an 
unbounded environment.-/

/-! `apply_pbc` : Function that calculates the adjusted p. -/
def apply_pbc (p c : α) : α :=
 p - c * round (p / c)

/- This theorem establishes that the periodic boundary condition (PBC) operation ensures the wrapped distance of 
any value 𝑥 within a cell of length 𝐿 > 0 is bounded by 𝐿/2. It guarantees that distances computed under PBC are 
minimal and consistent, a crucial property for simulations with periodic systems.-/

theorem abs_pbc_le (x L : ℝ) (hL : 0 < L) : |pbc x L| ≤ L / 2 := by
  dsimp [pbc]
  have : |(x / L) - round (x / L)| ≤ 1 / 2 := abs_diff_round_le_half (x / L)
  calc
    |x - L * round (x / L)| = |L * ((x / L) - round (x / L))| := by field_simp
    _ = |L| * |(x / L) - round (x / L)| := by rw [abs_mul]
    _ = L * |(x / L) - round (x / L)| := by rw [abs_of_pos hL]
    _ ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left this (by linarith)
    _ = L / 2 := by ring

/- This theorem proves that the periodic boundary condition (PBC) operation is invariant under translations by 
integer multiples of the cell length 𝐿 when 𝐿 ≠ 0. It ensures that subtracting 𝑘⋅𝐿 from 𝑥 does not affect the 
wrapped result, highlighting the periodicity and consistency of the PBC operation.-/

theorem pbc_periodic (x L : ℝ) (k : ℤ) (hL : L ≠ 0) : pbc (x - k * L) L = pbc x L := by
  dsimp [pbc]
  have : round ((x - k * L) / L) = round (x / L - k) := by
    congr
    field_simp
    ring
  rw [this, round_sub_int]
  rw [Int.cast_sub, mul_sub]
  ring

theorem apply_pbc_le_box_length (p c : α) (h1 : 0 < c) : apply_pbc p c < c := by
  dsimp only [apply_pbc]
  by_cases h : p / c ≤ round (p / c)
  · calc
      p - c * (round (p / c)) ≤ p - c * (p / c) := by
        apply sub_le_sub_left
        exact mul_le_mul_of_nonneg_left h (le_of_lt h1)
      _ = p - p := by rw [mul_div_cancel' p h1.ne']
      _ = 0 := by simp
      _ < c := h1

  · rw [not_le] at h
    have h2 : p / c - 1 / 2 < round (p / c) := sub_half_lt_round (p / c)
    calc
      p - c * round (p / c) < p - c * (p / c - 1 / 2) := by
        apply sub_lt_sub_left
        apply mul_lt_mul_of_pos_left h2 h1
      _ = c / 2 := by
        rw [mul_sub, mul_div_cancel' p h1.ne']; ring
      _ < c := by exact half_lt_self h1


-- Prove that `apply_pbc 0 c = 0` for any cell length `c`
-- `Zero Case`: What Happens When p = 0
-- If `p = 0`, then `apply_pbc(0, c)` should always return `0`, regardless of the value of the cell length `c`.
theorem apply_pbc_zero (c : α) : apply_pbc 0 c = 0 := by
  dsimp [apply_pbc]
  have h1 : (0 / c) = 0 := by norm_num
  rw [h1, round_zero]
  simp

--  `Scaling Behavior`: Prove that `apply_pbc (k * p, k * c)` is the same as `k * apply_pbc(p, c)` for a constant `k`.
-- This theorem explores how scaling both `p` and `c` by a constant `k` affects the result of the `apply_pbc` function.
theorem apply_pbc_scaling (k p c : α) (h : 0 < k) : apply_pbc (k * p) (k * c) = k * apply_pbc p c := by
  dsimp [apply_pbc]
  have h1 : (k * p) / (k * c) = p / c := mul_div_mul_left p c h.ne'
  rw [h1]
  ring

-- `Behavior for Integer Multiples of c`: Prove that if `p` is an integer multiple of `c`, then `apply_pbc(p, c) = 0`.
-- Prove that apply_pbc(n * c, c) = 0 for integer multiples of c

lemma div_of_int_mul (n : ℤ) (c : α) (h : 0 < c) : (↑n * c) / c = ↑n := by
  calc
    (↑n * c) / c = ↑n * (c / c) := by rw [mul_div_assoc]
    _ = ↑n * 1 := by rw [div_self h.ne']
    _ = ↑n := by rw [mul_one]

lemma round_int_cast (n : ℤ) : ↑(round (↑n : α)) = (↑n : α) := by
  rw [Int.cast_inj]
  simp

theorem apply_pbc_multiple_of_cell_length (n : ℤ) (c : α) (h : 0 < c) : apply_pbc (↑n * c) c = 0 := by
  dsimp [apply_pbc]
  rw [div_of_int_mul]
  rw [round_int_cast]
  ring
  linarith













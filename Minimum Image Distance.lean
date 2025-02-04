/-
Authors: Ejike Ugwuanyi
-/

import Mathlib

noncomputable def pbc (position box_length : ℝ) : ℝ :=  position - box_length * round (position / box_length)


noncomputable def minImageDistance (box_length posA posB : Fin n → ℝ) : ℝ :=
  let dist := fun i => pbc (posB i - posA i) (box_length i)
  (Finset.univ.sum (fun i => (dist i) ^ 2)).sqrt


theorem pbc_periodic (x L : ℝ) (k : ℤ) (hL : L ≠ 0) : pbc (x - k * L) L = pbc x L := by
  dsimp [pbc]
  have : round ((x - k * L) / L) = round (x / L - k) := by
    congr
    field_simp
    ring
  rw [this, round_sub_int]
  rw [Int.cast_sub, mul_sub]
  ring

--# The minImageDistance is bounded above by the diagonal of the simulation cell.
theorem minImageDistance_bounded
    (box_length posA posB : Fin n → ℝ) (hbox : ∀ i, 0 < box_length i) :
    minImageDistance box_length posA posB
    ≤ (Finset.univ.sum fun i => (box_length i / 2) ^ 2).sqrt := by
  dsimp [minImageDistance]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have bound : |pbc (posB i - posA i) (box_length i)| ≤ box_length i / 2 :=
    abs_pbc_le (posB i - posA i) (box_length i) (hbox i)
  calc
    (pbc (posB i - posA i) (box_length i))^2
        = |pbc (posB i - posA i) (box_length i)|^2 := by rw [sq_abs]
    _ ≤ (box_length i / 2)^2 := by
      apply pow_le_pow_left
      · exact abs_nonneg (pbc (posB i - posA i) (box_length i))
      · exact bound


--# The minimum image distance is invariant under periodic translations.
theorem minImageDistance_periodic
    (box_length posA posB : Fin n → ℝ) (k : Fin n → ℤ)
    (hbox : ∀ i, box_length i ≠ 0) :
    minImageDistance box_length posA posB =
    minImageDistance box_length (fun i => posA i + (k i : ℝ) * box_length i) posB := by
  dsimp [minImageDistance]
  have h_dist : ∀ i,
      pbc (posB i - (posA i + (k i : ℝ) * box_length i)) (box_length i)
        = pbc (posB i - posA i) (box_length i) := by
    intro i
    rw [sub_add_eq_sub_sub]
    exact pbc_periodic (posB i - posA i) (box_length i) (k i) (hbox i)
  simp_rw [h_dist]

--# The minimum image distance between any two points is non-negative
theorem minImageDistance_nonneg (box_length posA posB : Fin n → ℝ) :
  0 ≤ minImageDistance box_length posA posB := by
  unfold minImageDistance
  apply Real.sqrt_nonneg

--# The minimum image distance between two identical points is zero.
theorem minImageDistance_self (box_length pos : Fin n → ℝ) :
  minImageDistance box_length pos pos = 0 := by
  unfold minImageDistance
  have h_dist : ∀ i, pbc (pos i - pos i) (box_length i) = 0 := by
    intro i
    simp [pbc]
  simp_rw [h_dist]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]

lemma apply_pbc_sub (a b L : α) :
  pbc (a - b) L = (a - b) - L * round ((a - b) / L) := by rfl


lemma apply_pbc_nested (a b L : α) (hL : L ≠ 0) :
  pbc (pbc a L - pbc b L) L = (a - b) - L * round ((a - b) / L) := by
  calc
    pbc (pbc a L - pbc b L) L
        = pbc ((a - L * round (a / L)) - (b - L * round (b / L))) L := by rfl
    _ = pbc ((a - b) - L * (round (a / L) - round (b / L))) L := by ring_nf
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round (((a - b) - L * (round (a / L) - round (b / L))) / L) := by rw [pbc]
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round ((a - b) / L - (round (a / L) - round (b / L))) := by
      have h_div : ((a - b) - L * (round (a / L) - round (b / L))) / L =
                    (a - b) / L - (round (a / L) - round (b / L)) := by field_simp [hL]
      rw [h_div]
    _ = (a - b) - L * round ((a - b) / L) := by
        rw [← Int.cast_sub, round_sub_int, sub_sub, ← mul_add, ← Int.cast_add, add_sub_cancel]


-- Define the squared minimum image distance using a 3D vector as `Fin 3 → α`
def squaredminImageDistance (box_length posA posB : Fin 3 → α) : α :=
  let dx := pbc (posB ⟨0, by decide⟩  - posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩)
  dx^2 + dy^2 + dz^2

--# Theorem to show that applying PBC to each position individually gives the same squared distance
/-
This theorem asserts that the minimum image distance between two positions posA and posB in a periodic box
can be calculated equivalently in two ways:
By directly computing the minimum image distance for the box size, or
By first applying periodic boundary conditions (PBC) to both positions and then computing the minimum image
distance. In other words, the order of applying PBC—either before or during the computation of distances—
does not affect the final result.
-/

theorem squaredminImageDistance_theorem (box_length posA posB : Fin 3 → α) (hL : ∀ i, box_length i ≠ 0) :
  squaredminImageDistance box_length posA posB =
  squaredminImageDistance box_length
    (λ i => pbc (posA i) (box_length i))
    (λ i => pbc (posB i) (box_length i)) := by
  unfold squaredminImageDistance

  have h0 : pbc (pbc (posB ⟨0, by decide⟩) (box_length ⟨0, by decide⟩) -
                       pbc (posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩)) (box_length ⟨0, by decide⟩) =
            pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨0, by decide⟩

  have h1 : pbc (pbc (posB ⟨1, by decide⟩) (box_length ⟨1, by decide⟩) -
                       pbc (posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩)) (box_length ⟨1, by decide⟩) =
            pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨1, by decide⟩

  have h2 : pbc (pbc (posB ⟨2, by decide⟩) (box_length ⟨2, by decide⟩) -
                       pbc (posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩)) (box_length ⟨2, by decide⟩) =
            pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨2, by decide⟩
  simp_rw [h0, h1, h2]


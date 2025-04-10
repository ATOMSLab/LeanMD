import Mathlib
namespace LeanLJ

class HasSqrt (α : Type) where
  sqrt : α → α

instance : HasSqrt Float where
  sqrt := Float.sqrt

instance : HasSqrt ℕ where
  sqrt := Nat.sqrt

instance : HasSqrt ℤ where
  sqrt := Int.sqrt

instance : HasSqrt ℚ where
  sqrt := Rat.sqrt

noncomputable instance : HasSqrt ℝ where
  sqrt := Real.sqrt


class HasRound (α : Type) where
  pround : α → α

instance : HasRound Float where
  pround := Float.round

instance [LinearOrderedField α] [FloorRing α] : HasRound α where
  pround := (fun (x : α) => round x)


-- Polymorphic definition of Periodic boundary condition
def pbc (position boxLength : α) [HSub α α α] [HMul α α α] [HDiv α α α] [HasRound α] : α :=
  position - boxLength * (HasRound.pround (position / boxLength) : α)

-- Float type definition of periodic boundary conditions
def pbc_float (position boxLength : Float) : Float :=
  position - boxLength * Float.round (position / boxLength)

-- Real type definition of periodic boundary conditions
noncomputable def pbc_real (position boxLength : ℝ) : ℝ :=
  position - boxLength * round (position / boxLength)


-- Polymorphic definition of Lennard-Jones potential
def lj_p {α β : Type} [LE α] [DecidableLE α] [HDiv α α α] [HPow α β α] [HSub α α α]
  [HMul α α α] [OfNat β 2] [OfNat α 4] [OfNat β 6] [Zero α] (r r_c ε σ : α) : α :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ (6 : β)
    let r12 := r6 ^ (2 : β)
    4 * ε * (r12 - r6)
  else
    0

-- Float type definition of Lennard-Jones potential
def lj_float (r r_c ε σ : Float) : Float :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0

-- Real type definition of Lennard-Jones potential
noncomputable def lj_real (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0


-- Polymorphic definition of Minimum image distance in 3 dimensions, simplified
def MinImageDistance (α β : Type) (boxLength posA posB : Fin 3 → α) 
    [HSub α α α] [HMul α α α] [HDiv α α α] [HPow α β α] [AddCommMonoid α] [HasSqrt α] [HasRound α] [OfNat β 2] : α :=
  let dist := fun i => pbc (posB i - posA i) (boxLength i)
  HasSqrt.sqrt (Finset.univ.sum (fun i => (dist i) ^ (2 : β)))

-- Polymorphic definition of Minimum image distance in 3 dimensions
def minImageDistance (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) 
    [HSub α α α] [HMul α α α] [HDiv α α α] [HPow α β α] [AddCommMonoid α] [HasSqrt α] [HasRound α] [OfNat β 2] : α :=
  let dx := pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (boxLength ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (boxLength ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (boxLength ⟨2, by decide⟩)
  HasSqrt.sqrt (dx ^ (2 : β) + dy ^ (2 : β) + dz ^ (2 : β))

-- Real type definition of Minimum image distance
noncomputable def minImageDistance_real (posA posB : Fin 3 → ℝ) (boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbc_real (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (boxLength ⟨0, by decide⟩)
  let dy := pbc_real (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (boxLength ⟨1, by decide⟩)
  let dz := pbc_real (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (boxLength ⟨2, by decide⟩)
  HasSqrt.sqrt (dx ^ 2 + dy ^ 2 + dz ^ 2)

#eval HasSqrt.sqrt (5:Float)

end LeanLJ

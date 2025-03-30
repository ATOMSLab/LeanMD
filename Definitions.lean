import Mathlib
namespace Research

class HasSqrt (α : Type*) where
  sqrt : α → α

noncomputable instance : HasSqrt ℝ where
  sqrt := Real.sqrt


variable {α : Type*} [LinearOrderedField α] [FloorRing α] [HasSqrt α]


-- Polymorphic definition of Periodic boundary condition
def pbc (position boxLength : α) : α :=
  position - boxLength * (round (position / boxLength) : α)

-- Float type definition of periodic boundary conditions
def pbc_float (position boxLength : Float) : Float :=
  position - boxLength * Float.round (position / boxLength)

-- Real type definition of periodic boundary conditions
noncomputable def pbc_real (position boxLength : ℝ) : ℝ :=
  position - boxLength * round (position / boxLength)


-- Polymorphic definition of Lennard-Jones potential
def ljp {α β : Type} [LE α] [DecidableLE α] [HDiv α α α] [HPow α β α] [HSub α α α]
  [HMul α α α] [OfNat β 2] [OfNat α 4] [OfNat β 6] [Zero α] (r r_c ε σ : α) : α :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ (6 : β)
    let r12 := r6 ^ (2 : β)
    4 * ε * (r12 - r6)
  else
    0

-- Float type definition of Lennard-Jones potential
def ljfloat (r r_c ε σ : Float) : Float :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0

-- Real type definition of Lennard-Jones potential
noncomputable def ljreal (r r_c ε σ : ℝ) : ℝ :=
  if r ≤ r_c then
    let r6 := (σ / r) ^ 6
    let r12 := r6 ^ 2
    4 * ε * (r12 - r6)
  else
    0


def MinImageDistance (boxLength posA posB : Fin 3 → α) : α :=
  let dist := fun i => pbc (posB i - posA i) (boxLength i)
  HasSqrt.sqrt (Finset.univ.sum (fun i => (dist i) ^ 2))


-- Polymorphic definition of Minimum image distance
def minImageDistance (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) : α :=
  let dx := pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (boxLength ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (boxLength ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (boxLength ⟨2, by decide⟩)
  HasSqrt.sqrt (dx ^ 2 + dy ^ 2 + dz ^ 2)


noncomputable def minImageDistance_real (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) : α :=
  let dx := pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (boxLength ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (boxLength ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (boxLength ⟨2, by decide⟩)
  HasSqrt.sqrt (dx ^ 2 + dy ^ 2 + dz ^ 2)

end Research

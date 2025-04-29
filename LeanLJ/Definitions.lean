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

instance : Pow Float Nat where
  pow := fun x n =>
    let rec go (x : Float) (n : Nat) : Float :=
      match n with
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n


class LJCompatible (α : Type ) extends LinearOrderedField α, Div α, HPow α Nat α, HasSqrt α, HasRound α

-- Polymorphic definition of Lennard-Jones potential
def lj_p {α : Type} [LJCompatible α] (r r_c ε σ : α) : α :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

-- Polymorphic definition of Periodic boundary condition
def pbc (position boxLength : α) [LJCompatible α] : α :=
  position - boxLength * (HasRound.pround (position / boxLength) : α)

-- Float type definition of periodic boundary conditions
def pbc_float (position boxLength : Float) : Float :=
  position - boxLength * Float.round (position / boxLength)

-- Real type definition of periodic boundary conditions
noncomputable def pbc_real (position boxLength : ℝ) : ℝ :=
  position - boxLength * round (position / boxLength)


-- Float type definition of Lennard-Jones potential
def lj_float (r r_c ε σ : Float) : Float :=
    if r ≤ r_c then
      let r3 := (σ / r) ^ (3 : Nat)
      let r6 := r3 * r3
      let r12 := r6 * r6
      4 * ε * (r12 - r6)
    else
      0

-- Real type definition of Lennard-Jones potential
noncomputable def lj_real  (r r_c ε σ  : ℝ) : ℝ :=
  if r ≤ r_c then
    let r3 := (σ / r) ^ (3 : Nat)
    let r6 := r3 * r3
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0

-- Polymorphic definition of Minimum image distance in 3 dimensions, simplified
def MinImageDistance {α : Type } [LJCompatible α] (boxLength posA posB : Fin 3 → α)  : α :=
  let dist := fun i => pbc (posB i - posA i) (boxLength i)
  HasSqrt.sqrt (Finset.univ.sum (fun i => (dist i) ^ (2 : Nat)))

-- Polymorphic definition of Minimum image distance in 3 dimensions
def minImageDistance {α : Type } [LJCompatible α]
    (posA posB : Fin 3 → α) (boxLength : Fin 3 → α) : α :=
  let dx := pbc (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  HasSqrt.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

-- Real type definition of Minimum image distance
noncomputable def minImageDistance_real (posA posB : Fin 3 → ℝ) (boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbc_real (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc_real (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc_real (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  HasSqrt.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

-- Float type definition of Minimum image distance
def minImageDistance_float (posA posB : Fin 3 → Float) (boxLength : Fin 3 → Float) : Float :=
  let dx := pbc_float (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc_float (posB (1:Fin 3) - posA (1:Fin 3)) (boxLength (1:Fin 3))
  let dz := pbc_float (posB (2:Fin 3) - posA (2:Fin 3)) (boxLength (2:Fin 3))
  Float.sqrt (dx ^ (2 : Nat) + dy ^ (2 : Nat) + dz ^ (2 : Nat))

#eval HasSqrt.sqrt (5:Float)

def U_LRC
  {α : Type} [LJCompatible α]
  (ρ pi ε σ rc : α) : α :=
  (8 * pi * ρ * ε) *
    ((1 / 9) * (σ ^ (12 : Nat) / rc ^ (9 : Nat)) - (1 / 3) * (σ ^ (6 : Nat) / rc ^ (3 : Nat)))

noncomputable def U_LRC_real (ρ ε σ rc  : ℝ) : ℝ :=
  (8 * π  * ρ * ε) * ((1/9) * (σ ^ 12 / rc ^ 9) - (1/3) * (σ ^ 6 / rc ^ 3))

end LeanLJ

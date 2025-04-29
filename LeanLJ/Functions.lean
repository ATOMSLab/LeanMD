import Mathlib.Algebra.Field.Basic
namespace LeanLJ

instance : Pow Float Nat where
  pow := fun x n =>
    let rec go (x : Float) (n : Nat) : Float :=
      match n with
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n

class LJCompatible (α : Type) extends LinearOrderedField α, Div α, HPow α Nat α

def pbc (position box_length : Float) : Float :=
  position - box_length * Float.round (position / box_length)

def minImageDistance (posA posB : Fin 3 → Float) (box_length : Fin 3 → Float) : Float :=
  let dx := pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩)
  (dx^2 + dy^2 + dz^2).sqrt


def lj_float (r r_c ε σ : Float) : Float :=
    if r ≤ r_c then
      let r3 := (σ / r) ^ (3 : Nat)
      let r6 := r3 * r3
      let r12 := r6 * r6
      4 * ε * (r12 - r6)
    else
      0

def compute_total_energy (positions : List (Fin 3 → Float)) (box_length : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  let num_atoms := positions.length
  let rec energy (i j : Nat) (acc : Float) : Float :=
    if i = 0 then acc
    else if j = 0 then energy (i - 1) (i - 2) acc
    else
      let r := minImageDistance (positions[i - 1]!) (positions[j - 1]!) box_length
      let e := lj_float r cutoff ε σ
      energy i (j - 1) (acc + e)
  energy num_atoms (num_atoms - 1) 0.0


def pi : Float := 3.141592653589793

def rho (N boxlength : Float) : Float := N / (boxlength)^3

def U_LRC
  {α : Type} [LJCompatible α]
    (ρ pi ε σ rc : α) : α :=
  (8 * π * ρ * ε) *
    ((1 / (9 : α)) * (σ ^ (12 : Nat) / rc ^ (9 : Nat))
       - (1 / (3 : α)) * (σ ^ (6 : Nat)  / rc ^ (3 : Nat)))
  
def U_LRC_float (rho pi ε σ rc  : Float) : Float :=
  (8 * rho * pi * ε) * ((1/9) * (σ ^ 12 / rc ^ 9) - (1/3) * (σ ^ 6 / rc ^ 3))

def getNISTEnergy_LRC (n : Nat) : Option Float :=
  match n with
  | 30 => some (-0.54517)
  | 200 => some (-24.230)
  | 400 => some (-49.622)
  | 800 => some (-198.49)
  | _ => none

def getNISTEnergy (n : Nat) : Option Float :=
  match n with
  | 30 => some (-16.790)
  | 200 => some (-690.000)
  | 400 => some (-1146.700)
  | 800 => some (-4351.500)
  | _ => none


end LeanLJ

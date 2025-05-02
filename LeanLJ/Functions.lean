import Mathlib.Algebra.Field.Basic
namespace LeanLJ

instance : Pow Float Nat where
  pow := fun x n =>
    let rec go (x : Float) (n : Nat) : Float :=
      match n with
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n

class RealLike (α : Type ) extends LinearOrderedField α, Div α, HPow α Nat α, HasSqrt α, HasRound α

def pbc (position boxLength : Float) : Float :=
  position - boxLength * Float.round (position / boxLength)

def minImageDistance (posA posB : Fin 3 → Float) (boxLength : Fin 3 → Float) : Float :=
  let dx := pbc (posB (0:Fin 3) - posA (0: Fin 3)) (boxLength (0: Fin 3))
  let dy := pbc (posB (1: Fin 3) - posA (1: Fin 3)) (boxLength (1: Fin 3))
  let dz := pbc (posB (2: Fin 3) - posA (2: Fin 3)) (boxLength (2 : Fin 3))
  (dx^2 + dy^2 + dz^2).sqrt


def lj_Float (r r_c ε σ : Float) : Float :=
    if r ≤ r_c then
      let r3 := (σ / r) ^ (3 : Nat)
      let r6 := r3 * r3
      let r12 := r6 * r6
      4 * ε * (r12 - r6)
    else
      0

def pairs (n : Nat) : List (Nat × Nat) :=
  List.flatten ((List.range n).map fun i =>
    (List.range (n - i - 1)).map fun k =>
      (i, i + k + 1))

def computeTotalEnergy (positions : List (Fin 3 → Float))
    (boxLength : Fin 3 → Float)
    (cutoff ε σ : Float) : Float :=
  let n := positions.length
  let indexPairs := pairs n
  indexPairs.foldl (fun acc (i, j) =>
    let posI := List.get! positions i
    let posJ := List.get! positions j
    let r := minImageDistance posI posJ boxLength
    acc + lj_Float r cutoff ε σ
  ) 0.0

def pi : Float := 3.141592653589793

def rho (N box_length : Float) : Float := N / (boxLength)^3

def U_LRC
  {α : Type} [RealLike α]
    (ρ pi ε σ rc : α) : α :=
  (8 * π * ρ * ε) *
    ((1 / (9 : α)) * (σ ^ (12 : Nat) / rc ^ (9 : Nat))
       - (1 / (3 : α)) * (σ ^ (6 : Nat)  / rc ^ (3 : Nat)))
  
def U_LRC_Float (rho pi ε σ rc  : Float) : Float :=
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

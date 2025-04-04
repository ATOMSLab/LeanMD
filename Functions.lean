namespace Research

def pbc (position box_length : Float) : Float :=
  position - box_length * Float.round (position / box_length)

def minImageDistance (posA posB : Fin 3 → Float) (box_length : Fin 3 → Float) : Float :=
  let dx := pbc (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩)
  let dy := pbc (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩)
  let dz := pbc (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩)
  (dx^2 + dy^2 + dz^2).sqrt

def lj_float (r cutoff ε σ : Float) : Float :=
  if r ≤ cutoff then
    let r6 := (σ / r) ^ 6
    let r12 := r6 * r6
    4 * ε * (r12 - r6)
  else
    0.0

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

def getNISTEnergy (n : Nat) : Option Float :=
  match n with
  | 30 => some (-16.790)
  | 200 => some (-690.000)
  | 400 => some (-1146.700)
  | 800 => some (-4351.500)
  | _ => none


end Research

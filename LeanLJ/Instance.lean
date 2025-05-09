import Mathlib
namespace LeanLJ

instance : Pow Float Nat where
  pow := fun x n =>
    let rec go (x : Float) (n : Nat) : Float :=
      match n with
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n

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


class RealLike (α : Type ) extends Field α, LinearOrder α, IsStrictOrderedRing α, Div α, HPow α Nat α, HasSqrt α, HasRound α

end LeanLJ

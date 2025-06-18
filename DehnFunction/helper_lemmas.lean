-- iff : (step R x y), (xy⁻¹ or yx⁻¹ ∈ ConjSet (R))
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Rotate
import DehnFunction.Area1
import DehnFunction.Area2
import DehnFunction.Area_equiv




def ReduceMyPairs₂ {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | [x] => [x]
  | (p, b) :: xs =>
    match xs.getLast with
    | some (q, b') =>
      if p == q && b != b' then
        ReduceMyPairs (xs.dropLast)
      else
        (p, b) :: xs
    | none => (p, b) :: xs  -- Shouldn't happen due to first match
termination_by L.length

theorem cycperm_equiv_conj_by_preword : True := by sorry


def CycReduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Bool := ([L.getLast!].mk ≠ ([L.head].mk)⁻¹)

lemma CycRed_not_conj {α : Type*} [DecidableEq α] (L : List (α × Bool)) (h₁ : CycReduced L) : (L = []) ∨ ((L.head!).mk ≠ ((L.getLast!).mk)⁻¹) := by sorry

theorem step_iff_conjugate₂ {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} (x y : FreeGroup G):
    (step R x y) ↔
  x*y⁻¹ ∈ Group.conjugatesOfSet R ∨ y*x⁻¹ ∈ Group.conjugatesOfSet R := by
    unfold step
    unfold CycRed
    unfold ReduceMyPairs
    sorry

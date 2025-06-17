import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
-- import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.List.Rotate
import DehnFunction.Area2
import DehnFunction.Area1

#check Area2
#check wordArea

lemma A_two_le_A_one {α : Type*} {n : ℕ} [DecidableEq α] (rel_set : Set (FreeGroup α)) (w : FreeGroup α) (h : (Area2 rel_set w = n)) : n ≤ wordArea rel_set w := by
    unfold wordArea
    simp [sInf]
    sorry



lemma form_of_cycred {α : Type*} [DecidableEq α] (x : FreeGroup α) : True := sorry

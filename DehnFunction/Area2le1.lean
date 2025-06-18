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
import DehnFunction.Area1le2

#check Area2
#check wordArea

lemma A_two_le_A_one {α : Type*} {n : ℕ} [DecidableEq α] (rel_set : Set (FreeGroup α)) (w : FreeGroup α) (h : (wordArea rel_set w = n)) : Area2 rel_set w ≤ n := by
    unfold Area2
    apply Nat.sInf_le
    simp
    have isprconj : ∃ (l : List (FreeGroup α)),(∀ c ∈ l, c ∈ Group.conjugatesOfSet rel_set ∨ c⁻¹ ∈ Group.conjugatesOfSet rel_set) ∧
    l.length = n ∧ w = l.prod := by sorry
    unfold step_n
    cases n with
    | zero =>
      simp
      aesop
    | succ =>
      expose_names
      split
      · aesop
      · expose_names
        simp at heq
        rw [heq] at isprconj
        simp at isprconj
        rcases isprconj with ⟨ll,hypo⟩
        rcases hypo with ⟨fs, sc, th⟩
        apply step_is_conjugate
      · sorry









lemma form_of_cycred {α : Type*} [DecidableEq α] (x : FreeGroup α) : True := sorry

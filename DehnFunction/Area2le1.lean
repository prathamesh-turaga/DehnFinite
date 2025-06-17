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
    unfold step_n
    cases n with
    | zero =>
        apply FreeGroup.toWord_eq_nil_iff.mp ?_
        simp
        rw [wordArea_eq_zero_iff] at h
        rcases h with ⟨a,b⟩
        rfl
        sorry

    | succ =>
        expose_names
        aesop
        unfold wordArea at h
        have hmod : sInf {n | IsProductOfNConjugates rel_set n w} <= 1 := by exact Nat.le_of_eq h
        have one_in_set : 1 ∈ {n | IsProductOfNConjugates rel_set n w} := by sorry
        unfold IsProductOfNConjugates at one_in_set
        have smalllist : ∃ l, (∀ c ∈ l, c ∈ Group.conjugatesOfSet rel_set ∨ c⁻¹ ∈ Group.conjugatesOfSet rel_set) ∧ l.length = 1 ∧ w = List.prod l := by exact
          one_in_set
        rcases smalllist with ⟨a,b,c,d⟩
        sorry
        /-rw [step_is_conjugate w y]
        simp [one_mul, mul_one]-/









lemma form_of_cycred {α : Type*} [DecidableEq α] (x : FreeGroup α) : True := sorry

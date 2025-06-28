import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.List.Rotate
import DehnFunction.Area2
import DehnFunction.Area1
import Mathlib.Data.Set.Basic

#check Area2
#check wordArea


lemma sInf_le_sInf_of_subset {a b : Set ℕ} (ha : a.Nonempty) (h_sub : a ⊆ b) : sInf b ≤ sInf a := by

  apply le_csInf
  . exact ha
  . intro n hn_in_a
    have hn_in_b : n ∈ b := by
      exact h_sub hn_in_a
    exact Nat.sInf_le hn_in_b



theorem area1_le_area2 {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  wordArea R w ≤ Area2 R w := by

    unfold Area2
    by_cases h : {n | step_n R n w 1}.Nonempty
    . apply sInf_le_sInf_of_subset h
      intro n hn_in
      simp
      simp at hn_in
      exact step_n_implies_IsProductOfNConjugates R n w hn_in

    . have h_empty : {n | step_n R n w 1} = ∅ := by
        exact Set.not_nonempty_iff_eq_empty.mp h

      have h_rhs_zero: sInf {n | step_n R n w 1} = 0 := by
        rw [h_empty]
        simp

      rw [h_rhs_zero]
      have h_w_notin: w ∉ Subgroup.normalClosure R := by
        apply empty_step R w
        exact h_empty

      simp [h_w_notin]
      rw [wordArea_eq_zero_iff R w]
      right
      exact h_w_notin


theorem mem_clos_iff_isProdConj_nonempty {G : Type*} (R : Set (FreeGroup G)) (w : FreeGroup G)
  : {n | IsProductOfNConjugates R n w}.Nonempty ↔ w ∈ Subgroup.normalClosure R := by
  rw[mem_normalClosure_iff_prod_conj]
  constructor
  . rintro ⟨ n, l, h_conj, h_len, h_prod⟩
    use l
  . rintro ⟨ l, h_conj, h_prod⟩
    use l.length
    use l





theorem area2_le_area1 {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  Area2 R w ≤ wordArea R w := by

  by_cases h_mem : w ∈ Subgroup.normalClosure R

  ·
    have h_nonempty : {n | IsProductOfNConjugates R n w}.Nonempty := by
      rw [mem_clos_iff_isProdConj_nonempty]
      exact h_mem
    apply sInf_le_sInf_of_subset h_nonempty
    intro n h_is_prod

    rcases h_is_prod with ⟨l, h_l_conj, h_l_len, h_l_prod⟩
    simp

    rw [← h_l_len, h_l_prod]
    exact prod_conj_implies_step_n R l h_l_conj

  ·
    have h_area1_zero : wordArea R w = 0 := by
      unfold wordArea
      have h_set_empty : {n | IsProductOfNConjugates R n w} = ∅ := by
        by_contra!
        rw [mem_clos_iff_isProdConj_nonempty] at this
        exact h_mem this

      rw [h_set_empty]
      exact Nat.sInf_empty

    rw [h_area1_zero]
    have h_set_empty : {n | step_n R n w 1} = ∅ := by
      exact step_empty R w h_mem
    unfold Area2
    rw [h_set_empty]
    simp


  theorem area1_eq_area2 {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  wordArea R w = Area2 R w := by
    apply le_antisymm
    . exact area1_le_area2 R w
    . exact area2_le_area1 R w

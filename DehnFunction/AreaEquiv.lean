import DehnFunction.Area2
import DehnFunction.Area1
import Mathlib.Data.Set.Basic

open FreeGroup.ConjStep

lemma Set.sInf_le_sInf_of_subset {a b : Set ℕ} (ha : a.Nonempty) (h_sub : a ⊆ b) : sInf b ≤ sInf a := by
  apply le_csInf
  . exact ha
  . intro n hn_in_a
    have hn_in_b : n ∈ b := by
      exact h_sub hn_in_a
    exact Nat.sInf_le hn_in_b

namespace FreeGroup

theorem area_le_areaSteps {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  area R w ≤ areaSteps R w := by
    unfold areaSteps
    by_cases h : {n | StepN R n w 1}.Nonempty
    . apply Set.sInf_le_sInf_of_subset h
      intro n hn_in
      simp
      simp at hn_in
      exact step_n_implies_IsProductOfNConjugates R n w hn_in
    . have h_empty : {n | StepN R n w 1} = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h_rhs_zero: sInf {n | StepN R n w 1} = 0 := by
        rw [h_empty]
        simp
      rw [h_rhs_zero]
      have h_w_notin: w ∉ Subgroup.normalClosure R := by
        apply empty_step R w
        exact h_empty
      simp [h_w_notin]
      rw [area.eq_zero_iff R w]
      right
      exact h_w_notin

theorem mem_normalClosure_iff_isProductOfNConjugates_nonempty {G : Type*} (R : Set (FreeGroup G)) (w : FreeGroup G)
  : {n | IsProductOfNConjugates R n w}.Nonempty ↔ w ∈ Subgroup.normalClosure R := by
  rw[Subgroup.mem_normalClosure_iff_prod_conj]
  constructor
  . rintro ⟨ n, l, h_conj, h_len, h_prod⟩
    use l
  . rintro ⟨ l, h_conj, h_prod⟩
    use l.length
    use l

theorem areaSteps_le_area {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  areaSteps R w ≤ area R w := by
  by_cases h_mem : w ∈ Subgroup.normalClosure R
  · have h_nonempty : {n | IsProductOfNConjugates R n w}.Nonempty := by
      rw [mem_normalClosure_iff_isProductOfNConjugates_nonempty]
      exact h_mem
    apply Set.sInf_le_sInf_of_subset h_nonempty
    intro n h_is_prod
    rcases h_is_prod with ⟨l, h_l_conj, h_l_len, h_l_prod⟩
    simp
    rw [← h_l_len, h_l_prod]
    exact prod_conj_implies_step_n R l h_l_conj
  · have h_area1_zero : area R w = 0 := by
      unfold area
      have h_set_empty : {n | IsProductOfNConjugates R n w} = ∅ := by
        by_contra!
        rw [mem_normalClosure_iff_isProductOfNConjugates_nonempty] at this
        exact h_mem this
      rw [h_set_empty]
      exact Nat.sInf_empty
    rw [h_area1_zero]
    have h_set_empty : {n | StepN R n w 1} = ∅ := step_empty R w h_mem
    unfold areaSteps
    rw [h_set_empty]
    simp

theorem area_eq_areaSteps {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  area R w = areaSteps R w := le_antisymm (area_le_areaSteps R w) (areaSteps_le_area R w)

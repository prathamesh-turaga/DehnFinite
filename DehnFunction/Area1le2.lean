import DehnFunction.Area1
import DehnFunction.Area2
import Mathlib.Data.Set.Basic

lemma sInf_le_sInf_of_subset {a b : Set ℕ} (ha : a.Nonempty) (h_sub : a ⊆ b) : sInf b ≤ sInf a := by

  apply le_csInf
  . exact ha
  . intro n hn_in_a
    have hn_in_b : n ∈ b := by
      exact h_sub hn_in_a
    exact Nat.sInf_le hn_in_b




theorem isConjugate_of_prod {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} {n: ℕ } (x y : FreeGroup G)
    (h : IsProductOfNConjugates R n y) (h_prod : x * y⁻¹ ∈ Group.conjugatesOfSet R ∨ y * x⁻¹ ∈ Group.conjugatesOfSet R) :
  IsProductOfNConjugates R (n+1) x:= by
    rcases h with ⟨ l_y, h_ly_conj, h_ly_len, h_ly_prod⟩
    cases h_prod with
    | inl h_conj =>
        use (x* y⁻¹) :: l_y
        aesop

    | inr h_conj =>
        use (y * x⁻¹)⁻¹ :: l_y
        aesop



lemma step_n_implies_IsProductOfNConjugates {G : Type*} [DecidableEq G] (R : Set (FreeGroup G))(n : ℕ):
    ∀ (w : FreeGroup G),(step_n R n w 1) →
  IsProductOfNConjugates R n w := by
  induction n with

  | zero =>
    intros w h_step
    simp [step_n] at h_step
    rw [h_step]
    use []
    simp

  | succ n ih =>
    intros w h_step
    unfold step_n at h_step
    cases n with
        | zero =>
            simp at h_step
            have h_conj: w ∈ Group.conjugatesOfSet R ∨ w⁻¹ ∈ Group.conjugatesOfSet R := by
              have h_w_id : w = w* 1⁻¹ := by
                simp
              have h_id_w : w⁻¹ = 1 * w⁻¹ := by
                simp
              nth_rw 1 [h_w_id, h_id_w]
              rw [← step_iff_conjugate w 1]
              exact h_step
            use [w]
            aesop
        | succ m =>
            simp at h_step
            rcases h_step with ⟨y, h_step_wy, h_stepn_y1⟩
            have h_y_prod: IsProductOfNConjugates R (m+1) y := by
                apply ih
                exact h_stepn_y1

            have h_prod: w * y⁻¹ ∈ Group.conjugatesOfSet R ∨ y * w⁻¹ ∈ Group.conjugatesOfSet R := by
                rw[ ← step_iff_conjugate]
                exact h_step_wy
            exact isConjugate_of_prod w y h_y_prod h_prod



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

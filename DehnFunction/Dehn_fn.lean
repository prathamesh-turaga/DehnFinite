import DehnFunction.Area_equiv
import Mathlib.Data.Real.Basic

noncomputable def dehn {G: Type*} [DecidableEq G] (R : Set (FreeGroup G)) (n: ℕ ): ℕ :=
  sSup (Area R '' {w | FreeGroup.norm w ≤ n})

theorem dehn_of_zero {G: Type*} [DecidableEq G] (R : Set (FreeGroup G)) :
  dehn R 0 = 0 := by
  unfold dehn
  simp_all only [nonpos_iff_eq_zero, FreeGroup.norm_eq_zero, Set.setOf_eq_eq_singleton, Set.image_singleton,
    csSup_singleton]
  exact Area.one R

theorem dehn_free_grp_is_zero {G: Type*} [DecidableEq G](n: ℕ) :
  dehn (∅: Set (FreeGroup G)) n = 0 := by
  unfold dehn
  by_cases h_non_empty: {w: FreeGroup G | FreeGroup.norm w ≤ n} = ∅
  . rw [h_non_empty]
    simp
  . have h_empty : Area ∅ '' {w: FreeGroup G | FreeGroup.norm w ≤ n} = {0} := by
      simp [Area.free_grp_eq_zero]
      ext x
      simp
      constructor
      . intro h_x_in
        simp[h_x_in]
      . intro h_x_eq_0
        simp[h_x_eq_0]
        have h_n_empty: {w: FreeGroup G | FreeGroup.norm w ≤ n}.Nonempty := by
          exact Set.nonempty_iff_ne_empty.mpr h_non_empty
        rw [Set.nonempty_def] at h_n_empty
        subst h_x_eq_0
        simp_all only [Set.mem_setOf_eq]
    rw [h_empty]
    simp

theorem fin_gen_words_finite {G : Type*} [DecidableEq G] [Finite G] (m : ℕ): {(w :FreeGroup G) | FreeGroup.norm w ≤ m}.Finite :=by
  expose_names
  unfold Set.Finite
  induction m with
  | zero =>
    simp
    exact Set.finite_singleton 1
  | succ m ih =>
    have h_decomp : {w: FreeGroup G | w.norm ≤ m + 1} = {w | w.norm ≤ m} ∪ {w | w.norm = m + 1} := by
      ext w
      simp_all only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_union]
      apply Iff.intro
      · intro a
        by_cases h_w_norm: FreeGroup.norm w = m+1
        . right
          exact h_w_norm
        . left
          have h_lt: w.norm < m+1 := by
            apply Nat.lt_of_le_of_ne
            . exact a
            .
              exact h_w_norm
          exact Nat.le_of_lt_succ h_lt

      · intro a
        cases a with
        | inl h =>
          exact Nat.le_add_right_of_le h
        | inr h_1 => simp_all only [le_refl]
    rw [h_decomp]
    apply Set.Finite.union
    . apply ih
    .
      sorry



theorem dehn_is_monotonic {G : Type*} [DecidableEq G] [Finite G] (R : Set (FreeGroup G)) {n m : ℕ} (h : n ≤ m) :
    dehn R n ≤ dehn R m := by
  expose_names
  unfold dehn

  refine csSup_le_csSup' ?_ ?_
  . apply Set.Finite.bddAbove
    apply Set.Finite.image
    apply fin_gen_words_finite
  . apply Set.image_subset

    intro w hw

    exact Nat.le_trans hw h

theorem dehn_is_linear_for_finite_groups
    {G : Type*} [DecidableEq G]

    [Finite G]
    (R : Set (FreeGroup G))

    [Finite R]

    [Finite (PresentedGroup R)]
    :
    ∃ c : ℝ ,
    ∀ n : ℕ, dehn R n ≤ c * n :=
by
  use dehn R (Nat.card (PresentedGroup R))
  intro n
  by_cases h_n_le_g: n ≤ Nat.card (PresentedGroup R)
  .

    by_cases h_n_0: n=0
    . rw [h_n_0]
      simp
      exact dehn_of_zero R
    . have h_le : dehn R (Nat.card (PresentedGroup R)) ≤ (dehn R (Nat.card (PresentedGroup R))) * n := by

        refine Nat.le_mul_of_pos_right (dehn R (Nat.card (PresentedGroup R))) ?_
        exact Nat.zero_lt_of_ne_zero h_n_0
      have h_le' : dehn R n ≤ dehn R (Nat.card (PresentedGroup R)) := by
        apply dehn_is_monotonic
        exact h_n_le_g
      have h_le'' : dehn R n ≤ (dehn R (Nat.card (PresentedGroup R))) * n := by
        exact Nat.le_trans h_le' h_le
      simp [h_le'']
      rw [← Nat.cast_mul]
      apply Nat.cast_le.mpr
      exact h_le''

  . sorry

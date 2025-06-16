import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

#check Group.conjugatesOfSet

/--
R - subset of FreeGroup G
w - word in FreeGroup G
n - natural number

This predicate states that the word `w` is a product of `n` conjugates of elements from the set `R`.

-/
def IsProductOfNConjugates₂ {G: Type*}(R : Set (FreeGroup G)) (n : ℕ) (w : FreeGroup G) : Prop :=
  ∃ (l : List {c // c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R}),
    l.length = n ∧ w = (l.map Subtype.val).prod

def IsProductOfNConjugates {G: Type*}(R : Set (FreeGroup G)) (n : ℕ) (w : FreeGroup G) : Prop :=
  ∃ (l : List (FreeGroup G)),(∀ c ∈ l, c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R) ∧
    l.length = n ∧ w = l.prod


inductive MyGen | a | b
   deriving DecidableEq, Repr

namespace MyGen



def a' : FreeGroup MyGen := FreeGroup.of a
def b' : FreeGroup MyGen := FreeGroup.of b

def R : Set (FreeGroup MyGen) := {a' * b' * a'⁻¹ * b'⁻¹}

def w : FreeGroup MyGen := a' * b' * a'⁻¹ * b'⁻¹

lemma dumb : IsProductOfNConjugates R 1 w := by
  have h_w_conj : w ∈ Group.conjugatesOfSet R := by
    unfold Group.conjugatesOfSet
    unfold conjugatesOf
    unfold IsConj
    unfold SemiconjBy
    simp
    use w
    constructor
    · exact Set.mem_singleton w
    . use 1
      simp
  use [w]
  constructor
  . intro c h_c_in
    rw [List.mem_singleton] at h_c_in
    left
    unfold R
    exact Set.mem_of_eq_of_mem h_c_in h_w_conj
  . constructor
    . simp
    . simp


end MyGen

--# Area Defintion 1

#check sInf {}

noncomputable def wordArea {G: Type*}(R : Set (FreeGroup G)) (w : FreeGroup G) : ℕ :=
  sInf {n | IsProductOfNConjugates R n w}


namespace MyGen

#check le_sInf

example : wordArea R w = 1 := by
  apply Nat.le_antisymm
  . apply Nat.sInf_le
    have h_prod : IsProductOfNConjugates R 1 w := dumb
    simp [h_prod]
  . unfold wordArea
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro h_area_0
    have h_inf_0 := Nat.sInf_eq_zero.mp h_area_0
    have h_nonempty : {n | IsProductOfNConjugates R n w}.Nonempty := by
      use 1
      exact dumb
    have h_0_in : 0 ∈ {n | IsProductOfNConjugates R n w} := by
      aesop

    have h_w_is_1 : w=1 :=by
      have h_prod_of_0 : IsProductOfNConjugates R 0 w := by
        aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop

    have h_w_ne_1 : w ≠ 1 := by
      rw [w]
      intro h_eq_1
      have h_norm_is_zero: FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) = 0 := by
        rw [h_eq_1]
        simp
      have h_norm_nonzero : FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) ≠ 0 := by
        native_decide
      rw[ h_norm_is_zero] at h_norm_nonzero
      contradiction
    contradiction

end MyGen


structure wordArea₂ {G: Type*} (R : Set (FreeGroup G)) (w : FreeGroup G) where
  n : ℕ
  isProd : IsProductOfNConjugates R n w
  isMin : ∀ m, m < n → ¬ IsProductOfNConjugates R m w

namespace MyGen

example: wordArea₂ R w := {
  n := 1,
  isProd := dumb,
  isMin := by
    intros m h_gt0 h_lt
    have h_m_0 : m = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Nat.le_of_lt_succ h_gt0
    rw [h_m_0] at h_lt
    have h_w_is_1 : w = 1 := by
      have h_prod_of_0 : IsProductOfNConjugates R 0 w := by
        aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop

    have h_w_ne_1 : w ≠ 1 := by
      rw [w]
      intro h_eq_1
      have h_norm_is_zero: FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) = 0 := by
        rw [h_eq_1]
        simp
      have h_norm_nonzero : FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) ≠ 0 := by
        native_decide
      rw[ h_norm_is_zero] at h_norm_nonzero
      contradiction
    contradiction

}

end MyGen

theorem wordArea_one {G : Type*} (R : Set (FreeGroup G)) : wordArea R 1 = 0 := by
  unfold wordArea
  refine Nat.sInf_eq_zero.mpr ?_
  left
  unfold IsProductOfNConjugates
  use []
  simp

--# Important Theorems for normal closure

theorem list_prod_inv {G: Type*}[Group G](l : List G) :
    (l.map Inv.inv).reverse.prod = (l.prod)⁻¹ := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>

    simp [List.prod_cons, mul_inv_rev, List.map_cons, List.reverse_cons,
               List.prod_append, List.prod_singleton]

    rw [ih]


theorem exists_list_of_mem_closure' {G : Type*} [Group G] {s : Set G} {x : G} :
    x ∈ Subgroup.closure s ↔ ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by

  constructor


  . intro hx

    induction hx using Subgroup.closure_induction with


    | mem g hg =>

      use [g]
      constructor
      .
        intro y hy_mem_list
        rw [List.mem_singleton.mp hy_mem_list]
        left
        exact hg
      .
        simp

    | one =>

      use []

      simp

    | mul x y _ _ ih_x ih_y =>

      rcases ih_x with ⟨l₁, h_l₁_prop, h_l₁_prod⟩
      rcases ih_y with ⟨l₂, h_l₂_prop, h_l₂_prod⟩

      use l₁ ++ l₂
      constructor
      .
        intro z hz_mem_list
        rw [List.mem_append] at hz_mem_list

        cases hz_mem_list with
        | inl h => exact h_l₁_prop z h
        | inr h => exact h_l₂_prop z h
      .

        simp [h_l₁_prod, h_l₂_prod]

    | inv x _ ih_x =>

      rcases ih_x with ⟨l, h_l_prop, h_l_prod⟩

      use (l.map Inv.inv).reverse
      constructor
      .
        intro y hy_mem_list

        rw [List.mem_reverse, List.mem_map] at hy_mem_list
        rcases hy_mem_list with ⟨z, hz_mem_l, rfl⟩
        simp
        exact Or.symm (h_l_prop z hz_mem_l)

      . rw [← h_l_prod]
        rw [list_prod_inv]


  . rintro ⟨l, h_l_prop, h_l_prod⟩

    have h_all_mem_closure : ∀ y ∈ l, y ∈ Subgroup.closure s := by
      intros y hy_mem_l

      cases h_l_prop y hy_mem_l with
      | inl h_y_in_s =>

        exact Subgroup.subset_closure h_y_in_s
      | inr h_y_inv_in_s =>
        have h_yinv : y⁻¹ ∈ Subgroup.closure s := by
          exact Subgroup.subset_closure h_y_inv_in_s
        exact (Subgroup.inv_mem_iff (Subgroup.closure s)).mp h_yinv

    rw [← h_l_prod]
    exact Subgroup.list_prod_mem (Subgroup.closure s) h_all_mem_closure



theorem mem_normalClosure_iff_prod_conj {G : Type*} [Group G](R : Set G) (w: G): w∈ Subgroup.normalClosure R ↔ ∃ (l: List G), (∀ x ∈ l, x∈ Group.conjugatesOfSet R ∨ x⁻¹ ∈ Group.conjugatesOfSet R) ∧ w = l.prod := by
  rw[Subgroup.normalClosure]
  rw[ exists_list_of_mem_closure']
  apply Iff.intro
  · intro a
    obtain ⟨w_1, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    apply Exists.intro
    · apply And.intro
      intro x a
      on_goal 2 => {rfl
      }
      simp_all only
  · intro a
    obtain ⟨w_1, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    apply Exists.intro
    · apply And.intro
      intro y a
      on_goal 2 => {rfl
      }
      simp_all only

theorem wordArea_eq_zero_iff {G : Type*} (R : Set (FreeGroup G)) (w : FreeGroup G) :
  wordArea R w = 0 ↔ w = 1 ∨ w ∉ Subgroup.normalClosure R := by
  constructor
  . intro h_area_0
    unfold wordArea at h_area_0
    apply Nat.sInf_eq_zero.mp at h_area_0
    rcases h_area_0 with ⟨n, h_prod⟩
    case mp.inr k =>
      right
      unfold IsProductOfNConjugates at k
      intro h_in_closure

      rw [mem_normalClosure_iff_prod_conj] at h_in_closure

      rcases h_in_closure with ⟨l, h_l_prop, h_w_prod⟩

      have h_is_in_set : l.length ∈ {n | ∃ l': List (FreeGroup G), (∀ c ∈ l', c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R) ∧ l'.length = n ∧ w = l'.prod} := by
        use l

      have h_not_in_set := Set.eq_empty_iff_forall_notMem.mp k
      specialize h_not_in_set l.length

      exact h_not_in_set h_is_in_set

    case mp.inl =>
      left
      rcases h_prod with ⟨l, h_prod⟩
      have h_l_empty : n = [] := by
        aesop
      rw [h_l_empty] at h_prod
      simp at h_prod
      exact h_prod
  . intro h
    cases h with
    | inl h_eq_1 =>
      unfold wordArea
      rw [h_eq_1]
      exact wordArea_one R
    | inr h_not_in =>
      unfold wordArea
      refine Nat.sInf_eq_zero.mpr ?_
      right
      unfold IsProductOfNConjugates
      apply Set.eq_empty_iff_forall_notMem.mpr

      intro n h_n_in_set
      rcases h_n_in_set with ⟨l, h_l_prop, h_n_len, h_w_prod⟩
      have h_in_closure : w ∈ Subgroup.normalClosure R := by

        refine (mem_normalClosure_iff_prod_conj R w).mpr ?_
        use l

      exact h_not_in h_in_closure

theorem conjugatesOfSet_of_empty {G: Type*} [Group G] :
  Group.conjugatesOfSet (∅: Set G) = ∅ := by
  unfold Group.conjugatesOfSet
  simp


theorem wordArea_free_grp_is_zero {G: Type*} [DecidableEq G] (w : FreeGroup G) :
  wordArea ∅ w = 0 := by
  rw [wordArea_eq_zero_iff]

  by_cases h_w_1 : w = 1
  . left
    exact h_w_1

  . right
    intro h_in_closure
    unfold Subgroup.normalClosure at h_in_closure
    rw [conjugatesOfSet_of_empty] at h_in_closure
    simp at h_in_closure
    contradiction




--# Dehn Functions

noncomputable def dehn {G: Type*} [DecidableEq G] (R : Set (FreeGroup G)) (n: ℕ ): ℕ :=
  sSup (wordArea R '' {w | FreeGroup.norm w ≤ n})

theorem dehn_of_zero {G: Type*} [DecidableEq G] (R : Set (FreeGroup G)) :
  dehn R 0 = 0 := by
  unfold dehn
  simp_all only [nonpos_iff_eq_zero, FreeGroup.norm_eq_zero, Set.setOf_eq_eq_singleton, Set.image_singleton,
    csSup_singleton]
  exact wordArea_one R

theorem dehn_free_grp_is_zero {G: Type*} [DecidableEq G](n: ℕ) :
  dehn (∅: Set (FreeGroup G)) n = 0 := by
  unfold dehn
  by_cases h_non_empty: {w: FreeGroup G | FreeGroup.norm w ≤ n} = ∅
  . rw [h_non_empty]
    simp
  .
    have h_empty : wordArea ∅ '' {w: FreeGroup G | FreeGroup.norm w ≤ n} = {0} := by
      simp [wordArea_free_grp_is_zero]
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
      sorry

  . sorry

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic

variable {G: Type*} (R : Set (FreeGroup G)) (n : ℕ) (w : FreeGroup G)


/--
R - subset of FreeGroup G
w - word in FreeGroup G
n - natural number

This predicate states that the word `w` is a product of `n` conjugates of elements from the set `R`.

-/


def IsProductOfNConjugates : Prop :=
  ∃ (l : List (FreeGroup G)),(∀ c ∈ l, c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R) ∧
    l.length = n ∧ w = l.prod

--# Area Defintion 1

noncomputable def Area : ℕ :=
  sInf {n | IsProductOfNConjugates R n w}

structure Area_struct where
  n : ℕ
  isProd : IsProductOfNConjugates R n w
  isMin : ∀ m, m < n → ¬ IsProductOfNConjugates R m w

inductive MyGen | a | b
   deriving DecidableEq, Repr

namespace MyGen

def a' : FreeGroup MyGen := FreeGroup.of a
def b' : FreeGroup MyGen := FreeGroup.of b

def rels : Set (FreeGroup MyGen) := {a' * b' * a'⁻¹ * b'⁻¹}

def wrd : FreeGroup MyGen := a' * b' * a'⁻¹ * b'⁻¹

lemma IsprodOfNConj_one : IsProductOfNConjugates rels 1 wrd := by
  have h_w_conj : wrd ∈ Group.conjugatesOfSet rels := by
    unfold Group.conjugatesOfSet
    unfold conjugatesOf
    unfold IsConj
    unfold SemiconjBy
    simp
    use wrd
    constructor
    · exact Set.mem_singleton wrd
    . use 1
      simp
  use [wrd]
  constructor
  . intro c h_c_in
    rw [List.mem_singleton] at h_c_in
    left
    unfold rels
    exact Set.mem_of_eq_of_mem h_c_in h_w_conj
  . constructor
    . simp
    . simp

example : Area rels wrd = 1 := by
  apply Nat.le_antisymm
  . apply Nat.sInf_le
    have h_prod : IsProductOfNConjugates rels 1 wrd := IsprodOfNConj_one
    simp [h_prod]
  . unfold Area
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro h_area_0
    have h_inf_0 := Nat.sInf_eq_zero.mp h_area_0
    have h_nonempty : {n | IsProductOfNConjugates rels n wrd}.Nonempty := by
      use 1
      exact IsprodOfNConj_one
    have h_0_in : 0 ∈ {n | IsProductOfNConjugates rels n wrd} := by aesop
    have h_w_is_1 : wrd=1 :=by
      have h_prod_of_0 : IsProductOfNConjugates rels 0 wrd := by aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop
    have h_w_ne_1 : wrd ≠ 1 := by
      rw [wrd]
      intro h_eq_1
      have h_norm_is_zero: FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) = 0 := by
        rw [h_eq_1]
        simp
      have h_norm_nonzero : FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) ≠ 0 := by
        native_decide
      rw[ h_norm_is_zero] at h_norm_nonzero
      contradiction
    contradiction

example: Area_struct rels wrd := {
  n := 1,
  isProd := IsprodOfNConj_one,
  isMin := by
    intros m h_gt0 h_lt
    have h_m_0 : m = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Nat.le_of_lt_succ h_gt0
    rw [h_m_0] at h_lt
    have h_w_is_1 : wrd = 1 := by
      have h_prod_of_0 : IsProductOfNConjugates rels 0 wrd := by aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop
    have h_w_ne_1 : wrd ≠ 1 := by
      rw [wrd]
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

theorem Area.one : Area R 1 = 0 := by
  unfold Area
  refine Nat.sInf_eq_zero.mpr ?_
  left
  unfold IsProductOfNConjugates
  use []
  simp

--# Important Theorems for normal closure

section normalClosureThms

variable [Group G]

lemma Group.list_prod_inv (l : List G) :
    (l.map Inv.inv).reverse.prod = (l.prod)⁻¹ := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    simp [List.prod_cons, mul_inv_rev, List.map_cons, List.reverse_cons,List.prod_append, ih]

lemma Group.conjugatesOfSet_of_empty :
  Group.conjugatesOfSet (∅: Set G) = ∅ := by
  simp [Group.conjugatesOfSet]

namespace Subgroup

theorem exists_list_of_mem_closure' {s : Set G} {x : G} :
    x ∈ Subgroup.closure s ↔ ∃ l : List G, (∀ y ∈ l, y ∈ s ∨ y⁻¹ ∈ s) ∧ l.prod = x := by
  constructor
  . intro hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      use [g]
      constructor
      . intro y hy_mem_list
        rw [List.mem_singleton.mp hy_mem_list]
        left
        exact hg
      . simp
    | one =>
      use []
      simp
    | mul x y _ _ ih_x ih_y =>
      rcases ih_x with ⟨l₁, h_l₁_prop, h_l₁_prod⟩
      rcases ih_y with ⟨l₂, h_l₂_prop, h_l₂_prod⟩
      use l₁ ++ l₂
      constructor
      . intro z hz_mem_list
        rw [List.mem_append] at hz_mem_list
        cases hz_mem_list with
        | inl h => exact h_l₁_prop z h
        | inr h => exact h_l₂_prop z h
      . simp [h_l₁_prod, h_l₂_prod]
    | inv x _ ih_x =>
      rcases ih_x with ⟨l, h_l_prop, h_l_prod⟩
      use (l.map Inv.inv).reverse
      constructor
      . intro y hy_mem_list
        rw [List.mem_reverse, List.mem_map] at hy_mem_list
        rcases hy_mem_list with ⟨z, hz_mem_l, rfl⟩
        simp
        exact Or.symm (h_l_prop z hz_mem_l)
      . rw [← h_l_prod]
        rw [Group.list_prod_inv]
  . rintro ⟨l, h_l_prop, h_l_prod⟩
    have h_all_mem_closure : ∀ y ∈ l, y ∈ Subgroup.closure s := by
      intros y hy_mem_l
      cases h_l_prop y hy_mem_l with
      | inl h_y_in_s =>
        exact subset_closure h_y_in_s
      | inr h_y_inv_in_s =>
        have h_yinv : y⁻¹ ∈ closure s := by
          exact subset_closure h_y_inv_in_s
        exact (Subgroup.inv_mem_iff (closure s)).mp h_yinv
    rw [← h_l_prod]
    exact Subgroup.list_prod_mem (closure s) h_all_mem_closure

theorem mem_normalClosure_iff_prod_conj (R : Set G) (w: G): w∈ Subgroup.normalClosure R ↔ ∃ (l: List G), (∀ x ∈ l, x∈ Group.conjugatesOfSet R ∨ x⁻¹ ∈ Group.conjugatesOfSet R) ∧ w = l.prod := by
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

end Subgroup
end normalClosureThms

namespace Area

theorem eq_zero_iff : Area R w = 0 ↔ w = 1 ∨ w ∉ Subgroup.normalClosure R := by
  constructor
  . intro h_area_0
    unfold Area at h_area_0
    apply Nat.sInf_eq_zero.mp at h_area_0
    rcases h_area_0 with ⟨n, h_prod⟩
    case mp.inr k =>
      right
      unfold IsProductOfNConjugates at k
      intro h_in_closure
      rw [Subgroup.mem_normalClosure_iff_prod_conj] at h_in_closure
      rcases h_in_closure with ⟨l, h_l_prop, h_w_prod⟩
      have h_is_in_set : l.length ∈ {n | ∃ l': List (FreeGroup G), (∀ c ∈ l', c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R) ∧ l'.length = n ∧ w = l'.prod} := by use l
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
      unfold Area
      rw [h_eq_1]
      exact one R
    | inr h_not_in =>
      unfold Area
      refine Nat.sInf_eq_zero.mpr ?_
      right
      unfold IsProductOfNConjugates
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n h_n_in_set
      rcases h_n_in_set with ⟨l, h_l_prop, h_n_len, h_w_prod⟩
      have h_in_closure : w ∈ Subgroup.normalClosure R := by
        refine (Subgroup.mem_normalClosure_iff_prod_conj R w).mpr ?_
        use l
      exact h_not_in h_in_closure

theorem free_grp_eq_zero :
  Area ∅ w = 0 := by
  rw [eq_zero_iff]
  by_cases h_w_1 : w = 1
  . left
    exact h_w_1

  . right
    intro h_in_closure
    unfold Subgroup.normalClosure at h_in_closure
    rw [Group.conjugatesOfSet_of_empty] at h_in_closure
    simp at h_in_closure
    contradiction

end Area

lemma PresentedGroup.IsProductOfNConjugates_one (hw : PresentedGroup.mk R w = 1) : ∃ n, IsProductOfNConjugates R n w := by
  rw [mk_eq_one_iff,Subgroup.mem_normalClosure_iff_prod_conj] at hw
  simp [IsProductOfNConjugates]
  obtain ⟨w_1, h⟩ := hw
  obtain ⟨left, right⟩ := h
  subst right
  use w_1

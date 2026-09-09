import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic
import DehnFunction.FiniteGroupIsPresented


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

--# area Defintion 1

noncomputable def area : ℕ :=
  sInf {n | IsProductOfNConjugates R n w}

structure AreaStruct where
  n : ℕ
  isProd : IsProductOfNConjugates R n w
  isMin : ∀ m, m < n → ¬ IsProductOfNConjugates R m w

inductive MyGen | a | b
   deriving DecidableEq, Repr

namespace MyGen

def a' : FreeGroup MyGen := FreeGroup.of a
def b' : FreeGroup MyGen := FreeGroup.of b

def rels : Set (FreeGroup MyGen) := {a' * b' * a'⁻¹ * b'⁻¹}

def word : FreeGroup MyGen := a' * b' * a'⁻¹ * b'⁻¹

lemma isProductOfNConjugates_one : IsProductOfNConjugates rels 1 word := by
  have h_w_conj : word ∈ Group.conjugatesOfSet rels := by
    unfold Group.conjugatesOfSet
    unfold conjugatesOf
    unfold IsConj
    unfold SemiconjBy
    simp
    use word
    constructor
    · exact Set.mem_singleton word
    . use 1
      simp
  use [word]
  constructor
  . intro c h_c_in
    rw [List.mem_singleton] at h_c_in
    left
    unfold rels
    exact Set.mem_of_eq_of_mem h_c_in h_w_conj
  . constructor
    . simp
    . simp

example : area rels word = 1 := by
  apply Nat.le_antisymm
  . apply Nat.sInf_le
    have h_prod : IsProductOfNConjugates rels 1 word := isProductOfNConjugates_one
    simp [h_prod]
  . unfold area
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro h_area_0
    have h_inf_0 := Nat.sInf_eq_zero.mp h_area_0
    have h_nonempty : {n | IsProductOfNConjugates rels n word}.Nonempty := by
      use 1
      exact isProductOfNConjugates_one
    have h_0_in : 0 ∈ {n | IsProductOfNConjugates rels n word} := by aesop
    have h_w_is_1 : word=1 :=by
      have h_prod_of_0 : IsProductOfNConjugates rels 0 word := by aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop
    have h_w_ne_1 : word ≠ 1 := by
      rw [word]
      intro h_eq_1
      have h_norm_is_zero: FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) = 0 := by
        rw [h_eq_1]
        simp
      have h_norm_nonzero : FreeGroup.norm ( a' * b' * a'⁻¹ * b'⁻¹) ≠ 0 := by
        native_decide
      rw[ h_norm_is_zero] at h_norm_nonzero
      contradiction
    contradiction

example: AreaStruct rels word := {
  n := 1,
  isProd := isProductOfNConjugates_one,
  isMin := by
    intros m h_gt0 h_lt
    have h_m_0 : m = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Nat.le_of_lt_succ h_gt0
    rw [h_m_0] at h_lt
    have h_w_is_1 : word = 1 := by
      have h_prod_of_0 : IsProductOfNConjugates rels 0 word := by aesop
      unfold IsProductOfNConjugates at h_prod_of_0
      aesop
    have h_w_ne_1 : word ≠ 1 := by
      rw [word]
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

theorem area.one_eq_zero : area R 1 = 0 := by
  unfold area
  refine Nat.sInf_eq_zero.mpr ?_
  left
  unfold IsProductOfNConjugates
  use []
  simp

--# Important Theorems for normal closure

section NormalClosureThms

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

theorem exists_list_of_mem_closure_aux {s : Set G} {x : G} :
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
  rw[ exists_list_of_mem_closure_aux]
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
end NormalClosureThms

namespace area

theorem eq_zero_iff : area R w = 0 ↔ w = 1 ∨ w ∉ Subgroup.normalClosure R := by
  constructor
  . intro h_area_0
    unfold area at h_area_0
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
      unfold area
      rw [h_eq_1]
      exact one_eq_zero R
    | inr h_not_in =>
      unfold area
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
  area ∅ w = 0 := by
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

end area

lemma PresentedGroup.isProductOfNConjugates_one (hw : PresentedGroup.mk R w = 1) : ∃ n, IsProductOfNConjugates R n w := by
  rw [mk_eq_one_iff,Subgroup.mem_normalClosure_iff_prod_conj] at hw
  simp [IsProductOfNConjugates]
  obtain ⟨w_1, h⟩ := hw
  obtain ⟨left, right⟩ := h
  subst right
  use w_1

#print area
#check (Group.IsFinitelyPresented.finite_group_is_finitely_presented _).invFun
#check ((Group.IsFinitelyPresented.finite_group_is_finitely_presented _)).invFun (1: (PresentedGroup (Group.IsFinitelyPresented.finite_group_relators _)))
#print QuotientGroup.lift_mk

lemma embed_into [Group G] [Finite G] (a: G) :   (FreeGroup.mk  [(a, true)]) = (FreeGroup.of a) := by aesop

lemma embed_into_false [Group G] [Finite G] (a: G) :   (FreeGroup.mk  [(a, false)]) = FreeGroup.of a⁻¹ := by sorry

#print map_one
/- rw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  simp only [finite_group_relators, Set.mem_setOf_eq]
  have h_rel := IsFiniteGroupRelator.mul (1: G) 1
  rw [mul_one] at h_rel
  simp at h_rel
  exact h_rel
-/

--True Case
lemma singleton_idword_is_id_true [Group G] [Finite G] (a: G)  (h: PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk  [(a, true)]) = 1) : a = 1:= by
  let f:= Group.IsFinitelyPresented.finite_group_relators G
  let e := Group.IsFinitelyPresented.finite_group_is_finitely_presented G
  rw[←e.apply_eq_iff_eq]
  unfold e
  unfold Group.IsFinitelyPresented.finite_group_is_finitely_presented
  simp[Group.IsFinitelyPresented.fromFiniteGroup]
  simp[embed_into] at h
  simp[PresentedGroup.of, h, Group.IsFinitelyPresented.presentedGroup_of_one]
-- Bind your isomorphism to a readable name

local notation "e" => Group.IsFinitelyPresented.finite_group_is_finitely_presented G

-- The Bridge Lemma: Connect the raw generator map to the bundled inverse isomorphism
lemma presented_of_eq_symm (g : G) [Group G] [Finite G] (a: G):
  PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.of g) = ((Group.IsFinitelyPresented.finite_group_is_finitely_presented G) g) := by
  unfold Group.IsFinitelyPresented.finite_group_is_finitely_presented
  simp
  unfold Group.IsFinitelyPresented.fromFiniteGroup
  unfold PresentedGroup.of
  rfl

  -- You prove this once using the definition of how `e.symm` is constructed,
  -- usually by `rfl` or `dsimp` depending on Mathlib's exact implementation.
lemma invRev_singleton_false  [Group G] [Finite G] (a: G) : FreeGroup.invRev [(a, false)] = [(a, true)] := by
 exact Eq.symm List.toList_toArray


lemma mk_singleton_true_eq_of  [Group G] [Finite G] (a: G) : FreeGroup.mk [(a, true)] = FreeGroup.of a := by
 exact embed_into a

#print Subgroup.mem_normalClosure_iff_prod_conj
#print Subgroup.subset_normalClosure
#print PresentedGroup.mk_eq_mk_of_mul_inv_mem
#print PresentedGroup.mk_eq_mk_of_inv_mul_mem
#print Subgroup.normalClosure
#print PresentedGroup.mk_eq_one_iff
#print QuotientGroup.eq_iff_div_mem

lemma fregrp [Group G] [Finite G] (a: G) : PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk [(a, false)]) = PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.of a⁻¹) := by
/-
a -> (a, true) -> inv -> (a, False) -> [(a, False)] -> [(a,False)] / ~_1 -> [(a,False)]/~_1 ->  [(a,False)]/~_1/~_2
-/
  group
  unfold FreeGroup.of
  have isInv:    (FreeGroup.mk [(a⁻¹, true)])*
  (FreeGroup.mk [(a, true)]) ∈ Subgroup.normalClosure (Group.IsFinitelyPresented.finite_group_relators G)
 := by
    rw[embed_into, embed_into]
    have rtemp (g: G): FreeGroup.of (g⁻¹ * g) = FreeGroup.of 1 := by
     group
    have ltemp: FreeGroup.of (1 * 1) = FreeGroup.of 1 := by
     group
    let rel₁ :=  ((FreeGroup.of a⁻¹) * (FreeGroup.of a)) * (FreeGroup.of 1)⁻¹
    let rel₂ :=  ((FreeGroup.of (1: G)) * (FreeGroup.of 1)) * (FreeGroup.of 1)⁻¹
    have expand:(FreeGroup.of a⁻¹) * (FreeGroup.of a)
      = rel₁ * rel₂ := by
          simp[rel₁, rel₂]
    have rel₁_in: rel₁ ∈  (Group.IsFinitelyPresented.finite_group_relators G) := by
      simp[rel₁, ←rtemp a]
      simp only [Group.IsFinitelyPresented.finite_group_relators, Set.mem_setOf_eq]
      have h_rel := Group.IsFinitelyPresented.IsFiniteGroupRelator.mul (a⁻¹ : G) (a : G)
      exact h_rel
    have rel₂_in: rel₂ ∈  (Group.IsFinitelyPresented.finite_group_relators G) := by
      simp[rel₂]
      simp only [Group.IsFinitelyPresented.finite_group_relators, Set.mem_setOf_eq]
      have h_rel := Group.IsFinitelyPresented.IsFiniteGroupRelator.mul (1 : G) (1 : G)
      simp at h_rel
      exact h_rel
    simp[expand]
    have rel_1_in_1: rel₁ ∈  Subgroup.normalClosure (Group.IsFinitelyPresented.finite_group_relators G) := by
      apply Subgroup.subset_normalClosure
      exact rel₁_in
    have rel_2_in_1: rel₂ ∈  Subgroup.normalClosure (Group.IsFinitelyPresented.finite_group_relators G) := by
      apply Subgroup.subset_normalClosure
      exact rel₂_in
    let R :=  (Group.IsFinitelyPresented.finite_group_relators G)
    apply (Subgroup.normalClosure R).mul_mem
    simp[R, rel_1_in_1]
    simp[R, rel_2_in_1]
  apply eq_of_mul_inv_eq_one
  rw [← map_inv, ← map_mul, PresentedGroup.mk_eq_one_iff]
  have hmem := Subgroup.inv_mem (Subgroup.normalClosure (Group.IsFinitelyPresented.finite_group_relators G)) isInv
  simpa [FreeGroup.invRev, zpow_neg_one] using hmem

lemma singleton_idword_is_id_false [Group G] [Finite G] (a: G)  (h: PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk  [(a, false)]) = 1) : a = 1 := by
  rw[←((Group.IsFinitelyPresented.finite_group_is_finitely_presented G)).apply_eq_iff_eq]
  unfold Group.IsFinitelyPresented.finite_group_is_finitely_presented
  simp[Group.IsFinitelyPresented.fromFiniteGroup]
  simp[embed_into_false] at h
  unfold PresentedGroup.of
  have h_inv := congr_arg (Group.IsFinitelyPresented.toFiniteGroup G) h
  unfold PresentedGroup.mk at h_inv
  simp at h_inv
  push_cast at h

  have isone: ((Group.IsFinitelyPresented.finite_group_is_finitely_presented G)).invFun (1: (PresentedGroup (Group.IsFinitelyPresented.finite_group_relators G)))=  1 := by
    simp
  have hssd: ((Group.IsFinitelyPresented.finite_group_is_finitely_presented G)).invFun (PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk  [(a, false)])) = a⁻¹ := by

    sorry
  simp[h] at hssd
  sorry

lemma PresentedGroup.area_of_finite_bounded [Group G] (w: List (G × Bool)) (h: PresentedGroup.mk (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk  w) = 1 ) (h_n: w.length = n):
area  (Group.IsFinitelyPresented.finite_group_relators G) (FreeGroup.mk w) <= n + 1  := by
  induction n generalizing w with
  | zero =>
      have w_trivial: w = [] := by
        aesop
      have empty_is_identity: (FreeGroup.mk []) = (1 : FreeGroup G) := by
        aesop
      simp[empty_is_identity, w_trivial, area.one_eq_zero]
  | succ n ih =>
      cases n with
      | zero =>
        simp_all
        have exists_elem: ∃ a, w = [(a, false)] ∨ w = [(a, true)] := by sorry
        rcases exists_elem with ⟨ a, ha⟩
        rcases ha with hal | har
        · sorry
        · sorry

      | succ n => sorry

 /- | nil =>
    have g: (FreeGroup.mk []) = (1 : FreeGroup G) := by
      aesop
    simp[g, area.one_eq_zero]
  | cons x xs ih =>
     cases xs
     · simp
       sorry
     · sorry

  sorry
-/

 --∃ m,   (IsProductOfNConjugates (Group.IsFinitelyPresented.finite_group_relators G) (m) (FreeGroup.mk w)) ∧ (m ≤ w.length + 1) := by
/-induction w with
| nil =>
   have w_is_one:(FreeGroup.mk w = 1) := by sorry
   have, ∃m, (IsProductOfNConjugates (Group.IsFinitelyPresented.finite_group_relators G) (m) (FreeGroup.mk w)) ∧ (m ≤ w.length + 1) := by sorry
| cons x xs ih => sorry
-/

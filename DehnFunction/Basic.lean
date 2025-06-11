import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Reduce


#check Group.conjugatesOfSet

/--
R - subset of FreeGroup G
w - word in FreeGroup G
n - natural number

This predicate states that the word `w` is a product of `n` conjugates of elements from the set `R`.

-/
def IsProductOfNConjugates {G: Type*}(R : Set (FreeGroup G)) (n : ℕ) (w : FreeGroup G) : Prop :=
  ∃ (l : List {c // c ∈ Group.conjugatesOfSet R}),
    l.length = n ∧ w = (l.map Subtype.val).prod

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
  use [{val := a' * b' * a'⁻¹ * b'⁻¹, property :=by exact h_w_conj}]
  constructor
  · rfl
  · rfl

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
      rcases h_0_in with ⟨l, h_len, h_prod⟩
      have h_l_empty : l = [] := by
        exact List.eq_nil_iff_length_eq_zero.mpr h_len
      rw [h_l_empty] at h_prod
      simp at h_prod
      exact h_prod
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
      unfold IsProductOfNConjugates at h_lt
      rcases h_lt with ⟨l, h_len, h_prod⟩
      have h_l_empty : l = [] := by
        exact List.eq_nil_iff_length_eq_zero.mpr h_len
      rw [h_l_empty] at h_prod
      simp at h_prod
      exact h_prod
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


--# Dehn Functions

noncomputable def dehnFunction {G: Type*} [DecidableEq G] (R : Set (FreeGroup G)) (n: ℕ ): ℕ :=
  sSup (wordArea R '' {w | FreeGroup.norm w ≤ n})
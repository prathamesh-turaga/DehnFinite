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
/-
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
        apply (step_iff_conjugate w 1).mpr ?_
        simp
        simp [th, sc]
        simp [List.length_eq_one_iff] at sc
        rcases sc with ⟨a, inlist⟩
        specialize fs a; simp [inlist] at fs
        simp [inlist]; simp [inlist] at th
        exact fs
      · expose_names
        simp at heq; rw [<-heq] at h_1
        rcases isprconj with ⟨ll, hypo, len_ll, w_is_prod⟩
        have : ll ≠ [] := by exact List.ne_nil_of_length_eq_add_one len_ll
        use List.prod (ll.tail)
        constructor

        apply (step_iff_conjugate w (List.prod (ll.tail))).mpr ?_
        have that : ll = ll.dropLast ++ [ll.getLast this] := by exact Eq.symm (List.dropLast_concat_getLast this)


        have that₂ {χ : Type*} [DecidableEq χ]  : ∀ (A B : List (FreeGroup χ)), List.prod (A++B) = (List.prod A) * (List.prod B) := by exact
          fun A B ↦ List.prod_append
        -- prod of appended lists is product of individual list prods


        have that₃ : List.prod ll = List.prod (ll.dropLast) * List.prod ([ll.getLast this]) := by
          calc
            ll.prod = List.prod (ll.dropLast ++ [ll.getLast this]) := by exact congrArg List.prod that
            _  = (List.prod ll.dropLast) * (List.prod [ll.getLast this]) := by exact List.prod_append
        simp [w_is_prod]
        have that₄ : ll = (ll.head this) :: ll.tail := by exact Eq.symm (List.head_cons_tail ll this)
        have that₅ : ll.prod = [ll.head this].prod * ll.tail.prod := by calc
          ll.prod = ([ll.head this] ++ ll.tail).prod := by exact congrArg List.prod that₄
          _ = [ll.head this].prod * ll.tail.prod := by exact List.prod_append
        simp [that₅]
        have head_in_ll_so : (ll.head this) ∈ ll := by exact List.head_mem this
        have head_in_conj : (ll.head this) ∈ Group.conjugatesOfSet rel_set ∨ (ll.head this)⁻¹ ∈ Group.conjugatesOfSet rel_set := by exact hypo (ll.head this) head_in_ll_so
        simp [head_in_conj]

        rw [<-heq]-/


lemma A_two_le_A_one' {α : Type*} {n : ℕ} [DecidableEq α] (rel_set : Set (FreeGroup α)) (w : FreeGroup α) (h : (wordArea rel_set w = n)) : Area2 rel_set w ≤ n := by
  unfold Area2
  apply Nat.sInf_le
  simp
  have isprconj : ∃ (l : List (FreeGroup α)),(∀ c ∈ l, c ∈ Group.conjugatesOfSet rel_set ∨ c⁻¹ ∈ Group.conjugatesOfSet rel_set) ∧
  l.length = n ∧ w = l.prod := by sorry
  induction n with
  | zero =>
    unfold step_n
    aesop
  | succ n _ =>
    expose_names
    simp at h_1
    rcases isprconj with ⟨ll, inconj, len_ll, prod_ll⟩
    have EZ : n+1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
    unfold step_n
    cases n + 1
    · sorry
    · sorry

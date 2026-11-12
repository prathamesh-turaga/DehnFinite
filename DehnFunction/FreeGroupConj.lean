/-
Copyright (c) 2026 Ajun Sheth, Omar, Vivek Rajesh Joshi, T V H Prathamesh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ajun Sheth, Omar, Vivek Rajesh Joshi, T V H Prathamesh
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Conjugacy in free groups

Two elements of a free group are conjugate if and only if the cyclic reductions of their reduced
words are cyclic permutations of each other. As a consequence, conjugacy in `FreeGroup α` is
decidable when `α` has decidable equality.

## Main results

* `FreeGroup.isConj_iff_isRotated`: `g` and `h` are conjugate iff
  `reduceCyclically g.toWord ~r reduceCyclically h.toWord`.
* `FreeGroup.isConj_mk_iff`: the same criterion for elements given by (not necessarily reduced)
  words.
* `FreeGroup.instDecidableRelIsConj`: conjugacy in a free group is decidable.
-/

open List

namespace FreeGroup

variable {α : Type*} {L L₁ L₂ : List (α × Bool)}

/-- Cyclically permuting a word gives a conjugate element. -/
theorem isConj_mk_of_isRotated (h : L₁ ~r L₂) : IsConj (mk L₁) (mk L₂) := by
  obtain ⟨n, rfl⟩ := h
  rw [rotate_eq_drop_append_take_mod, isConj_iff]
  refine ⟨(mk (L₁.take (n % L₁.length)))⁻¹, ?_⟩
  have h₁ : mk L₁ = mk (L₁.take (n % L₁.length)) * mk (L₁.drop (n % L₁.length)) := by
    rw [mul_mk, take_append_drop]
  rw [h₁, ← mul_mk]
  group

theorem isCyclicallyReduced_iff_isReduced_append_self :
    IsCyclicallyReduced L ↔ IsReduced (L ++ L) := by
  simp [isCyclicallyReduced_iff, IsReduced, isChain_append]

theorem isCyclicallyReduced_append_comm :
    IsCyclicallyReduced (L₁ ++ L₂) ↔ IsCyclicallyReduced (L₂ ++ L₁) := by
  suffices ∀ {L₁ L₂ : List (α × Bool)}, IsCyclicallyReduced (L₁ ++ L₂) →
      IsCyclicallyReduced (L₂ ++ L₁) from ⟨this, this⟩
  intro L₁ L₂ h
  rw [isCyclicallyReduced_iff_isReduced_append_self] at h ⊢
  by_cases hn : L₁ ++ L₂ = []
  · simp_all
  exact (h.append_overlap h hn).infix ⟨L₁, L₂, by simp⟩

theorem IsCyclicallyReduced.rotate (h : IsCyclicallyReduced L) (n : ℕ) :
    IsCyclicallyReduced (L.rotate n) := by
  rw [rotate_eq_drop_append_take_mod, isCyclicallyReduced_append_comm, take_append_drop]
  exact h

theorem IsCyclicallyReduced.of_isRotated (h : IsCyclicallyReduced L₁) (hr : L₁ ~r L₂) :
    IsCyclicallyReduced L₂ := by
  obtain ⟨n, rfl⟩ := hr
  exact h.rotate n

variable [DecidableEq α]

theorem IsCyclicallyReduced.reduceCyclically_eq (h : IsCyclicallyReduced L) :
    reduceCyclically L = L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton => simp
  | cons_append a L b _ =>
    rw [reduceCyclically.cons_append, if_neg]
    · simp
    · rw [← cons_append, isCyclicallyReduced_cons_append_iff] at h
      rintro ⟨h₁, h₂⟩
      rw [h.2 h₁] at h₂
      cases a.2 <;> simp at h₂

theorem reduceCyclically.append_append_invRev (L₁ L₂ : List (α × Bool)) :
    reduceCyclically (L₁ ++ L₂ ++ invRev L₁) = reduceCyclically L₂ := by
  induction L₁ with
  | nil => simp
  | cons a L₁ ih =>
    have : a :: L₁ ++ L₂ ++ invRev (a :: L₁) =
        a :: ((L₁ ++ L₂ ++ invRev L₁) ++ [(a.1, !a.2)]) := by
      simp [invRev]
    rw [this, reduceCyclically.cons_append, if_pos (by simp), ih]

/-- Every word is conjugate to its cyclic reduction. -/
theorem isConj_mk_reduceCyclically (L : List (α × Bool)) :
    IsConj (mk (reduceCyclically L)) (mk L) := by
  rw [isConj_iff]
  refine ⟨mk (reduceCyclically.conjugator L), ?_⟩
  conv_rhs => rw [← reduceCyclically.conj_conjugator_reduceCyclically L]
  rw [inv_mk, mul_mk, mul_mk]

private theorem cancel_iff {x y : α × Bool} :
    (x.1 = y.1 → x.2 = y.2) ↔ y ≠ (x.1, !x.2) := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  by_cases h : x₁ = y₁
  · subst h; cases x₂ <;> cases y₂ <;> simp
  · simp [h, Ne.symm h]

private theorem cancel_iff' {x y : α × Bool} : (y.1 = x.1 → y.2 = !x.2) ↔ y ≠ x := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  by_cases h : y₁ = x₁
  · subst h; cases x₂ <;> cases y₂ <;> simp
  · simp [h]

omit [DecidableEq α] in
private theorem isReduced_concat {a : α × Bool} (hL : IsReduced L)
    (h : ∀ b ∈ L.getLast?, b.1 = a.1 → b.2 = a.2) : IsReduced (L ++ [a]) := by
  rw [IsReduced, isChain_append]
  exact ⟨hL, isChain_singleton a, by simpa using h⟩

private theorem toWord_mk_of_isReduced (h : IsReduced L) : (mk L).toWord = L := by
  rw [toWord_mk, h.reduce_eq]

/-- Conjugating by a single letter changes the cyclic reduction only up to rotation. -/
theorem reduceCyclically_toWord_conj_mk_singleton (x : α × Bool) (g : FreeGroup α) :
    reduceCyclically (mk [x] * g * (mk [x])⁻¹).toWord ~r reduceCyclically g.toWord := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, IsReduced u ∧ mk u = g :=
    ⟨g.toWord, isReduced_toWord, mk_toWord⟩
  rw [toWord_mk_of_isReduced hu]
  set x' : α × Bool := (x.1, !x.2) with hx'
  have hinv : (mk [x])⁻¹ = mk [x'] := by simp [inv_mk, invRev, hx']
  rw [hinv]
  have hcancel {y : α × Bool} : (x.1 = y.1 → x.2 = y.2) ↔ y ≠ x' := cancel_iff
  have hcancel' {y : α × Bool} : (y.1 = x'.1 → y.2 = x'.2) ↔ y ≠ x := by
    rw [hx']; exact cancel_iff' (x := x)
  have hxx' : x ≠ x' := by simp [hx', Prod.ext_iff]
  rcases u.eq_nil_or_concat' with rfl | ⟨v, last, rfl⟩
  · rw [← hinv, show mk ([] : List (α × Bool)) = 1 from rfl, mul_one, mul_inv_cancel]
    simp
  rcases v with _ | ⟨first, v⟩
  · -- `u` is a single letter.
    simp only [nil_append] at hu ⊢
    by_cases hl : last = x'
    · subst last
      rw [show mk [x] * mk [x'] * mk [x'] = mk [x'] by rw [← hinv]; group]
      simp
    by_cases hl' : last = x
    · subst last
      rw [show mk [x] * mk [x] * mk [x'] = mk [x] by rw [← hinv]; group]
      simp
    have hW : IsReduced [x, last, x'] := by
      simp only [isReduced_cons_cons, IsReduced.singleton, and_true]
      exact ⟨hcancel.2 hl, hcancel'.2 hl'⟩
    rw [mul_mk, mul_mk, toWord_mk_of_isReduced (by simpa using hW)]
    rw [show [x] ++ [last] ++ [x'] = x :: ([last] ++ [x']) by rfl, reduceCyclically.cons_append,
      if_pos (by simp [hx'])]
  · -- `u = first :: v ++ [last]` has at least two letters.
    have hred : IsReduced (first :: v) := hu.infix ⟨[], [last], by simp⟩
    have hred' : IsReduced (v ++ [last]) := hu.infix ⟨[first], [], by simp⟩
    by_cases hf : first = x'
    · subst first
      by_cases hl : last = x
      · -- Both ends cancel: the result is the middle `v`.
        subst last
        have hv : IsReduced v := hu.infix ⟨[x'], [x], by simp⟩
        rw [show mk [x] * mk (x' :: v ++ [x]) * mk [x'] = mk v by
          rw [show x' :: v ++ [x] = [x'] ++ v ++ [x] by rfl, ← mul_mk, ← mul_mk, ← hinv]
          group]
        rw [toWord_mk_of_isReduced hv, cons_append, reduceCyclically.cons_append,
          if_pos (by simp [hx'])]
      · -- Only the first letter cancels: the result is a rotation of `u`.
        have hcyc : IsCyclicallyReduced (x' :: v ++ [last]) := by
          rw [cons_append, ← cons_append, isCyclicallyReduced_cons_append_iff]
          exact ⟨hu, hcancel'.2 hl⟩
        have hrot : x' :: v ++ [last] ~r v ++ [last] ++ [x'] := by
          rw [cons_append]; exact (isRotated_concat _ _).symm
        rw [show mk [x] * mk (x' :: v ++ [last]) * mk [x'] = mk (v ++ [last] ++ [x']) by
          rw [show x' :: v ++ [last] = [x'] ++ (v ++ [last]) by rfl, ← mul_mk, ← mul_mk,
            ← mul_mk, ← hinv]; simp only [← mul_mk]; group]
        rw [toWord_mk_of_isReduced (hcyc.of_isRotated hrot).isReduced,
          (hcyc.of_isRotated hrot).reduceCyclically_eq, hcyc.reduceCyclically_eq]
        exact hrot.symm
    · by_cases hl : last = x
      · -- Only the last letter cancels: the result is a rotation of `u`.
        subst last
        have hcyc : IsCyclicallyReduced (first :: v ++ [x]) := by
          rw [cons_append, ← cons_append, isCyclicallyReduced_cons_append_iff]
          refine ⟨hu, fun h₁ ↦ ?_⟩
          exact (hcancel (y := first)).2 hf h₁
        have hrot : first :: v ++ [x] ~r x :: first :: v := isRotated_concat _ _
        rw [show mk [x] * mk (first :: v ++ [x]) * mk [x'] = mk (x :: first :: v) by
          rw [show x :: first :: v = [x] ++ (first :: v) by rfl, ← mul_mk, ← mul_mk,
            ← hinv]; group]
        rw [toWord_mk_of_isReduced (hcyc.of_isRotated hrot).isReduced,
          (hcyc.of_isRotated hrot).reduceCyclically_eq, hcyc.reduceCyclically_eq]
        exact hrot.symm
      · -- Nothing cancels: conjugating adds a cancelling outer pair.
        have hW : IsReduced (x :: (first :: v ++ [last] ++ [x'])) := by
          have h₁ : IsReduced (x :: (first :: v ++ [last])) := by
            rw [cons_append, isReduced_cons_cons]
            exact ⟨hcancel.2 hf, hu⟩
          have h₂ : IsReduced (first :: v ++ [last] ++ [x']) :=
            isReduced_concat hu (by
              intro b hb
              rw [show (first :: v ++ [last]).getLast? = some last by
                exact getLast?_concat ..] at hb
              simp only [Option.mem_def, Option.some.injEq] at hb
              subst hb
              exact hcancel'.2 hl)
          exact IsReduced.append_overlap (L₁ := [x]) h₁ h₂ (by simp)
        rw [mul_mk, mul_mk, show [x] ++ (first :: v ++ [last]) ++ [x'] =
          x :: (first :: v ++ [last] ++ [x']) by rfl, toWord_mk_of_isReduced hW,
          reduceCyclically.cons_append, if_pos (by simp [hx'])]

/-- Conjugation changes the cyclic reduction of the reduced word only up to rotation. -/
theorem reduceCyclically_toWord_conj (c g : FreeGroup α) :
    reduceCyclically (c * g * c⁻¹).toWord ~r reduceCyclically g.toWord := by
  obtain ⟨w, rfl⟩ : ∃ w, mk w = c := ⟨c.toWord, mk_toWord⟩
  induction w with
  | nil => simpa [show mk ([] : List (α × Bool)) = 1 from rfl] using IsRotated.refl _
  | cons x w ih =>
    have : mk (x :: w) * g * (mk (x :: w))⁻¹ =
        mk [x] * (mk w * g * (mk w)⁻¹) * (mk [x])⁻¹ := by
      rw [show x :: w = [x] ++ w by rfl, ← mul_mk]
      group
    rw [this]
    exact (reduceCyclically_toWord_conj_mk_singleton x _).trans ih

/-- **Conjugacy criterion for free groups**: two elements are conjugate iff the cyclic reductions
of their reduced words are cyclic permutations of each other. -/
theorem isConj_iff_isRotated {g h : FreeGroup α} :
    IsConj g h ↔ reduceCyclically g.toWord ~r reduceCyclically h.toWord := by
  refine ⟨fun hc ↦ ?_, fun hr ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    exact (reduceCyclically_toWord_conj c g).symm
  · have hg := isConj_mk_reduceCyclically g.toWord
    have hh := isConj_mk_reduceCyclically h.toWord
    rw [mk_toWord] at hg hh
    exact (hg.symm.trans (isConj_mk_of_isRotated hr)).trans hh

/-- The conjugacy criterion for elements given by (not necessarily reduced) words. -/
theorem isConj_mk_iff :
    IsConj (mk L₁) (mk L₂) ↔
      reduceCyclically (reduce L₁) ~r reduceCyclically (reduce L₂) := by
  simp only [isConj_iff_isRotated, toWord_mk]

instance instDecidableRelIsConj : DecidableRel (IsConj : FreeGroup α → FreeGroup α → Prop) :=
  fun _ _ ↦ decidable_of_iff _ isConj_iff_isRotated.symm

end FreeGroup

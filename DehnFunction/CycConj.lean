import DehnFunction.Area1
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
Cyclic reduction of words in free groups. We use Mathlib's `FreeGroup.reduceCyclically`
(strip matching first/last letter pairs) and `FreeGroup.reduceCyclically.conjugator`.
-/

namespace FreeGroup

variable {α : Type*} [DecidableEq α] (L : List (α × Bool)) (w : FreeGroup α)

namespace reduceCyclically

/-- `L` splits as `U ++ reduceCyclically L ++ V` with `V ++ U` trivial. -/
theorem property (L : List (α × Bool)) :
    ∃ (U V : List (α × Bool)), L = U ++ reduceCyclically L ++ V ∧ FreeGroup.mk (V ++ U) = 1 :=
  ⟨conjugator L, invRev (conjugator L), (conj_conjugator_reduceCyclically L).symm, by
    rw [← mul_mk, ← inv_mk, inv_mul_cancel]⟩

lemma conj_singleton (a : α) (b : Bool) :
    reduceCyclically ((a, b) :: L ++ [(a, !b)]) = reduceCyclically L := by
  rw [List.cons_append, reduceCyclically.cons_append]
  simp

theorem conj :
    ∀ (P Q: List (α × Bool)), reduceCyclically (P ++ Q ++ FreeGroup.invRev P) = reduceCyclically (Q) := by
    intro P
    induction P with
    | nil =>
      intro Q
      simp
    | cons head tail ih =>
      intro Q
      rw[FreeGroup.invRev_cons]
      rw[List.cons_append]
      rw[← List.append_assoc (head :: (tail ++ Q)) (FreeGroup.invRev tail) (FreeGroup.invRev [head])]
      have h_list_rw: head :: (tail ++ Q) ++ FreeGroup.invRev tail = head :: (tail ++ Q ++ FreeGroup.invRev tail) := by
        simp [List.append_assoc]
      rw[h_list_rw]
      have h_head_eq: head = (head.1, head.2) := by
        simp
      have h_head_inv: FreeGroup.invRev [head] = [(head.1, !head.2)] := by
        simp [FreeGroup.invRev]
      rw [h_head_eq, h_head_inv]
      rw [conj_singleton (tail ++ Q ++ FreeGroup.invRev tail) head.1 head.2]
      rw [ih (Q)]

theorem length_le (L : List (α × Bool)) :
    (reduceCyclically L).length ≤ L.length := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton => simp
  | cons_append a L b ih =>
    rw [reduceCyclically.cons_append]
    split <;> simp
    omega

theorem pair (a b : α × Bool) :
    reduceCyclically [a, b] = if b.1 = a.1 ∧ (!b.2) = a.2 then [] else [a, b] := by
  simpa using reduceCyclically.cons_append (a := a) (b := b) []

end reduceCyclically

def CycRed := FreeGroup.mk (reduceCyclically (FreeGroup.toWord w))
--Cyclically reduces a freeword

def CyclicPermutationsOfRelators (R : Set (FreeGroup α)) : Set (FreeGroup α) :=
  ⋃ r ∈ R,
    { elem |
      ∃ word ∈ (FreeGroup.toWord r).cyclicPermutations,
      elem = FreeGroup.mk word
    }

theorem cycRed_is_a_cyclic_permutation (y : FreeGroup α) :
  CycRed y ∈ CyclicPermutationsOfRelators {y} := by
  let L := FreeGroup.toWord y
  let M := reduceCyclically L
  unfold CyclicPermutationsOfRelators
  simp
  unfold CycRed
  have h_prop := reduceCyclically.property L
  rcases h_prop with ⟨U, V, h_decomp, h_vu_is_one⟩
  let p := M ++ V ++ U
  use p
  constructor
  · change p ~r L
    use (M ++ V).length
    dsimp [p]
    rw[h_decomp]
    have h_M_def: reduceCyclically L = M := rfl
    rw [h_M_def]
    rw [List.rotate_eq_drop_append_take]
    . simp
      have h_assoc: M ++ (V ++ U) = (M ++ V) ++ U := by
        simp
      rw [h_assoc]
      rw [List.take_append_of_le_length (by simp)]
      simp
    . simp
  · dsimp [p]
    change FreeGroup.mk M = FreeGroup.mk (M ++ V ++ U)
    apply Eq.symm
    calc
      FreeGroup.mk (M ++ V ++ U) = FreeGroup.mk M * FreeGroup.mk (V ++ U) := by
        simp
      _ = FreeGroup.mk M * 1 := by
        rw[h_vu_is_one]
      _ = FreeGroup.mk M := by
        simp


def IsUncycled (L : List (α × Bool)) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | x :: y :: ys =>
    let xs := y :: ys
    let last := xs.getLast (by simp)
    let middle := xs.dropLast
    if x.1 = last.1 ∧ x.2 ≠ last.2 then
      false
    else
      true

theorem isUncycled_cons_append (a b : α × Bool) (M : List (α × Bool)) :
    IsUncycled (a :: (M ++ [b])) ↔ ¬(b.1 = a.1 ∧ (!b.2) = a.2) := by
  obtain ⟨y, ys, h⟩ : ∃ y ys, M ++ [b] = y :: ys := by cases M <;> simp
  have hl : (y :: ys).getLast (by simp) = b := by simp [← h]
  rw [h]
  unfold IsUncycled
  simp only [hl]
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  by_cases h1 : a1 = b1 <;> cases a2 <;> cases b2 <;> simp [h1, Ne.symm, eq_comm (a := b1)]

theorem isUncycled_iff : IsUncycled L ↔ reduceCyclically L = L := by
  induction L using List.bidirectionalRec with
  | nil => simp [IsUncycled]
  | singleton x => simp [IsUncycled]
  | cons_append a M b _ =>
    rw [isUncycled_cons_append, reduceCyclically.cons_append]
    split
    · next h =>
      have hne : reduceCyclically M ≠ a :: (M ++ [b]) := fun heq => by
        have := reduceCyclically.length_le M
        rw [heq] at this
        simp at this
      simp [h, hne]
    · next h =>
      simp only [List.cons_append, iff_true]
      exact h

theorem reduceCyclically.isConj_to_self (L : List (α × Bool)) :
    IsConj (FreeGroup.mk L) (FreeGroup.mk (reduceCyclically L)) := by
  have h := conj_conjugator_reduceCyclically L
  rw [isConj_comm, isConj_iff]
  refine ⟨mk (conjugator L), ?_⟩
  conv_rhs => rw [← h]
  rw [inv_mk, mul_mk, mul_mk]

theorem word_conj_cycRed : IsConj w (CycRed w) := by
  unfold CycRed
  let L := FreeGroup.toWord w
  have h_L_w : FreeGroup.mk L = w := by
    dsimp[L]
    exact FreeGroup.mk_toWord
  nth_rw 1 [← h_L_w]
  change IsConj (FreeGroup.mk L) (FreeGroup.mk (reduceCyclically L))
  apply reduceCyclically.isConj_to_self L

omit [DecidableEq α] in
theorem cycPerm_is_conj :
  ∀ l₁ l₂ : List (α × Bool), l₁ ~r l₂ → IsConj (FreeGroup.mk l₁) (FreeGroup.mk l₂)   := by
  intros l₁ l₂ h_rot
  rw [List.isRotated_iff_mod] at h_rot
  rcases h_rot with ⟨n, h_n, h_e⟩
  unfold IsConj SemiconjBy
  let A := l₁.take n
  let B := l₁.drop n
  have h_l1: l₁ = A ++ B := (List.take_append_drop n l₁).symm
  use ⟨ (FreeGroup.mk (A))⁻¹, FreeGroup.mk (A),
        by exact mul_eq_one_iff_eq_inv.mpr rfl,
        by exact mul_eq_one_iff_inv_eq.mpr rfl⟩
  rw[← h_e]
  rw [List.rotate_eq_drop_append_take]
  . change (FreeGroup.mk A)⁻¹ * FreeGroup.mk l₁ =
    FreeGroup.mk (List.drop n l₁ ++ List.take n l₁) *
      (FreeGroup.mk A)⁻¹
    have h_A: A = l₁.take n := by
      rfl
    have h_B: B = List.drop n l₁ := by
      rfl
    rw [← h_A, ← h_B]
    rw[h_l1]
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    group
  . exact h_n

theorem conj_if_cyc (r : FreeGroup α): (∃ (word: List (α × Bool)), word ~r (FreeGroup.toWord r) ∧ (CycRed w) = FreeGroup.mk word) → (∃ (g: FreeGroup α), w = g * r * g⁻¹)
   := by
    intro h_exist
    rcases h_exist with ⟨p, h_p_r, h_cyc⟩
    have h_r: r = FreeGroup.mk (FreeGroup.toWord r) := by
      exact Eq.symm FreeGroup.mk_toWord
    have h_p_r_conj: IsConj (FreeGroup.mk p) r := by
      rw [h_r]
      exact cycPerm_is_conj p (FreeGroup.toWord r) h_p_r
    have h_cyc_conj: IsConj (w) (CycRed w) := by
      apply word_conj_cycRed w
    have h_cycw_r: IsConj (CycRed w) r := by
      rw [h_cyc]
      exact h_p_r_conj
    have h_conj: IsConj w r := by
      exact IsConj.trans h_cyc_conj h_cycw_r
    obtain ⟨g, h_g⟩ := h_conj
    unfold SemiconjBy at h_g
    have h_fin : w = (↑g)⁻¹* (r * (↑g)) := eq_inv_mul_of_mul_eq h_g
    use g⁻¹
    rw[ inv_inv]
    rw[h_fin]
    exact Eq.symm (mul_assoc (↑g)⁻¹ r ↑g)

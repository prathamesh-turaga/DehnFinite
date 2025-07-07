import DehnFunction.Area1

namespace FreeGroup

variable {α : Type*} [DecidableEq α] (L : List (α × Bool)) (w : FreeGroup α)

def Uncycle (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | [_] => L
  | x :: y :: ys =>
      let xs := y :: ys
      let last := xs.getLast (by simp)
      let middle := xs.dropLast
      if x.1 = last.1 ∧ x.2 ≠ last.2 then
        Uncycle middle
      else
        L
termination_by L.length

theorem Uncycle.property (L : List (α × Bool)) :
    ∃ (U V : List (α × Bool)), L = U ++ Uncycle L ++ V ∧ FreeGroup.mk (V ++ U) = 1 := by
  match h_L_eq : L with
  | [] =>
    use [], []
    simp
    constructor
    . unfold Uncycle
      simp
    . subst h_L_eq
      rfl
  | [x] =>
    use [], []
    simp
    constructor
    . unfold Uncycle
      simp
    . subst h_L_eq
      rfl
  | x :: y :: ys =>
    let xs := y :: ys
    have h_L_form : L = x :: xs := by
      simp [h_L_eq]
      simp[xs]
    let last := xs.getLast (by simp)
    let middle := xs.dropLast
    if h_if : x.1 = last.1 ∧ x.2 ≠ last.2 then
      have h_def : Uncycle L = Uncycle middle := by
        rw [Uncycle.eq_def]
        rw [h_L_form]
        aesop
      have ih := property middle
      rcases ih with ⟨U', V', h_middle_decomp, h_vu'_is_one⟩
      let U := [x] ++ U'
      let V := V' ++ [last]
      use U, V
      constructor
      · rw[← h_L_eq]
        dsimp [U, V]
        rw [h_def, h_middle_decomp]
        rw [h_L_form]
        simp only [List.append_assoc, List.cons_append, ← h_middle_decomp]
        rw [show xs = middle ++ [last]
        by
          change xs = xs.dropLast ++ [xs.getLast _]
          exact
            Eq.symm
              (List.dropLast_concat_getLast
                (of_eq_true
                  (Eq.trans (congrArg Not (eq_false' fun h ↦ List.noConfusion h))
                    not_false_eq_true)))
          ]
        simp
        rw[← List.append_assoc]
        rw [← List.append_assoc ]
        rw[← h_middle_decomp]
      · dsimp [U, V]
        rw [List.append_assoc]
        rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
        change FreeGroup.mk V' * (FreeGroup.mk [last] * FreeGroup.mk ([x] ++ U')) = 1
        rw [← FreeGroup.mul_mk]
        have h_cancel : FreeGroup.mk [last] * FreeGroup.mk [x] = 1 := by
          have h_fst : x.1 = last.1 := by
            simp [h_if]
          have h_snd : (x.2) ≠  last.2 := by
            simp [h_if]
          have h_snd' : last.2 = !x.2 := by
            exact Bool.eq_not.mpr (id (Ne.symm h_snd))
          rw [mul_eq_one_iff_eq_inv]
          rw [FreeGroup.inv_mk]
          simp[FreeGroup.invRev]
          change FreeGroup.mk [(last.1, last.2)] = FreeGroup.mk [(x.1, !x.2)]
          rw[← h_fst, h_snd']
        rw[← mul_assoc (FreeGroup.mk [last]) (FreeGroup.mk [x]) (FreeGroup.mk U')]
        rw [h_cancel]
        simp
        exact h_vu'_is_one
    else
      have h_def : Uncycle L = L := by
        rw [h_L_eq]
        simp [Uncycle, h_if]
        aesop
      use [], []
      rw[← h_L_eq]
      rw [h_def]
      aesop
  termination_by L.length

def Uncycle' {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | a::as =>
    if has:as = [] then [a]
    else if a.1 = (as.getLast has).1 ∧ a.2 ≠ (as.getLast has).2 then
      Uncycle' (as.dropLast)
    else
      L
  termination_by L.length

def Uncycle_eq_Uncycle' {G: Type*} [DecidableEq G] (l : List (G × Bool)) : Uncycle l = Uncycle' l := by
  match l with
  | [] => simp [Uncycle,Uncycle']
  | [a] => simp [Uncycle,Uncycle']
  | a::b::bs =>
    simp [Uncycle,Uncycle']
    congr
    exact Uncycle_eq_Uncycle' ((b :: bs).dropLast)
  termination_by l.length

def CycRed := FreeGroup.mk (Uncycle (FreeGroup.toWord w))
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
  let M := Uncycle L
  unfold CyclicPermutationsOfRelators
  simp
  unfold CycRed
  have h_prop := Uncycle.property L
  rcases h_prop with ⟨U, V, h_decomp, h_vu_is_one⟩
  let p := M ++ V ++ U
  use p
  constructor
  · change p ~r L
    use (M ++ V).length
    dsimp [p]
    rw[h_decomp]
    have h_M_def: Uncycle L = M := rfl
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

namespace Uncycle

lemma conj_singleton (a : α) (b : Bool) :
    Uncycle ((a, b) :: L ++ [(a, !b)]) = Uncycle L := by
  cases L with
  | nil =>
    simp [Uncycle]
  | cons hd tl =>
    have this₁: (hd :: (tl ++ [(a, !b)])).dropLast = (hd :: tl ++ [(a, !b)]).dropLast := rfl
    have this₂ : (hd :: tl ++ [(a, !b)]).dropLast = (hd :: tl) := by exact List.dropLast_concat
    have this₃ : (hd :: (tl ++ [(a, !b)])).dropLast = (hd :: tl) := by exact this₂
    simp [Uncycle]
    have last_eq : ((hd :: tl) ++ [(a, !b)]).getLast (by simp) = (a, !b) := by simp [this₁, this₂, this₃]
    have cond_true : a = a ∧ b ≠ !b := by simp [Bool.not_eq_true']
    rw [this₃]

theorem conj :
    ∀ (P Q: List (α × Bool)), Uncycle (P ++ Q ++ FreeGroup.invRev P) = Uncycle (Q) := by
    intro P
    induction P with
    | nil =>
      intro Q
      simp [Uncycle]
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
  (Uncycle L).length ≤ L.length := by
  match hL: L with
  | [] => simp [Uncycle]
  | [_] =>
    have h_def : Uncycle L = L := by simp [Uncycle.eq_def, hL]
    rw[← hL]
    rw [h_def]
  | x :: y :: ys =>
    let xs := y :: ys
    have hL_form : L = x :: xs := by simp [hL, xs]
    let last := xs.getLast (by simp [hL, xs])
    let middle := xs.dropLast
    if h_if : x.1 = last.1 ∧ x.2 ≠ last.2 then
      have h_def : Uncycle L = Uncycle middle := by
          rw [hL_form]
          change Uncycle ((x.1, x.2) :: xs) = Uncycle middle
          rw [← conj_singleton middle x.1 x.2]
          have h_lastne : last.2 = !x.2 := by
            refine Bool.eq_not.mpr ?_
            apply Ne.symm
            exact h_if.2
          have h_last_eq : last = (x.1, !x.2) := by
            simp [h_if]
            simp [h_lastne.symm]
          rw [← h_last_eq]
          simp
          dsimp [middle, last]
          apply congrArg Uncycle
          simp [List.cons.injEq]
          exact
            Eq.symm
              (List.dropLast_concat_getLast
                (of_eq_true
                  (Eq.trans (congrArg Not (eq_false' fun h ↦ List.noConfusion h))
                    not_false_eq_true)))
      rw [← hL]
      rw [h_def]
      have ih := length_le middle
      have h_middle_len_lt : middle.length < L.length := by
        simp [hL_form, last, middle, xs]
        linarith
      linarith
    else
      have h_def : Uncycle L = L := by
        unfold Uncycle
        simp [h_if]
        aesop
      rw [← hL]
      rw [h_def]
  termination_by L.length

end Uncycle

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

theorem isUncycled_iff : IsUncycled L ↔ Uncycle L = L := by
  match hL: L with
  | [] =>
    simp [Uncycle, IsUncycled]
  | [x] =>
    simp [Uncycle, IsUncycled]
  | x :: y :: ys =>
    let xs := y :: ys
    have hL_form : L = x :: xs := by simp [hL, xs]
    let last := xs.getLast (by simp [hL, xs])
    let middle := xs.dropLast
    rw [← hL]
    if h_if : x.1 = last.1 ∧ x.2 ≠ last.2 then
      apply Iff.intro
      . intro h_eq
        have h_cond_is_false : ¬(x.1 = last.1 ∧ x.2 ≠ last.2) := by
          by_contra h_cond_is_true
          unfold IsUncycled at h_eq
          rw[hL] at h_eq
          simp at h_eq
          have h_last_eq : ((y :: ys).getLast (by simp [xs])) = last := by
            simp [last, xs]
          rw[h_last_eq] at h_eq
          have h_contr : ¬ (x.1 = last.1 ∧ x.2 ≠ last.2) := by
            rw[not_and_or]
            simp
            exact h_eq
          contradiction
        contradiction
      . intro h_eq
        have h_uncycle_eval : Uncycle L = Uncycle middle := by
          rw [hL_form]
          change Uncycle ((x.1, x.2) :: xs) = Uncycle middle
          rw [← Uncycle.conj_singleton middle x.1 x.2]
          have h_lastne : last.2 = !x.2 := by
            refine Bool.eq_not.mpr ?_
            apply Ne.symm
            exact h_if.2
          have h_last_eq : last = (x.1, !x.2) := by
            simp [h_if]
            simp [h_lastne.symm]
          rw [← h_last_eq]
          simp
          dsimp [middle, last]
          apply congrArg Uncycle
          simp [List.cons.injEq]
          exact
            Eq.symm
              (List.dropLast_concat_getLast
                (of_eq_true
                  (Eq.trans (congrArg Not (eq_false' fun h ↦ List.noConfusion h))
                    not_false_eq_true)))
        have h_impossible_equality : L = Uncycle middle := by rw [← h_eq, h_uncycle_eval]
        have h_contradiction : False := by
          have h_len_eq : L.length = (Uncycle middle).length := by rw [h_impossible_equality]
          have h_len_lt : (Uncycle middle).length < L.length := by
            have h_uncycle_len_le : (Uncycle middle).length ≤ middle.length := Uncycle.length_le middle
            have h_middle_len : middle.length < L.length := by
              simp [hL_form, last, middle, xs]
              linarith
            linarith
          linarith
        exfalso
        exact h_contradiction
    else
      simp [Uncycle, IsUncycled, h_if]
      apply iff_of_true
      · simp [hL]
        change ¬x.1 = (last).1 ∨ x.2 = (last).2
        push_neg at h_if
        exact Decidable.not_or_of_imp h_if
      · rw [Uncycle.eq_def]
        simp [hL]
        rw[← hL]
        change  x.1 = (last).1 → ¬x.2 = (last).2 → Uncycle middle = L
        intro h_1
        intro h_2
        have h_contr: (x.1 = (last).1 ∧ x.2 ≠ last.2) := by
          push_neg at h_2
          exact And.intro h_1 h_2
        contradiction

theorem Uncycle.isConj_to_self (L : List (α × Bool)) : IsConj (FreeGroup.mk L) (FreeGroup.mk (Uncycle L)) := by
  match hL: L with
  | [] =>
    simp [Uncycle]
    use 1
    simp
  | [x] =>
    simp [Uncycle]
    use 1
    simp
  | x :: y :: ys =>
    let xs := y :: ys
    have hL_form : L = x :: xs := by simp [hL, xs]
    let last := xs.getLast (by simp [hL, xs])
    let middle := xs.dropLast
    if h_if : x.1 = last.1 ∧ x.2 ≠ last.2 then
      have h_list: L = x :: middle ++ [last] := by
        rw [hL_form, show xs = middle ++ [last] by
        exact
          Eq.symm
            (List.dropLast_concat_getLast
              (of_eq_true
                (Eq.trans (congrArg Not (eq_false' fun h ↦ List.noConfusion h)) not_false_eq_true)))]
        rfl
      have h_lastne : last.2 = !x.2 := by
        refine Bool.eq_not.mpr ?_
        apply Ne.symm
        exact h_if.2
      have h_last : last = (x.1, !x.2) := by
        simp [h_if,h_lastne.symm]
      have h_uncycle_def : Uncycle L = Uncycle middle := by
        rw [h_list]
        change Uncycle ((x.1, x.2) :: middle ++ [last]) = Uncycle middle
        rw[h_last,← conj_singleton middle x.1 x.2]
      have ih := Uncycle.isConj_to_self middle
      have h_semiconj : FreeGroup.mk L * FreeGroup.mk [x] = FreeGroup.mk [x] * FreeGroup.mk middle := by
        rw [h_list]
        have h_head_list : x::middle = [x] ++ middle := by
          simp [List.cons_append]
        rw [h_head_list,← FreeGroup.mul_mk, ← FreeGroup.mul_mk,mul_assoc]
        have h_cancel : FreeGroup.mk [last] * FreeGroup.mk [x] = 1 := by
          rw [mul_eq_one_iff_eq_inv, FreeGroup.inv_mk]
          simp [FreeGroup.invRev]
          rw[h_last]
        rw [h_cancel,mul_one]
      rw[← hL, h_uncycle_def]
      have h_L_conj_middle : IsConj (FreeGroup.mk L) (FreeGroup.mk middle) := by
        unfold IsConj SemiconjBy
        use ⟨ (FreeGroup.mk (FreeGroup.invRev [x])), FreeGroup.mk [x],
              by exact mul_eq_one_iff_eq_inv.mpr rfl,
              by exact mul_eq_one_iff_inv_eq.mpr rfl⟩
        simp
        rw [ ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
        have h_L_eq : FreeGroup.mk L = FreeGroup.mk [x] * FreeGroup.mk middle * (FreeGroup.mk [x])⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq]
          exact h_semiconj
        rw [h_L_eq,← FreeGroup.inv_mk]
        group
      exact IsConj.trans h_L_conj_middle ih
    else
      rw[← hL]
      have h_uncycle_def : Uncycle L = L := by
        rw[← isUncycled_iff]
        unfold IsUncycled
        rw[hL]
        simp
        change ¬ x.1 = (last).1 ∨ x.2 = (last).2
        push_neg at h_if
        exact Decidable.not_or_of_imp h_if
      rw [h_uncycle_def]
termination_by L.length

theorem word_conj_cycRed : IsConj w (CycRed w) := by
  unfold CycRed
  let L := FreeGroup.toWord w
  have h_L_w : FreeGroup.mk L = w := by
    dsimp[L]
    exact FreeGroup.mk_toWord
  nth_rw 1 [← h_L_w]
  change IsConj (FreeGroup.mk L) (FreeGroup.mk (Uncycle L))
  apply Uncycle.isConj_to_self L

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

theorem conj_if_cyc (r : FreeGroup α): (∃ (wrd: List (α × Bool)), wrd ~r (FreeGroup.toWord r) ∧ (CycRed w) = FreeGroup.mk wrd) → (∃ (g: FreeGroup α), w = g * r * g⁻¹)
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

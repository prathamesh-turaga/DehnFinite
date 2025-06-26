import DehnFunction.Area1
import Mathlib.Data.List.Basic

open FreeGroup


variable {α : Type*} [DecidableEq α] {a b : α × Bool} (l l1 l2 : List (α × Bool))

theorem Red.append_left_right (l2' l3 : List (α × Bool)) (hl2 : Red l2 l2' ∧ l2' ≠ l2) :
  Red (l1++l2++l3) (l1++(l2')++l3) := by
  apply Red.append_append
  apply Red.append_append
  rfl; exact hl2.1; rfl

lemma Red.two_nil (h : Red [a,b] []) :
  a.1 = b.1 ∧ a.2 = !b.2 := by
  let (x,y) := a
  rw [Red.cons_nil_iff_singleton,Red.singleton_iff] at h
  simp at h
  simp [← h]

lemma Red.two_nil_if_red_pair (h : a.1 = b.1 ∧ a.2 = !b.2) :
  Red [a,b] [] := by
  let (x,y) := a
  have h1 : b = (x,!y) := by
    simp at h
    apply Prod.ext_iff.mpr
    simp [h]
  rw [h1]
  exact Red.cons_nil_iff_singleton.mpr (Red.singleton_iff.mpr rfl)

theorem Red.two_nil_iff : Red [a,b] [] ↔ a.1 = b.1 ∧ a.2 = !b.2 :=
  ⟨fun h => Red.two_nil h,fun h => Red.two_nil_if_red_pair h⟩

theorem Red.length_eq_iff_eq (h1 : Red l1 l2) (h2 : l1.length = l2.length) :
  l1 = l2 := by
  induction h1 using Relation.ReflTransGen.rec with
  | refl => rfl
  | tail h2 h3 ih =>
    expose_names
    have h4 := Red.Step.length h3
    have h5 := Red.length_le h2_1
    rw [le_iff_lt_or_eq] at h5
    rcases h5 with h5|h5
    · have h6 : c.length < b.length := by linarith
      have h7 := lt_trans h6 h5
      rw [h2] at h7
      linarith
    · rw [h5] at h4
      rw [← h2] at h4
      linarith

lemma Red.two_nil_if_length_lt_two (h : Red [a,b] l) (hl : l.length < 2) :
  l = [] := by
  have h1 := Red.length h
  rcases h1 with ⟨n,hn⟩
  simp at hn
  have h2 := add_lt_add_right hl (2*n)
  rw [← hn] at h2
  norm_num at h2
  have hn' : n < 2 := by
    rw [lt_iff_not_ge]
    intro h
    linarith
  have hn' : n=1 := by linarith
  rw [hn'] at hn
  simp at hn
  exact hn

lemma Red.two_nil_if_not_self (h : Red [a,b] l) (hl : l ≠ [a,b]) :
  l = [] := by
  have h1 := Red.length_le h
  simp at h1
  rw [le_iff_eq_or_lt] at h1
  rcases h1 with h1|h2
  · have h2 : 2 = [a,b].length := by simp
    rw [h2] at h1
    have h3 := Red.length_eq_iff_eq _ _ h
    symm at h1 hl
    apply h3 at h1
    contradiction
  · exact two_nil_if_length_lt_two l h h2

theorem Red.two_if (h : Red [a,b] l) :
  (l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2) ∨ (l = [a,b]) := by
  by_cases h1 : l = [a,b]
  · right; assumption
  · left
    have h2 := two_nil_if_not_self l h h1
    rw [h2] at h
    have h3 := two_nil h
    exact ⟨h2,h3⟩

lemma Red.two_nil_and_red_pair_if_not_self (h1 : Red [a,b] l) (h2 : l ≠ [a,b]) :
  l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2 := by
  rcases two_if l h1 with h1|h1
  · exact h1
  · contradiction

lemma Red.Step.irrefl : ¬Red.Step l l := by
  intro h
  have h1 := Red.Step.length h
  linarith

lemma Red.Step.not_self (h : Red.Step l1 l2) : l1 ≠ l2 := by
  intro h1
  have h2 := Red.Step.length h
  rw [h1] at h2
  linarith

lemma Red.not_self_imp_step (h1 : Red l1 l2) (h2 : l1 ≠ l2) :
  ∃ p, Red.Step l1 p := by
  induction h1 with
  | refl => contradiction
  | tail h1 h2 ih =>
    expose_names
    by_cases hl : l1=b
    · rw [← hl] at h2_1
      use c
    · exact ih hl

lemma Red.Step.exists_if_red_pair_exists (h : ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2)) :
  (∃ l', Red.Step l l') := by
  rcases h with ⟨l1,l2,a,b,h⟩
  use (l1++l2)
  rw [h]
  simp

lemma Red.Step.red_pair_exists_if_step : (∃ l', Red.Step l l')
  → ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2) := by
  intro h
  rcases h with ⟨l',hl'⟩
  induction hl' with
  | not =>
    expose_names
    use L₁
    use L₂
    use x
    use b

lemma Red.Step.exists_iff_red_pair_exists {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  (∃ l', Red.Step l l') ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2) :=
  ⟨Red.Step.red_pair_exists_if_step l,Red.Step.exists_if_red_pair_exists l⟩

def IsRed : Prop := ∀ J : List (α × Bool), FreeGroup.Red l J → J = l

namespace IsRed

theorem iff_reduce_self : IsRed l ↔ FreeGroup.reduce l = l := by
  constructor
  unfold IsRed; intro hypo
  have this₁ : FreeGroup.Red l (FreeGroup.reduce l) := by exact FreeGroup.reduce.red
  apply hypo at this₁; exact this₁
  intro hypo
  unfold IsRed;
  intro J
  intro are_rel_by_red
  have this₂ : FreeGroup.Red J (FreeGroup.reduce J) := by exact FreeGroup.reduce.red
  have RLJ : FreeGroup.Red l J := by exact are_rel_by_red
  apply FreeGroup.reduce.eq_of_red at are_rel_by_red
  rw [hypo] at are_rel_by_red
  rw [<-are_rel_by_red] at this₂
  apply FreeGroup.Red.sublist at RLJ
  apply FreeGroup.Red.sublist at this₂
  apply List.Sublist.antisymm RLJ this₂

theorem iff_noStep {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  IsRed l ↔ ∀ l', ¬Red.Step l l' := by
  constructor
  · intro h p hp
    have h1 : l ≠ p := (Red.Step.not_self l p hp)
    apply Red.Step.to_red at hp
    exact h1 (Eq.symm (h p hp))
  · intro h
    rw [IsRed]
    intro p hp
    induction hp with
    | refl => rfl
    | tail h1 h2 ih =>
      expose_names
      rw [ih] at h2
      specialize h c
      contradiction

lemma nil : IsRed ([] : List (α×Bool)) := by
  intro l hl
  exact Red.nil_iff.mp hl

theorem singleton : IsRed [a] := by
  dsimp [IsRed]
  intro l
  exact Red.singleton_iff.mp

theorem two (hab : IsRed [a,b]) :
  (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  by_contra h
  push_neg at h
  rw [← Bool.eq_not] at h
  dsimp [IsRed] at hab
  specialize hab []
  have h1 : Red [a, b] [] := by
    rw [Red.cons_nil_iff_singleton]
    apply Red.singleton_iff.mpr
    simp [h]
  apply hab at h1
  contradiction

lemma two_not_if_red_pair (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed [a,b] := by
  contrapose hab
  rw [not_and_or]
  push_neg at hab
  convert two hab; simp

lemma two_if_not_red_pair (hab : a.1 ≠ b.1) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push_neg at *
  rcases hab with ⟨p,hp1,hp2⟩
  exact (Red.two_nil_and_red_pair_if_not_self p hp1 hp2).2.1

lemma two_if_not_red_pair' (hab : a.2 = b.2) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push_neg at *
  rcases hab with ⟨p,hp1,hp2⟩
  rw [← Bool.eq_not_iff]
  exact (Red.two_nil_and_red_pair_if_not_self p hp1 hp2).2.2

theorem two_iff_not_red_pair : IsRed [a,b] ↔ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  constructor
  · intro h
    exact two h
  · intro h
    rcases h with h|h
    · exact two_if_not_red_pair h
    · exact two_if_not_red_pair' h

lemma prefix_IsRed (hL : IsRed (l1++l2)) : IsRed l1 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (P++l2)
  have h1 : Red (l1 ++ l2) (P ++ l2) := by refine Red.append_append hP (Red.refl)
  apply hL at h1
  exact List.append_cancel_right h1

lemma suffix_IsRed (hL : IsRed (l1++l2)) : IsRed l2 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (l1++P)
  have h1 : Red (l1 ++ l2) (l1++P) := by refine Red.append_append (Red.refl) hP
  apply hL at h1
  exact List.append_cancel_left h1

theorem infix_IsRed (l3 : List (α×Bool)) (hL : IsRed (l1++l3++l2)) : IsRed l3 := by
  apply suffix_IsRed l1 l3
  exact prefix_IsRed (l1++l3) l2 hL

lemma tail (h : IsRed (a::l)) :
  IsRed l := by
  have h1 : a::l = [a]++l := rfl
  rw [h1] at h
  exact suffix_IsRed [a] l h

theorem cons_cons (h : IsRed (a::b::l)) :
  IsRed (b::l) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  induction l with
  | nil =>
    apply two at h
    simp [h,singleton]
  | cons hd tl ih =>
    constructor
    · exact tail (b :: hd :: tl) h
    · by_contra h1
      push_neg at h1
      have h4 : Red (a::b::hd::tl) (hd::tl) := by
        apply Red.Step.to_red
        rw [← Bool.eq_not] at h1
        let (x,y) := a
        have h5 : b = (x,!y) := by
          simp at h1
          apply Prod.ext_iff.mpr
          simp [h1]
        rw [h5]
        simp
      rw [IsRed] at h
      specialize h (hd::tl) h4
      simp at h
      rcases h with ⟨_,h⟩
      have h5 : tl.length = (b::hd::tl).length := by rw [← h]
      simp at h5
      linarith

theorem cons (hl : l ≠ []) (h : IsRed (a::l)) :
  IsRed l ∧ (a.1 ≠ (l.head hl).1 ∨ a.2 = (l.head hl).2) := by
  match l with
  | [] => contradiction
  | b::bs => exact cons_cons bs h

lemma not_if_red_pair_suffix (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed (l++[a,b]) := by
  induction l with
  | nil => simp [two_not_if_red_pair hab]
  | cons x xs ih =>
    contrapose ih
    push_neg at *
    exact tail (xs ++ [a, b]) ih

lemma not_if_red_pair_prefix (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed ([a,b]++l) := by
  induction l using List.reverseRecOn with
  | nil => simp [two_not_if_red_pair hab]
  | append_singleton l x ih =>
    rw [← List.append_assoc]
    contrapose ih
    push_neg at *
    exact prefix_IsRed ([a, b] ++ l) [x] ih

lemma not_if_red_pair_infix (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed (l1++[a,b]++l2) := by
  match l1 with
  | [] => simp; exact not_if_red_pair_prefix l2 hab
  | x::xs =>
    induction l2 using List.reverseRecOn with
    | nil => simp; rw [← List.cons_append]; exact not_if_red_pair_suffix (x::xs) hab
    | append_singleton ys y ih =>
      have h1 : x :: xs ++ [a, b] ++ ys = [x] ++ xs ++ [a, b] ++ ys := by simp
      rw [h1] at ih
      have h2 : x :: xs ++ [a, b] ++ (ys ++ [y]) = [x] ++ xs ++ [a, b] ++ ys ++ [y] := by simp
      rw [h2]
      contrapose ih
      push_neg at *
      exact prefix_IsRed ([x] ++ xs ++ [a, b] ++ ys) [y] ih

theorem not_iff_red_pair_exists :
  ¬IsRed l ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, not b) :: l2) := by
  constructor
  · intro hl
    rw [iff_noStep] at hl
    push_neg at hl
    rw [Red.Step.exists_iff_red_pair_exists] at hl
    exact hl
  · intro hl
    rcases hl with ⟨l1,l2,a,b,h⟩
    rw [h]
    set x := (a,b) with hx
    set y := (a,!b) with hy
    have : l1 ++ x :: y :: l2 = l1++[x,y]++l2 := by simp
    rw [this]
    exact not_if_red_pair_infix l1 l2 (by simp [hx,hy])

theorem cons_if_not_red_pair (hl : IsRed (b::l)) (hab : a.1 ≠ b.1) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact two_if_not_red_pair hab
  | cons x xs ih =>
    contrapose hl
    rw [iff_noStep] at hl ⊢
    push_neg at hl ⊢
    rw [Red.Step.exists_iff_red_pair_exists] at hl ⊢
    rcases hl with ⟨l1,l2,y,c,hl⟩
    match l1 with
    | [] =>
      simp at hl
      rw [hl.1,hl.2.1] at hab
      simp at hab
    | p::ps =>
      use ps
      use l2
      use y
      use c
      simp at hl
      exact hl.2

theorem cons_if_not_red_pair' {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (hab : a.2 = b.2) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact two_if_not_red_pair' hab
  | cons x xs ih =>
    contrapose hl
    rw [iff_noStep] at hl ⊢
    push_neg at hl ⊢
    rw [Red.Step.exists_iff_red_pair_exists] at hl ⊢
    rcases hl with ⟨l1,l2,y,c,hl⟩
    match l1 with
    | [] =>
      simp at hl
      rw [hl.1,hl.2.1] at hab
      simp at hab
    | p::ps =>
      use ps
      use l2
      use y
      use c
      simp at hl
      exact hl.2

end IsRed

def IsRed_inductive {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | a::b::as =>
    IsRed_inductive (b::as) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2)

theorem IsRed.iff_IsRed_inductive {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L ↔ IsRed_inductive L := by
  constructor
  · intro h
    induction L using IsRed_inductive.induct with
    | case1 => rw [IsRed_inductive]; tauto
    | case2 _ => rw [IsRed_inductive]; tauto
    | case3 a b bs ih =>
      rw [IsRed_inductive]
      have h1 : IsRed (b::bs) := tail _ h
      apply ih at h1
      exact ⟨h1,(cons _ (List.cons_ne_nil b bs) h).2⟩
  · intro h
    induction L using IsRed_inductive.induct with
    | case1 => exact (iff_reduce_self []).mpr rfl
    | case2 b => exact singleton
    | case3 a b as ih =>
      rw [IsRed_inductive] at h
      have h1 := ih h.1
      rcases h.2 with h2|h2
      · exact cons_if_not_red_pair as h1 h2
      · exact cons_if_not_red_pair' a b as h1 h2

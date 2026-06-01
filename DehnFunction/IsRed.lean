import DehnFunction.Area1

namespace FreeGroup

variable {α : Type*} [DecidableEq α] {a b : α × Bool} (l l1 l2 : List (α × Bool))

omit [DecidableEq α] in
/--If `[a,b]` reduces to `[]`, then `a = b⁻¹`-/
lemma Red.two_nil (h : Red [a,b] []) :
  a.1 = b.1 ∧ a.2 = !b.2 := by
  let (x,y) := a
  rw [Red.cons_nil_iff_singleton,Red.singleton_iff] at h
  simp at h
  simp [← h]

omit [DecidableEq α] in
/--If `a = b⁻¹`, then `[a,b]` reduces to `[]`-/
lemma Red.two_nil_if_red_pair (h : a.1 = b.1 ∧ a.2 = !b.2) :
  Red [a,b] [] := by
  let (x,y) := a
  have h1 : b = (x,!y) := by
    simp at h
    apply Prod.ext_iff.mpr
    simp [h]
  rw [h1]
  exact Red.cons_nil_iff_singleton.mpr (Red.singleton_iff.mpr rfl)

omit [DecidableEq α] in
/--`[a,b]` reduces to `[]` iff `a = b⁻¹-/
theorem Red.two_nil_iff : Red [a,b] [] ↔ a.1 = b.1 ∧ a.2 = !b.2 :=
  ⟨fun h => Red.two_nil h,fun h => Red.two_nil_if_red_pair h⟩

omit [DecidableEq α] in
/--If `l₁` reduces to `l₂` and `l₁.length = l₂.length`, then `l₁ = l₂`-/
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

omit [DecidableEq α] in
/--If `[a,b]` reduces to `l` and `l.length < 2`, then `l = []`-/
lemma Red.two_nil_if_length_lt_two (h : Red [a,b] l) (hl : l.length < 2) :
  l = [] := by
  have h1 := Red.length h
  rcases h1 with ⟨n,hn⟩
  simp at hn
  have h2 := add_lt_add_right hl (2*n)
  rw [hn] at h2
  norm_num at h2
  have hn' : n < 2 := by
    rw [lt_iff_not_ge]
    intro h
    linarith
  have hn' : n=1 := by linarith
  rw [hn'] at hn
  simp at hn
  exact hn

omit [DecidableEq α] in
/--If `[a,b]` doesn't reduce to itself, it reduces to `[]`-/
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

/--`[a,b]` either reduces to `[]` with `a = b⁻¹`, or it reduces to itself-/
theorem Red.two_if (h : Red [a,b] l) :
  (l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2) ∨ (l = [a,b]) := by
  by_cases h1 : l = [a,b]
  · right; assumption
  · left
    have h2 := two_nil_if_not_self l h h1
    rw [h2] at h
    have h3 := two_nil h
    exact ⟨h2,h3⟩

/--If `[a,b]` doesn't reduce to itself, it reduces to `[]` and `a = b⁻¹`-/
lemma Red.two_nil_and_red_pair_if_not_self (h1 : Red [a,b] l) (h2 : l ≠ [a,b]) :
  l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2 := by
  rcases two_if l h1 with h1|h1
  · exact h1
  · contradiction

omit [DecidableEq α] in
/--`Red.Step` is irrefl, i.e. no list `l` reduces to itself in one step-/
lemma Red.Step.irrefl : ¬Red.Step l l := by
  intro h
  have h1 := Red.Step.length h
  linarith

omit [DecidableEq α] in
/--If `l₁` reduces to `l₂` in one step, then `l₁ ≠ l₂`-/
lemma Red.Step.not_self (h : Red.Step l1 l2) : l1 ≠ l2 := by
  intro h1
  have h2 := Red.Step.length h
  rw [h1] at h2
  linarith

/--If `l₁` reduces to `l₂` and `l₁ ≠ l₂`, then there is a list `p` that `l₁` reduces to in one step-/
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

omit [DecidableEq α] in
/--If `l` contains a reducible pair, then `l` reduces to some list `l'` in one step-/
lemma Red.Step.exists_if_red_pair_exists (h : ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2)) :
  (∃ l', Red.Step l l') := by
  rcases h with ⟨l1,l2,a,b,h⟩
  use (l1++l2)
  rw [h]
  simp

omit [DecidableEq α] in
/--If `l` reduces to some list `l'` in one step, then `l` contains a reducible pair-/
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

/--`l` contains a reducible pair iff `l` reduces to some list `l'` in one step-/
lemma Red.Step.exists_iff_red_pair_exists {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  (∃ l', Red.Step l l') ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2) :=
  ⟨Red.Step.red_pair_exists_if_step l,Red.Step.exists_if_red_pair_exists l⟩

lemma mk_red_pair (a b : α×Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) : mk [a,b] = 1 := by
  rw [← toWord_inj]
  simp [hab]

/--A word is reduced if `∀ J : List (α × Bool), Red l J → J = l`, i.e. the word can only further reduce to itself-/
def IsRed : Prop := ∀ J : List (α × Bool), FreeGroup.Red l J → J = l

namespace IsRed

/--If `l` is reduced, then `reduce l = l`-/
theorem equiv_of_reds : IsRed l ↔ FreeGroup.reduce l = l := by
  constructor
  unfold IsRed; intro hypo
  have this₁ : FreeGroup.Red l (FreeGroup.reduce l) := by exact FreeGroup.reduce.red
  apply hypo at this₁; exact this₁
  intro hypo
  unfold IsRed;
  intro J are_rel_by_red
  have this₂ : FreeGroup.Red J (FreeGroup.reduce J) := by exact FreeGroup.reduce.red
  have RLJ : FreeGroup.Red l J := by exact are_rel_by_red
  apply FreeGroup.reduce.eq_of_red at are_rel_by_red
  rw [hypo] at are_rel_by_red
  rw [<-are_rel_by_red] at this₂
  apply FreeGroup.Red.sublist at RLJ
  apply FreeGroup.Red.sublist at this₂
  apply List.Sublist.antisymm RLJ this₂

omit [DecidableEq α] in
/--`l` is reduced iff `l` can't be reduced any further in one step-/
theorem iff_noStep : IsRed l ↔ ∀ l', ¬Red.Step l l' := by
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

omit [DecidableEq α] in
/--`[]` is reduced-/
lemma nil : IsRed ([] : List (α×Bool)) := by
  intro l hl
  exact Red.nil_iff.mp hl

omit [DecidableEq α] in
/--A singleton list is always reduced-/
theorem singleton : IsRed [a] := by
  dsimp [IsRed]
  intro l
  exact Red.singleton_iff.mp

/--If `[a,b]` is reduced, then `a ≠ b⁻¹`-/
theorem two (hab : IsRed [a,b]) : (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  by_contra h
  push Not at h
  rw [← Bool.eq_not] at h
  dsimp [IsRed] at hab
  specialize hab []
  have h1 : Red [a, b] [] := by
    rw [Red.cons_nil_iff_singleton]
    apply Red.singleton_iff.mpr
    simp [h]
  apply hab at h1
  contradiction

/--If `a = b⁻¹`, then `[a,b]` is not reduced-/
lemma two_not_if_red_pair (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed [a,b] := by
  contrapose hab
  rw [not_and_or]
  convert two hab; simp

lemma two_if_not_red_pair (hab : a.1 ≠ b.1) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push Not at *
  rcases hab with ⟨p,hp1,hp2⟩
  exact (Red.two_nil_and_red_pair_if_not_self p hp1 hp2).2.1

lemma two_if_not_red_pair' (hab : a.2 = b.2) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push Not at *
  rcases hab with ⟨p,hp1,hp2⟩
  rw [← Bool.eq_not_iff]
  exact (Red.two_nil_and_red_pair_if_not_self p hp1 hp2).2.2

/--`[a,b]` is reduced iff `a ≠ b⁻¹`-/
theorem two_iff_not_red_pair : IsRed [a,b] ↔ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  constructor
  · intro h
    exact two h
  · intro h
    rcases h with h|h
    · exact two_if_not_red_pair h
    · exact two_if_not_red_pair' h

omit [DecidableEq α] in
/--Prefix of a reduced word is reduced-/
lemma prefix_IsRed (hL : IsRed (l1++l2)) : IsRed l1 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (P++l2)
  have h1 : Red (l1 ++ l2) (P ++ l2) := by refine Red.append_append hP (Red.refl)
  apply hL at h1
  exact List.append_cancel_right h1

omit [DecidableEq α] in
/--Suffix of a reduced word is reduced-/
lemma suffix_IsRed (hL : IsRed (l1++l2)) : IsRed l2 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (l1++P)
  have h1 : Red (l1 ++ l2) (l1++P) := by refine Red.append_append (Red.refl) hP
  apply hL at h1
  exact List.append_cancel_left h1

omit [DecidableEq α] in
/--Infix of a reduced word is reduced-/
theorem infix_IsRed (l3 : List (α×Bool)) (hL : IsRed (l1++l3++l2)) : IsRed l3 := by
  apply suffix_IsRed l1 l3
  exact prefix_IsRed (l1++l3) l2 hL

omit [DecidableEq α] in
/--Tail of a reduced word is reduced-/
lemma tail (h : IsRed (a::l)) :
  IsRed l := by
  have h1 : a::l = [a]++l := rfl
  rw [h1] at h
  exact suffix_IsRed [a] l h

/--If `a::b::l` is reduced, then `b::l` is reduced and `a ≠ b⁻¹`-/
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
      push Not at h1
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

/--If `a::l` is reduced, then `l` is reduced and `a ≠ (l.head)⁻¹`-/
theorem cons (hl : l ≠ []) (h : IsRed (a::l)) :
  IsRed l ∧ (a.1 ≠ (l.head hl).1 ∨ a.2 = (l.head hl).2) := by
  match l with
  | [] => contradiction
  | b::bs => exact cons_cons bs h

/--`l` is not reduced if its suffix is a reducible pair-/
lemma not_if_red_pair_suffix (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed (l++[a,b]) := by
  induction l with
  | nil => simp [two_not_if_red_pair hab]
  | cons x xs ih =>
    contrapose ih
    exact tail (xs ++ [a, b]) ih

/--`l` is not reduced if its prefix is a reducible pair-/
lemma not_if_red_pair_prefix (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed ([a,b]++l) := by
  induction l using List.reverseRecOn with
  | nil => simp [two_not_if_red_pair hab]
  | append_singleton l x ih =>
    rw [← List.append_assoc]
    contrapose ih
    exact prefix_IsRed ([a, b] ++ l) [x] ih

/--`l` is not reduced if it contains is a reducible pair-/
lemma not_if_contains_red_pair (hab : a.1 = b.1 ∧ a.2 = !b.2) :
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
      exact prefix_IsRed ([x] ++ xs ++ [a, b] ++ ys) [y] ih

/--`l` is not reduced iff it contains a reducible pair-/
theorem not_iff_red_pair_exists :
  ¬IsRed l ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, not b) :: l2) := by
  constructor
  · intro hl
    rw [iff_noStep] at hl
    push Not at hl
    rw [Red.Step.exists_iff_red_pair_exists] at hl
    exact hl
  · intro hl
    rcases hl with ⟨l1,l2,a,b,h⟩
    rw [h]
    set x := (a,b) with hx
    set y := (a,!b) with hy
    have : l1 ++ x :: y :: l2 = l1++[x,y]++l2 := by simp
    rw [this]
    exact not_if_contains_red_pair l1 l2 (by simp [hx,hy])

theorem cons_if_not_red_pair (hl : IsRed (b::l)) (hab : a.1 ≠ b.1) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact two_if_not_red_pair hab
  | cons x xs ih =>
    contrapose hl
    rw [iff_noStep] at hl ⊢
    push Not at hl ⊢
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

theorem cons_if_not_red_pair' (hl : IsRed (b::l)) (hab : a.2 = b.2) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact two_if_not_red_pair' hab
  | cons x xs ih =>
    contrapose hl
    rw [iff_noStep] at hl ⊢
    push Not at hl ⊢
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

/--`a::b::l` is reduced iff `b::l` is reduced and `a ≠ b⁻¹`-/
theorem cons_cons_iff_not_red_pair :
  IsRed (a::b::l) ↔ IsRed (b::l) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  constructor
  · intro h
    constructor
    · exact tail (b :: l) h
    · apply two_iff_not_red_pair.mp
      have : a::b::l = [a,b]++l := by simp
      rw [this] at h
      exact prefix_IsRed [a, b] l h
  · intro ⟨h1,h2⟩
    cases h2 with
    | inl h2 => exact cons_if_not_red_pair l h1 h2
    | inr h2 => exact cons_if_not_red_pair' l h1 h2

/--`a::l` is reduced iff `l` is reduced and `a ≠ (l.head)⁻¹`-/
theorem cons_iff_not_red_pair (hl : l ≠ []) : IsRed (a::l) ↔ IsRed (l) ∧ (a.1 ≠ (l.head hl).1 ∨ a.2 = (l.head hl).2) := by
  match l with
  | [] => contradiction
  | b::bs => exact cons_cons_iff_not_red_pair bs

end IsRed

/--The inductive version of `IsRed`:
* `[]` is reduced
* Singleton lists are reduced
* `a::b::as` is reduced if `b::as` is reduced and `a ≠ b⁻¹`-/
def IsRed_inductive (L : List (α × Bool)) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | a::b::as =>
    IsRed_inductive (b::as) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2)

/--`IsRed` and its inductive version are equivalent-/
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
    | case1 => exact (equiv_of_reds []).mpr rfl
    | case2 b => exact singleton
    | case3 a b as ih =>
      rw [IsRed_inductive] at h
      have h1 := ih h.1
      rcases h.2 with h2|h2
      · exact cons_if_not_red_pair as h1 h2
      · exact cons_if_not_red_pair' as h1 h2

omit [DecidableEq α] in
lemma List.concat_if_not_empty (l : List α) (hl : l ≠ []) : l = l.dropLast++[l.getLast hl] := by
  induction l using List.reverseRecOn with
  | nil => contradiction
  | append_singleton l a _ => simp

/--The tail recursive version of `IsRed`:-/
def IsRed_TR (L : List (α×Bool)) : Prop :=
  List.reverseRecOn L
  (True)
  (fun as a iha =>
    if has : as = [] then True
    else if (a.1 ≠ (as.getLast has).1 ∨ a.2 = (as.getLast has).2) then iha
    else False)

lemma IsRed_TR.nil {α : Type*} [DecidableEq α] : IsRed_TR ([] : List (α×Bool)) := by simp [IsRed_TR]

lemma IsRed_TR.singleton {α : Type*} [DecidableEq α] {a : α×Bool} : IsRed_TR [a] := by
  simp [IsRed_TR,List.reverseRecOn, List.reverseRec]

lemma IsRed_TR.concat_concat_iff : IsRed_TR (l++[b]) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) ↔ IsRed_TR (l ++ [b] ++ [a]) := by
  constructor
  · intro h
    rw [IsRed_TR,List.reverseRecOn_concat]
    have h1 : l ++ [b] ≠ [] := by simp
    rw [dif_neg h1,List.getLast_concat,if_pos h.2]
    rw [← IsRed_TR]
    exact h.1
  · intro h
    rw [IsRed_TR,List.reverseRecOn_concat] at h
    have h1 : l ++ [b] ≠ [] := by simp
    rw [dif_neg h1,List.getLast_concat] at h
    by_cases hab : (a.1 ≠ b.1 ∨ a.2 = b.2)
    · rw [if_pos hab] at h
      rw [← IsRed_TR] at h
      exact ⟨h,hab⟩
    · rw [if_neg hab] at h
      contradiction

lemma IsRed_TR.concat_if (hl1 : l ≠ []) (hl : IsRed_TR l) (ha : a.1 ≠ (l.getLast hl1).1 ∨ a.2 = (l.getLast hl1).2) : IsRed_TR (l++[a]) := by
  rw [List.concat_if_not_empty _ hl1] at hl ⊢
  exact (concat_concat_iff l.dropLast).mp ⟨hl,ha⟩

namespace IsRed

lemma three_iff_pair_red (c : α×Bool) (hab : IsRed [a,b]) (hbc : IsRed [b,c]) :
  IsRed [a,b,c] := by
  rw [two_iff_not_red_pair] at hab
  exact (cons_cons_iff_not_red_pair [c]).mpr ⟨hbc, hab⟩

lemma concat_if_end_not_red_pair (hl1 : IsRed (l1++[a])) (hab : a.1 ≠ b.1 ∨ a.2 = b.2) : IsRed (l1++[a]++[b]) := by
  induction l1 using IsRed_inductive.induct with
  | case1 => simp; exact two_iff_not_red_pair.mpr hab
  | case2 x =>
    simp at hl1
    have h3 : ([x] ++ [a] ++ [b]) = x::[a,b] := rfl
    rw [h3]
    rw [← two_iff_not_red_pair] at hab
    exact three_iff_pair_red b hl1 hab
  | case3 x y ys ih =>
    have h1 := ih (tail _ hl1)
    have h2 : IsRed (x::y::ys) := prefix_IsRed (x :: y :: ys) [a] hl1
    apply (cons _ (List.cons_ne_nil y ys)) at h2
    have h3 : x :: y :: ys ++ [a] ++ [b] = x :: y :: (ys ++ [a] ++ [b]) := rfl
    rw [h3]
    apply (cons_cons_iff_not_red_pair (ys ++ [a] ++ [b])).mpr
    exact ⟨h1,h2.2⟩

lemma concat_iff_end_not_red_pair : IsRed (l1++[a]) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) ↔ IsRed (l1++[a]++[b]) := by
  constructor
  · intro h
    exact concat_if_end_not_red_pair l1 h.1 h.2
  · intro h
    constructor
    · exact prefix_IsRed (l1 ++ [a]) [b] h
    · apply two_iff_not_red_pair.mp
      have : l1 ++ [a] ++ [b] = l1++[a,b] := Eq.symm (List.append_cons l1 a [b])
      rw [this] at h
      exact suffix_IsRed l1 [a, b] h

lemma reverse_IsRed (hl : IsRed l) : IsRed l.reverse := by
  induction l using IsRed_inductive.induct with
  | case1 => simp [nil]
  | case2 a => simp [singleton]
  | case3 a b as ih =>
    have h1 := ih (tail _ hl)
    rw [List.reverse_cons] at h1 ⊢
    rw [List.reverse_cons]
    rw [iff_IsRed_inductive] at hl
    rw [IsRed_inductive] at hl
    apply concat_if_end_not_red_pair as.reverse h1
    convert hl.2 using 1
    aesop
    aesop

lemma iff_reverse_IsRed : IsRed l ↔ IsRed l.reverse := by
  constructor
  · intro h; exact reverse_IsRed l h
  · intro h; rw [← List.reverse_reverse l]; exact reverse_IsRed l.reverse h

theorem iff_IsRed_TR (L : List (α × Bool)) : IsRed L ↔ IsRed_TR L := by
  constructor
  · intro h
    induction L using List.reverseRecOn with
  | nil => exact IsRed_TR.nil
  | append_singleton xs x ih =>
    by_cases hxs : xs = []
    · simp [hxs]; exact IsRed_TR.singleton
    · have h1 := List.concat_if_not_empty xs hxs
      have h2 : IsRed xs := by exact prefix_IsRed xs [x] h
      rw [h1] at h
      rw [iff_reverse_IsRed,iff_IsRed_inductive] at h
      simp [IsRed_inductive] at h
      refine IsRed_TR.concat_if xs hxs (ih h2) (h.2)
  · intro h
    induction L using List.reverseRecOn with
  | nil => exact nil
  | append_singleton xs x ih =>
    by_cases hxs : xs = []
    · simp [hxs]; exact singleton
    · have h1 := List.concat_if_not_empty xs hxs
      rw [h1,← IsRed_TR.concat_concat_iff] at h
      rw [h1,iff_reverse_IsRed,iff_IsRed_inductive]
      simp [IsRed_inductive]
      constructor
      · rw [← iff_IsRed_inductive]
        rw [iff_reverse_IsRed]
        simp [← h1] at h ⊢
        exact ih h.1
      · exact h.2

-- lemma concat_cons_append_if_not_red_pair (hl1 : IsRed (l1++[a])) (hl2 : IsRed (b::l2)) (hab : a.1 ≠ b.1 ∨ a.2 = b.2) : IsRed (l1++[a]++b::l2) := by
--   induction l2 using List.reverseRecOn with
--   | nil =>
--     simp
--     have h1 : (l1 ++ [a, b]) = (l1++[a])++[b] := by simp
--     rw [h1]
--   | append_singleton xs x ih =>
--     rw [← List.cons_append] at hl2
--     have h1 := ih (prefix_IsRed (b :: xs) [x] hl2)
--     sorry
--   -- induction l2 with
--   -- | nil =>
--   --   simp
--   --   have h1 : (l1 ++ [a, b]) = (l1++[a])++[b] := by simp
--   --   rw [h1]
--   --   exact concat_if_end_not_red_pair l1 hl1 hab
--   -- | cons head tail ih =>
--   --   sorry

-- lemma append_if_no_red_pair_at_join (h1 : IsRed l1) (h2 : IsRed l2) (h1ne : l1 ≠ []) (h2ne : l2 ≠ []) :
--   (l1.getLast h1ne).1 ≠ (l2.head h2ne).1 ∨ (l1.getLast h1ne).2 = (l2.head h2ne).2  → IsRed (l1 ++ l2) := by sorry

theorem iff_mk_norm_eq_length : IsRed l ↔ (mk l).norm = l.length := by
  induction l using IsRed_inductive.induct with
  | case1 => simp [nil]; rfl
  | case2 a => simp [singleton]; rfl
  | case3 a b as ih =>
    constructor
    · intro h
      rw [equiv_of_reds] at h
      rw [FreeGroup.norm,toWord_mk,h]
    · intro h
      rw [FreeGroup.norm,toWord_mk] at h
      have h1 : Red (a::b::as) (reduce (a::b::as)) := reduce.red
      have h2 := Red.length_eq_iff_eq _ _ h1 (Eq.symm h)
      symm at h2
      exact (equiv_of_reds (a :: b :: as)).mpr h2

instance : Decidable (IsRed l) := decidable_of_decidable_of_iff (iff_mk_norm_eq_length l).symm

#synth Decidable (IsRed [(1,true),(1,false)])
#eval IsRed [(1,true),(1,false)]

end IsRed

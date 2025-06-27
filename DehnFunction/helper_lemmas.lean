import DehnFunction.Area1
import DehnFunction.Cyc_conj
import Mathlib.Data.List.Basic



-- STUFF FROM AREA2



def CycReduce {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) := Uncycle (FreeGroup.reduce L)
-- Takes a list and returns cyclic reduction of that list's freely-reduced form.




def IsRed {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := ∀ J : List (α × Bool), FreeGroup.Red L J → J = L

lemma app_lists_eq_canc_r {k : Type*}: ∀ (P Q R : List k), P ++ Q = R ++ Q → P = R := by exact fun P Q R a ↦ List.append_cancel_right a
lemma app_lists_eq_canc_l {k : Type*}: ∀ (P Q R : List k), Q ++ P = Q ++ R → P = R := by exact fun P Q R a ↦ List.append_cancel_left a

lemma uncyc_of_red_is_red {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L → IsRed (Uncycle L) := by
  intro hypo
  unfold IsRed at hypo
  unfold IsRed
  by_contra
  expose_names; simp at h
  rcases h with ⟨L', h₁,h₂⟩;
  apply Uncycle_property at L; rcases L with ⟨U,V,p₁,p₂⟩
  rw [<- FreeGroup.Red.append_append_left_iff U] at h₁
  have tempp : FreeGroup.Red V V := by exact FreeGroup.Red.refl
  have this_one : FreeGroup.Red (U ++ Uncycle L ++ V) (U ++ L' ++ V) := by apply FreeGroup.Red.append_append h₁ tempp
  rw [<-p₁] at this_one
  specialize hypo (U ++ L' ++ V)
  have this₁ : (U ++ L' ++ V) = L := by exact hypo this_one
  have this₂ : (U ++ L' ++ V) = (U ++ (Uncycle L) ++ V) := by rw [p₁] at this₁; exact this₁
  have this₃ : L' = Uncycle L := by
    apply app_lists_eq_canc_r at this₂
    apply app_lists_eq_canc_l at this₂; exact this₂
  contradiction


lemma equiv_of_reds {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L ↔ FreeGroup.reduce L = L := by
  constructor
  unfold IsRed; intro hypo
  have this₁ : FreeGroup.Red L (FreeGroup.reduce L) := by exact FreeGroup.reduce.red
  apply hypo at this₁; exact this₁
  intro hypo
  unfold IsRed;
  intro J
  intro are_rel_by_red
  have this₂ : FreeGroup.Red J (FreeGroup.reduce J) := by exact FreeGroup.reduce.red
  have RLJ : FreeGroup.Red L J := by exact are_rel_by_red
  apply FreeGroup.reduce.eq_of_red at are_rel_by_red
  rw [hypo] at are_rel_by_red
  rw [<-are_rel_by_red] at this₂
  apply FreeGroup.Red.sublist at RLJ
  apply FreeGroup.Red.sublist at this₂
  apply List.Sublist.antisymm RLJ this₂




-- reduced word a₁a₂...a_n is cycreduced iff it is reduced and ¬(a₁a_n = 1)

-- The last part can be said for the word as a list also. L represents a reduced word iff :
-- it is "reduced" (as a list, so would need to invoke standard free reduction somehow) and
-- (([L.head].mk) * ([L.getLast].mk) = 1)

-- Lemma : ∃! red and cycred reps for each equiv class that a FG constitutes.
-- pg 176 of pdf has an outline
-- Propn (w, w' cycreduced) : w.conj w' ↔ they are cyclically equivalent



--  have other₁ : True := sorry
--  simp [this₁, this₂, that₁, that₂, that₃]







lemma form_of_conj {α : Type*} [DecidableEq α] (g y : FreeGroup α): (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]

#check List.IsInfix

def cycreduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := (IsRed L) ∧ (Uncycle L = L)

lemma uncyclicmid {α : Type*} [DecidableEq α] (L₁ L₂ : List (α × Bool)) (h : cycreduced L₁): (IsRed (L₂ ++ L₁)) ∨ (IsRed (L₁ ++ FreeGroup.invRev L₂)) := by sorry

lemma technique {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧(IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by sorry




namespace FreeGroup

<<<<<<< Updated upstream
theorem IsRed_singleton {α : Type*} [DecidableEq α] (a : α × Bool) : IsRed [a] := by
  dsimp [IsRed]
  intro l
  exact Red.singleton_iff.mp

theorem IsRed_two {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : IsRed [a,b]) :
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
=======
lemma isredsubl {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : IsRed (P ++ Q)) : (IsRed P) ∧ (IsRed Q) := by exact ⟨IsRed.prefix_IsRed P Q h,IsRed.suffix_IsRed P Q h⟩

lemma red_join_at_nonempty_left {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P = []) (h₂ : Q ≠ []) : IsRed (P ++ Q) := by
  rw [h₁]; simp [List.nil_append]; exact hQ

lemma red_join_at_nonempty_right {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q = []) : IsRed (P ++ Q) := by
  rw [h₂]; simp [List.nil_append]; exact hP

lemma red_at_join_nonempty_both {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2  → IsRed (P ++ Q) := by
  induction P generalizing Q with
  | nil =>
    by_contra
    aesop
  | cons head tail ih =>
    specialize ih Q
    have this₁ : (head :: tail) = [head]++tail := by simp!
    rw [this₁] at hP

    have prelim : IsRed tail := by
      have hRed_and_tRed : IsRed [head] ∧ IsRed tail := by apply isredsubl [head] tail hP
      exact hRed_and_tRed.2
    simp [prelim, hQ] at ih
    have case_maker : tail = [] ∨ tail ≠ [] := by exact eq_or_ne tail []
    cases case_maker with
    | inl h =>
      rw [h] at hP; simp at hP
      simp [h]
      rw [equiv_of_reds]
      intros hypo₁
      rw [<-equiv_of_reds]
      exact (IsRed.cons_iff_not_red_pair Q h₂).mpr ⟨hQ,hypo₁⟩

    | inr h =>
      simp [h, h₂] at ih
      have tail_is_the_player : ((head :: tail).getLast h₁) = (tail.getLast h) := by exact List.getLast_cons h
      rw [tail_is_the_player]
      intro hypo_last
      apply ih at hypo_last
      rw [←this₁] at hP
      rw [IsRed.cons_iff_not_red_pair _ h] at hP
      exact (IsRed.cons_iff_not_red_pair (tail++Q) (List.append_ne_nil_of_left_ne_nil h Q)).mpr ⟨hypo_last,by convert hP.2 using 2 <;> simp [List.head_append,h]⟩

lemma join_is_red_then_safe {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) → (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
  intro hypo
  by_contra
  expose_names
  simp at h
  have P_is_like : P = (P.dropLast) ++ [P.getLast h₁] := by exact Eq.symm (List.dropLast_concat_getLast h₁)
  have Q_is_like : Q = [Q.head h₂] ++ Q.tail := by simp
  have P_end_end : (P.getLast h₁).2 ≠ (Q.head h₂).2 := by simp [h.2]
  have P_end_end_end : (P.getLast h₁).2 = !(Q.head h₂).2 := by exact Bool.eq_not.mpr P_end_end
  have P_end : [P.getLast h₁] = [((Q.head h₂).1, !(Q.head h₂).2)] := by calc
    [P.getLast h₁] = [((P.getLast h₁).1, (P.getLast h₁).2)] := by simp
    _ = [((Q.head h₂).1, !(Q.head h₂).2)] := by
      rw [h.1]
      rw [P_end_end_end]
  have Q_end : [Q.head h₂] = [((Q.head h₂).1, (Q.head h₂).2)] := by simp
  have this₁ : (P ++ Q) = P.dropLast ++ [((Q.head h₂).1, !(Q.head h₂).2)] ++ [((Q.head h₂).1, (Q.head h₂).2)] ++ Q.tail := by
    nth_rewrite 1 [P_is_like, Q_is_like, P_end, Q_end]
    simp
  have scandal : [((Q.head h₂).1, (Q.head h₂).2)] = FreeGroup.invRev [((Q.head h₂).1, !(Q.head h₂).2)] := by
    unfold FreeGroup.invRev
    simp
  rw [scandal] at this₁
  have this₂ : FreeGroup.reduce (P.dropLast ++ [((Q.head h₂).1, !(Q.head h₂).2)] ++ FreeGroup.invRev [((Q.head h₂).1, !(Q.head h₂).2)] ++ Q.tail) = FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce Q.tail) := by rw [distrib_reduce (P.dropLast) [((Q.head h₂).1, !(Q.head h₂).2)] Q.tail]

  rw [<-scandal] at this₁ this₂
  rw [<- this₁] at this₂
  rw [equiv_of_reds] at hypo
  rw [hypo] at this₂
  let n₁ : ℕ := P.length
  let n₂ : ℕ := Q.length
  have a₁ : P.length > (P.dropLast).length := by calc
    P.length = (P.dropLast ++ [P.getLast h₁]).length := by exact congrArg List.length P_is_like
    _ = (P.dropLast).length + [P.getLast h₁].length := by exact List.length_append
    _ > (P.dropLast).length := by simp
  have a₂ : Q.length > (Q.tail).length := by calc
    Q.length = ([Q.head h₂] ++ (Q.tail)).length := by simp
    _ = [Q.head h₂].length + Q.tail.length := by exact List.length_append
    _ > Q.tail.length := by simp
  have a₃ : FreeGroup.Red (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail) (FreeGroup.reduce (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) := by exact
    FreeGroup.reduce.red
  have a₄ : ∃ n, List.length ((FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) = List.length (FreeGroup.reduce (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) + 2 * n := by exact FreeGroup.Red.length a₃
  rcases a₄ with ⟨m, a₄⟩
  have a₅_1 : FreeGroup.Red P.dropLast (FreeGroup.reduce P.dropLast) := by exact FreeGroup.reduce.red
  have a₅_2 : ∃ n, List.length (P.dropLast) = List.length ((FreeGroup.reduce P.dropLast)) + 2 * n := by exact FreeGroup.Red.length a₅_1
  rcases a₅_2 with ⟨m₁, a₅⟩
  have a₆_1 : FreeGroup.Red Q.tail (FreeGroup.reduce Q.tail) := by exact FreeGroup.reduce.red
  have a₆_2 : ∃ n, List.length (Q.tail) = List.length ((FreeGroup.reduce Q.tail)) + 2 * n := by exact FreeGroup.Red.length a₆_1
  rcases a₆_2 with ⟨m₂, a₆⟩
  have a₇ : (P ++ Q).length > (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail).length := by calc
    (P ++ Q).length = P.length + Q.length := by simp!
    _ > P.length + Q.tail.length := by linarith [a₂]
    _ > P.dropLast.length + Q.tail.length := by linarith
    _ >= (FreeGroup.reduce (P.dropLast)).length + (FreeGroup.reduce (Q.tail)).length := by linarith
    _ = (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)).length := by exact Eq.symm List.length_append
  have a₈_1 : FreeGroup.Red (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)) (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))) := by exact FreeGroup.reduce.red
  have a₈_2 : ∃ n, List.length (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)) = List.length ((FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)))) + 2 * n := by exact FreeGroup.Red.length a₈_1
  rcases a₈_2 with ⟨m₃, a₈⟩
  have a₉ : (P ++ Q).length > (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))).length := by linarith
  have a₀ : (P ++ Q).length = (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))).length := by exact congrArg List.length this₂
  linarith

lemma join_red_iff_safe {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) ↔ (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
  constructor
  exact fun a ↦ join_is_red_then_safe P Q hP hQ h₁ h₂ a
  exact fun a ↦ red_at_join_nonempty_both P Q hP hQ h₁ h₂ a

lemma app_red_still_red {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)) (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) (h₃ : Q ≠ []): (IsRed (P++Q++R)) := by
  have Pcases : (P = []) ∨ (P ≠ []) := by exact eq_or_ne P []
  have Rcases : (R = []) ∨ (R ≠ []) := by exact eq_or_ne R []
  cases Pcases with
  | inl h =>
    cases Rcases with
    | inl h =>
      expose_names
      aesop
    | inr h =>
      expose_names
      aesop
  | inr h =>
    cases Rcases with
    | inl h =>
      expose_names
      aesop
    | inr h =>
      expose_names
      have QRne : Q ++ R ≠ [] := by exact List.append_ne_nil_of_left_ne_nil h₃ R
      have main : (Q ++ R).head QRne= Q.head h₃ := by simp [h₃]
      have this : IsRed (P ++ (Q ++ R)) := by
        rw [join_red_iff_safe]
        rw [main]
        rw [<-join_red_iff_safe]
        exact h₁
        exact hp
        exact hq
        exact h_1
        exact hp
        exact h₂
      simp [this]

-- extremely important

lemma uncyc_then_comm_lists₁ {α : Type*} [DecidableEq α] (P : List (α × Bool)) : ∀ K, K~r P → cycreduced (P) → cycreduced (K) := by
  induction P with
  | nil => sorry
  | cons head tail ih =>
    intro hd hypo
    specialize ih hd; specialize ih
    sorry
-- extremely important

lemma uncyc_then_comm_lists₂ {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : cycreduced (P ++ Q) → cycreduced (Q ++ P) := by sorry
-- need this exactly in proof, don't remove for now.


-- is done by vivek



lemma inv_of_red {α : Type*} [DecidableEq α] (P : List (α × Bool)) : IsRed P → IsRed (FreeGroup.invRev P) := by
  intro hypo
  rw [equiv_of_reds] at hypo ⊢
  rw [FreeGroup.reduce_invRev, hypo]

lemma appnonempty_then_some_nonempty {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : P ++ Q ≠ []) : (P ≠ []) ∨ (Q ≠ []) := by
  apply Decidable.not_and_iff_or_not.mp ?_
  by_contra
  expose_names
  have : P ++ Q = [] := by calc
    P ++ Q = [] ++ [] := by rw [h_1.1, h_1.2]
    _ = [] := by simp
>>>>>>> Stashed changes
  contradiction

-- theorem IsRed_cons {α : Type*} [DecidableEq α] (a : α × Bool) (l : List (α × Bool)) (hl : l ≠ []) (h : IsRed (a::l)) :
--   IsRed l ∧ (a.1 ≠ (l.head hl).1 ∨ a.2 = (l.head hl).2) := by
--   induction l generalizing a with
--   | nil => contradiction
--   | cons hd tl ih =>

theorem Red_infix {α : Type*} [DecidableEq α] (l1 l2 l2' l3 : List (α × Bool)) (hl2 : Red l2 l2' ∧ l2' ≠ l2) :
  Red (l1++l2++l3) (l1++(l2')++l3) := by
  apply Red.append_append
  apply Red.append_append
  rfl; exact hl2.1; rfl

lemma IsRed_append1 {α : Type*} [DecidableEq α] (l1 l2 : List (α × Bool)) (hL : IsRed (l1++l2)) : IsRed l1 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (P++l2)
  have h1 : Red (l1 ++ l2) (P ++ l2) := by refine Red.append_append hP (Red.refl)
  apply hL at h1
  exact app_lists_eq_canc_r P l2 l1 h1

lemma IsRed_append2 {α : Type*} [DecidableEq α] (l1 l2 : List (α × Bool)) (hL : IsRed (l1++l2)) : IsRed l2 := by
  rw [IsRed] at *
  intro P hP
  specialize hL (l1++P)
  have h1 : Red (l1 ++ l2) (l1++P) := by refine Red.append_append (Red.refl) hP
  apply hL at h1
  exact app_lists_eq_canc_l P l1 l2 h1

theorem IsRed_append {α : Type*} [DecidableEq α] (l1 l2 : List (α × Bool)) (hL : IsRed (l1++l2)) : IsRed l1 ∧ IsRed l2 :=
  ⟨IsRed_append1 l1 l2 hL,IsRed_append2 l1 l2 hL⟩

lemma IsRed_tail {α : Type*} [DecidableEq α] (a : α × Bool) (l : List (α × Bool)) (h : IsRed (a::l)) :
  IsRed l := by
  have h1 : a::l = [a]++l := rfl
  rw [h1] at h
  apply IsRed_append at h
  exact h.2

theorem IsRed_cons_cons {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (h : IsRed (a::b::l)) :
  IsRed (b::l) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  induction l with
  | nil =>
    apply IsRed_two at h
    simp [h,IsRed_singleton]
  | cons hd tl ih =>
    constructor
    · exact IsRed_tail a (b :: hd :: tl) h
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
      nth_rw 1 [← add_zero tl.length] at h5
      rw [add_assoc] at h5
      norm_num at h5

theorem IsRed_cons {α : Type*} [DecidableEq α] (a : α × Bool) (l : List (α × Bool)) (hl : l ≠ []) (h : IsRed (a::l)) :
  IsRed l ∧ (a.1 ≠ (l.head hl).1 ∨ a.2 = (l.head hl).2) := by
  match l with
  | [] => contradiction
  | b::bs => exact IsRed_cons_cons a b bs h

#check Red.Step.cons_left_iff
-- #check rtc.induct

-- theorem IsRed_step_same {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
--   IsRed l → ∀ l', Red.Step l l' → l' = l := by
--   constructor
--   · intro h p hp
--     apply Red.Step.to_red at hp
--     exact h p hp
--   · intro h p hp
--     specialize h p
--     apply h
--     induction hp using Relation.ReflTransGen.rec with
--     | refl => sorry
--     | tail h1 h2 ih =>
--       expose_names

--       sorry

--     sorry

-- lemma Red_cons_if {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (h : Red (a::b::l) l) :
--   a.1 = b.1 ∧ a.2 = !b.2 := by
--   let (x,y) := a
--   simp
--   -- have h2 := Red.Step.cons_left_iff {a:=x} {b:=y} {L₁ := b::l} {L₂ := l}
--   sorry
  -- by_contra h1
  -- push_neg at h1
  -- let (x,y) := a
  -- have h2 : b = (x,!y) := by
  --   simp at h1
  --   apply Prod.ext_iff.mpr
  --   simp [h1]
  -- rw [IsRed] at hl
  -- contrapose hl
  -- push_neg at *

lemma IsRed_two_not_if {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed [a,b] := by
  contrapose hab
  rw [not_and_or]
  push_neg at hab
  convert IsRed_two _ _ hab; simp

#check Red.singleton_iff

lemma Red_two_l1 {α : Type*} [DecidableEq α] (a b : α × Bool) (h : Red [a,b] []) :
  a.1 = b.1 ∧ a.2 = !b.2 := by
  let (x,y) := a
  rw [Red.cons_nil_iff_singleton,Red.singleton_iff] at h
  simp at h
  simp [← h]

lemma Red_two_l2 {α : Type*} [DecidableEq α] (a b : α × Bool) (h : a.1 = b.1 ∧ a.2 = !b.2) :
  Red [a,b] [] := by
  let (x,y) := a
  have h1 : b = (x,!y) := by
    simp at h
    apply Prod.ext_iff.mpr
    simp [h]
  rw [h1]
  exact Red.cons_nil_iff_singleton.mpr (Red.singleton_iff.mpr rfl)

theorem Red_two_nil_iff {α : Type*} [DecidableEq α] (a b : α × Bool) : Red [a,b] [] ↔ a.1 = b.1 ∧ a.2 = !b.2 :=
  ⟨fun h => Red_two_l1 a b h,fun h => Red_two_l2 a b h⟩

-- theorem Red.Step.length_eq_iff {α : Type*} [DecidableEq α] (L1 L2 : List (α×Bool)) (h1 : Red.Step L1 L2) (h2 : L1.length = L2.length) :
--   L1 = L2 := by

theorem Red.length_eq_iff {α : Type*} [DecidableEq α] (L1 L2 : List (α×Bool)) (h1 : Red L1 L2) (h2 : L1.length = L2.length) :
  L1 = L2 := by
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

-- lemma Red_two_l5 {α : Type*} [DecidableEq α] (a b x y : α × Bool) (L : List (α×Bool)) (hab : a.1 = b.1 ∧ a.2 = !b.2) (h : Red [a,b] L) : L = [] := by
--   match L with
--   | [] => rfl
--   | [x] =>
--     have h1 := Red.length h
--     obtain ⟨n,hn⟩ := h1
--     simp at hn
--     have h2 : 2*n = 1 := by linarith
--     have h3 : 2*n ≠ 1 := by norm_num
--     contradiction
--   | [x,y] =>
--     sorry
--   | x::y::z::xs =>
--     have h1 := Red.length_le h
--     simp at h1



lemma Red_two_l3 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α×Bool)) (h : Red [a,b] l) (hl : l.length < 2) :
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

-- #check Red.red_iff_irreducible
-- #check Red.Step.cons_not

-- lemma Red_two_l4 {α : Type*} [DecidableEq α] (a b x y : α × Bool) (h : Red [a,b] [x,y]) : x=a ∧ y=b := by
--   let (x1,b1) := a
--   let (x2,b2) := b
--   by_cases h1 : (x1,!b1) = (x2,b2)
--   · rw [← h1] at h
--     have h2 : Red.Step [(x1, b1), (x1, !b1)] [] := Red.Step.cons_not
--     sorry
--   · have h2 := (Red.red_iff_irreducible (L:=[x,y]) h1).mp
--     simp at h2
--     exact h2 h


lemma Red_two_l6 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α×Bool)) (h : Red [a,b] l) (hl : l ≠ [a,b]) :
  l = [] := by
  have h1 := Red.length_le h
  simp at h1
  rw [le_iff_eq_or_lt] at h1
  rcases h1 with h1|h2
  · have h2 : 2 = [a,b].length := by simp
    rw [h2] at h1
    have h3 := Red.length_eq_iff _ _ h
    symm at h1 hl
    apply h3 at h1
    contradiction
  · exact Red_two_l3 a b l h h2

theorem Red_two_if {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α×Bool)) (h : Red [a,b] l) :
  (l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2) ∨ (l = [a,b]) := by
  by_cases h1 : l = [a,b]
  · right; assumption
  · left
    have h2 := Red_two_l6 a b l h h1
    rw [h2] at h
    have h3 := Red_two_l1 a b h
    exact ⟨h2,h3⟩

lemma Red_two_l7 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α×Bool)) (h1 : Red [a,b] l) (h2 : l ≠ [a,b]) :
  l = [] ∧ a.1 = b.1 ∧ a.2 = !b.2 := by
  rcases Red_two_if a b l h1 with h1|h1
  · exact h1
  · contradiction

lemma IsRed_two_if1 {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 ≠ b.1) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push_neg at *
  rcases hab with ⟨p,hp1,hp2⟩
  exact (Red_two_l7 a b p hp1 hp2).2.1

lemma IsRed_two_if2 {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.2 = b.2) :
  IsRed [a,b] := by
  contrapose hab
  rw [IsRed] at hab
  push_neg at *
  rcases hab with ⟨p,hp1,hp2⟩
  rw [← Bool.eq_not_iff]
  exact (Red_two_l7 a b p hp1 hp2).2.2

theorem IsRed_two_iff {α : Type*} [DecidableEq α] (a b : α × Bool) : IsRed [a,b] ↔ (a.1 ≠ b.1 ∨ a.2 = b.2) := by
  constructor
  · intro h
    exact IsRed_two a b h
  · intro h
    rcases h with h|h
    · exact IsRed_two_if1 a b h
    · exact IsRed_two_if2 a b h

lemma Red.Step.irrefl {α : Type*} [DecidableEq α] (l : List (α × Bool)) : ¬Step l l := by
  intro h
  have h1 := Red.Step.length h
  linarith

lemma Red.Step.not_self {α : Type*} [DecidableEq α] (l l' : List (α × Bool)) (h : Step l l') : l' ≠ l := by
  intro h1
  have h2 := Red.Step.length h
  rw [h1] at h2
  linarith

lemma Red.not_self_imp_step {α : Type*} [DecidableEq α] (l l' : List (α × Bool)) (h1 : Red l l') (h2 : l ≠ l') :
  ∃ p, Red.Step l p := by
  induction h1 with
  | refl => contradiction
  | tail h1 h2 ih =>
    expose_names
    by_cases hl : l=b
    · rw [← hl] at h2_1
      use c
    · exact ih hl

theorem IsRed_iff_noStep {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  IsRed l ↔ ∀ l', ¬Red.Step l l' := by
  constructor
  · intro h p hp
    have h1 : l ≠ p := by exact Ne.symm (Red.Step.not_self l p hp)
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

lemma IsRed_nil {α : Type*} [DecidableEq α] : IsRed ([] : List (α×Bool)) := by
  intro l hl
  exact Red.nil_iff.mp hl

lemma IsRed_two_not {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) :
  ¬IsRed [a,b] := by
  let (x,y) := a
  have h1 : b = (x,!y) := by
    simp at hab
    apply Prod.ext_iff.mpr
    simp [hab]
  rw [h1]
  simp [IsRed]
  use []
  simp
  rw [Red.cons_nil_iff_singleton]

lemma IsRed_not_append_left {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) (l : List (α × Bool)) :
  ¬IsRed (l++[a,b]) := by
  induction l with
  | nil => simp [IsRed_two_not a b hab]
  | cons x xs ih =>
    contrapose ih
    push_neg at *
    exact IsRed_tail x (xs ++ [a, b]) ih

lemma IsRed_not_append_right {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) (l : List (α × Bool)) :
  ¬IsRed ([a,b]++l) := by
  induction l using List.reverseRecOn with
  | nil => simp [IsRed_two_not_if a b hab]
  | append_singleton l x ih =>
    rw [← List.append_assoc]
    contrapose ih
    push_neg at *
    exact IsRed_append1 ([a, b] ++ l) [x] ih

lemma IsRed_not_if {α : Type*} [DecidableEq α] (a b : α × Bool) (hab : a.1 = b.1 ∧ a.2 = !b.2) (l1 l2 : List (α × Bool)) :
  ¬IsRed (l1++[a,b]++l2) := by
  match l1 with
  | [] => simp; exact IsRed_not_append_right a b hab l2
  | x::xs =>
    induction l2 using List.reverseRecOn with
    | nil => simp; rw [← List.cons_append]; exact IsRed_not_append_left a b hab (x::xs)
    | append_singleton ys y ih =>
      have h1 : x :: xs ++ [a, b] ++ ys = [x] ++ xs ++ [a, b] ++ ys := by simp
      rw [h1] at ih
      have h2 : x :: xs ++ [a, b] ++ (ys ++ [y]) = [x] ++ xs ++ [a, b] ++ ys ++ [y] := by simp
      rw [h2]
      contrapose ih
      push_neg at *
      exact IsRed_append1 ([x] ++ xs ++ [a, b] ++ ys) [y] ih

lemma Red.Step.condition_l1 {α : Type*} [DecidableEq α] (l : List (α × Bool)) (h : ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2)) :
  (∃ l', Red.Step l l') := by
  rcases h with ⟨l1,l2,a,b,h⟩
  use (l1++l2)
  rw [h]
  simp

lemma Red.Step.condition_l2 {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  (∃ l', Red.Step l l') → ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool),
  l = (l1 ++ (x, b) :: (x, !b) :: l2) := by
  intro h
  rcases h with ⟨l',hl'⟩
  induction hl' with
  | not =>
    expose_names
    use L₁
    use L₂
    use x
    use b

lemma Red.Step.condition {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  (∃ l', Red.Step l l') ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2) :=
  ⟨Red.Step.condition_l2 l,Red.Step.condition_l1 l⟩

-- lemma Red.Step.condition {α : Type*} [DecidableEq α] (l l' : List (α × Bool)) :
--   Red.Step l l' → ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, !b) :: l2) := by
--   intro h
--   induction l generalizing l' with
--   | nil =>
--     have := IsRed_nil (α:=α)
--     rw [IsRed_iff_noStep] at this
--     specialize this l'
--     contradiction
--   | cons a as ih =>
--     by_cases hp: ∃ p, Step as p
--     · rcases hp with ⟨p,hp⟩
--       rcases ih p hp with ⟨l1,l2,r,s,h⟩
--       use a::l1
--       use l2
--       use r
--       use s
--       simp [h]
--     · push_neg at hp
--       rw [← IsRed_iff_noStep] at hp
--       sorry
--   -- · intro hl
--   --   rcases hl with ⟨l1,l2,a,b,h⟩
--   --   rw [h.1,h.2]
--   --   simp

theorem IsRed_not_iff {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  ¬IsRed l ↔ ∃ (l1 l2 : List (α×Bool)) (x : α) (b : Bool), l = (l1 ++ (x, b) :: (x, not b) :: l2) := by
  constructor
  · intro hl
    rw [IsRed_iff_noStep] at hl
    push_neg at hl
    rw [Red.Step.condition] at hl
    exact hl
  · intro hl
    rcases hl with ⟨l1,l2,a,b,h⟩
    rw [h]
    set x := (a,b) with hx
    set y := (a,!b) with hy
    have : l1 ++ x :: y :: l2 = l1++[x,y]++l2 := by simp
    rw [this]
    refine IsRed_not_if x y (by simp [hx,hy]) l1 l2

lemma IsRed_three_iff_pair {α : Type*} [DecidableEq α] (a b c : α × Bool) : IsRed [a,b,c] ↔ IsRed [a,b] ∧ IsRed [b,c] := by
  constructor
  · intro h
    constructor
    · exact IsRed_append1 [a, b] [c] h
    · exact IsRed_tail a [b, c] h
  · intro ⟨h1,h2⟩
    rw [IsRed_two_iff] at h1 h2
    rcases h1 with h1|h1
    · sorry
    · sorry

theorem IsRed_cons_if1 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (hab : a.1 ≠ b.1) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact IsRed_two_if1 a b hab
  | cons x xs ih =>
    contrapose hl
    rw [IsRed_iff_noStep] at hl ⊢
    push_neg at hl ⊢
    rw [Red.Step.condition] at hl ⊢
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

theorem IsRed_cons_if2 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (hab : a.2 = b.2) :
  IsRed (a::b::l) := by
  induction l generalizing a b with
  | nil => exact IsRed_two_if2 a b hab
  | cons x xs ih =>
    contrapose hl
    rw [IsRed_iff_noStep] at hl ⊢
    push_neg at hl ⊢
    rw [Red.Step.condition] at hl ⊢
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

def IsRed' {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | a::b::as =>
    IsRed' (b::as) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2)

theorem IsRed_same {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L ↔ IsRed' L := by
  constructor
  · intro h
    induction L using IsRed'.induct with
    | case1 => rw [IsRed']; tauto
    | case2 _ => rw [IsRed']; tauto
    | case3 a b bs ih =>
      rw [IsRed']
      have h1 : IsRed (b::bs) := IsRed_tail _ _ h
      apply ih at h1
      exact ⟨h1,(IsRed_cons _ _ (List.cons_ne_nil b bs) h).2⟩
  · intro h
    induction L using IsRed'.induct with
    | case1 => exact (equiv_of_reds []).mpr rfl
    | case2 b => exact IsRed_singleton b
    | case3 a b as ih =>
      rw [IsRed'] at h
      have h1 := ih h.1
      rcases h.2 with h2|h2
      · exact IsRed_cons_if1 a b as h1 h2
      · exact IsRed_cons_if2 a b as h1 h2

end FreeGroup



lemma subword_of_red_red {α : Type*} [DecidableEq α] (L l : List (α × Bool)) (hl : List.IsInfix l L) (hL : IsRed L) :
  IsRed L := by sorry

lemma app_red_still_red {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)) (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) : (IsRed (P++Q++R)) := by sorry

-- lemma uncyc_on_conj {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : Uncycle (P ++ Q ++ FreeGroup.invRev P) = Uncycle Q := by sorry

lemma uncyc_red_isrotated_red_uncyc {α : Type*} [DecidableEq α] : ∀ (g x  : FreeGroup α), (xhypo : cycreduced x.toWord) → (Uncycle ((g*x*g⁻¹).toWord)) ~r (FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord))) := by
  intro g x
  rw [form_of_conj]
  let Lg := g.toWord
  let Lx := x.toWord
  have : g⁻¹.toWord = FreeGroup.invRev g.toWord := by exact FreeGroup.toWord_inv g
  have gRed : IsRed g.toWord := by apply (equiv_of_reds g.toWord).mpr; exact FreeGroup.reduce_toWord g

  have key : FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (x.toWord)) := by calc
    FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ FreeGroup.invRev g.toWord)) := by exact congrArg FreeGroup.reduce (congrArg Uncycle (congrArg (HAppend.hAppend (g.toWord ++ x.toWord)) this))
    _ = FreeGroup.reduce (Uncycle x.toWord) := by rw [uncyc_on_conj g.toWord x.toWord]

  rw [this]
  rw [uncyc_on_conj]
  /-
  induction g.toWord with
  | nil =>
    simp
    have this₁ : IsRed x.toWord := by simp [(equiv_of_reds x.toWord)]
    have this₂ : IsRed (Uncycle x.toWord) := by
      simp [uncyc_of_red_is_red x.toWord this₁]
    simp [equiv_of_reds x.toWord] at this₂
    have this₃ : FreeGroup.reduce (Uncycle x.toWord) = (Uncycle x.toWord) := by exact (equiv_of_reds (Uncycle x.toWord)).mp this₂
    rw [this₃]
    intro dd
    aesop
  | cons head tail ih =>
    intro CC'
    unfold cycreduced at CC'
    have CC : cycreduced x.toWord := by exact CC'
    rcases CC' with ⟨xisred, xisuncyclic⟩
    rw [xisuncyclic]
    apply (equiv_of_reds x.toWord).mp at xisred; simp only [xisred]
    have xisred' : IsRed x.toWord := by exact(equiv_of_reds x.toWord).mpr xisred
    have mylem : IsRed (head :: tail ++ x.toWord) ∨ IsRed (x.toWord ++ FreeGroup.invRev (head :: tail)) := by
      exact uncyclicmid x.toWord (head :: tail) CC
    -/




  cases h_g: g.toWord with
  | nil =>
      simp
      have this₁ : IsRed x.toWord := by simp [(equiv_of_reds x.toWord)]
      have this₂ : IsRed (Uncycle x.toWord) := by
        simp [uncyc_of_red_is_red x.toWord this₁]
      simp [equiv_of_reds x.toWord] at this₂
      have this₃ : FreeGroup.reduce (Uncycle x.toWord) = (Uncycle x.toWord) := by exact (equiv_of_reds (Uncycle x.toWord)).mp this₂
      rw [this₃]
      intro dd
      aesop
  | cons head tail =>
    intro CC'
    unfold cycreduced at CC'
    have CC : cycreduced x.toWord := by exact CC'
    rcases CC' with ⟨xisred, xisuncyclic⟩
    rw [xisuncyclic]
    apply (equiv_of_reds x.toWord).mp at xisred; simp only [xisred]
    have xisred' : IsRed x.toWord := by exact(equiv_of_reds x.toWord).mpr xisred
    have mylem : IsRed (head :: tail ++ x.toWord) ∨ IsRed (x.toWord ++ FreeGroup.invRev (head :: tail)) := by
      exact uncyclicmid x.toWord (head :: tail) CC
    cases mylem with
    | inl h =>
      by_cases h : IsRed (x.toWord ++ FreeGroup.invRev g.toWord)
      rw [h_g] at h
      rw [h_g] at gRed
      have htinvred : IsRed (FreeGroup.invRev (head :: tail)) := by
        apply (equiv_of_reds (FreeGroup.invRev (head :: tail))).mpr
        rw [FreeGroup.reduce_invRev]
        rw [equiv_of_reds] at gRed
        rw [gRed]
      · expose_names
           -- how to prove, if we're taking cases over g.toWord, then gRed should carry over to (head :: tail), right?
        have this₁ : IsRed (head :: tail ++ x.toWord ++ FreeGroup.invRev (head :: tail)) := by exact app_red_still_red (head :: tail) x.toWord (FreeGroup.invRev (head :: tail)) gRed xisred' htinvred h_1 h
        rw [equiv_of_reds] at this₁
        rw [this₁]
        rw [uncyc_on_conj (head :: tail) x.toWord]
        rw [xisuncyclic]
      · sorry
    | inr h => sorry







lemma Uncycleconj_is_reduced_cperm {α : Type*} [DecidableEq α] : ∀ (g y : FreeGroup α), Uncycle (g*y*g⁻¹).toWord ∈ List.map FreeGroup.reduce (y.toWord).cyclicPermutations := by
  intros g y
  rw [form_of_conj]
  simp
  let conju := FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord)
  let r := conju.head (by sorry)

  sorry


-- cycperm is a conj
-- uncyc is a conj
-- cycred is a conj
-- use cyclically reduced things. formalize cycreduced, reduced.

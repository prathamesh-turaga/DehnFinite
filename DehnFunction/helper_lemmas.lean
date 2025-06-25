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

theorem IsRed_append {α : Type*} [DecidableEq α] (l1 l2 : List (α × Bool)) (hL : IsRed (l1++l2)) : IsRed l1 ∧ IsRed l2 := by
  constructor
  · rw [IsRed] at *
    intro P hP
    specialize hL (P++l2)
    have h1 : Red (l1 ++ l2) (P ++ l2) := by refine Red.append_append hP (Red.refl)
    apply hL at h1
    exact app_lists_eq_canc_r P l2 l1 h1
  · rw [IsRed] at *
    intro P hP
    specialize hL (l1++P)
    have h1 : Red (l1 ++ l2) (l1++P) := by refine Red.append_append (Red.refl) hP
    apply hL at h1
    exact app_lists_eq_canc_l P l1 l2 h1

lemma IsRed_cons_aux {α : Type*} [DecidableEq α] (a : α × Bool) (l : List (α × Bool)) (h : IsRed (a::l)) :
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
    · exact IsRed_cons_aux a (b :: hd :: tl) h
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

theorem IsRed_step_same {α : Type*} [DecidableEq α] (l : List (α × Bool)) :
  IsRed l ↔ ∀ l', Red.Step l l' → l' = l := by
  constructor
  · intro h p hp
    apply Red.Step.to_red at hp
    exact h p hp
  · intro h p hp
    specialize h p
    apply h
    rw [Red] at hp

lemma Red_cons_if {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (h : Red (a::b::l) l) :
  a.1 = b.1 ∧ a.2 = !b.2 := by
  let (x,y) := a
  simp
  -- have h2 := Red.Step.cons_left_iff {a:=x} {b:=y} {L₁ := b::l} {L₂ := l}
  sorry
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




theorem IsRed_cons_if1 {α : Type*} [DecidableEq α] (a b : α × Bool) (l : List (α × Bool)) (hl : IsRed (b::l)) (hab : a.1 ≠ b.1) :
  IsRed (a::b::l) := by
  rw [IsRed]
  by_contra h1
  push_neg at h1
  rcases h1 with ⟨p,hp1,hp2⟩



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
      have h1 : IsRed (b::bs) := IsRed_cons_aux _ _ h
      apply ih at h1
      exact ⟨h1,(IsRed_cons _ _ (List.cons_ne_nil b bs) h).2⟩
  · intro h
    induction L using IsRed'.induct with
    | case1 => exact (equiv_of_reds []).mpr rfl
    | case2 b => exact IsRed_singleton b
    | case3 a b as ih =>
      rw [IsRed'] at h
      have := ih h.1
      by_contra h1
      rw [IsRed] at h1
      push_neg at h1
      rcases h1 with ⟨P,hP1,hP2⟩

      sorry
    -- induction L with
    -- | nil => exact (equiv_of_reds []).mpr rfl
    -- | cons a as ih =>

    --   sorry
    -- by_contra h1
    -- rw [IsRed] at h1
    -- push_neg at h1



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

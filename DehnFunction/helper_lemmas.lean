import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.List.Rotate
import DehnFunction.Area1

def Uncycle {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
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




def CycRed {α : Type*} [DecidableEq α] (w : FreeGroup α) := FreeGroup.mk (Uncycle (FreeGroup.toWord w))
--Cyclically reduces a freeword

def CyclicPermutationsOfRelators {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) : Set (FreeGroup G) :=

  ⋃ r ∈ R,
    { elem |
      ∃ word ∈ (FreeGroup.toWord r).cyclicPermutations,
      elem = FreeGroup.mk word
    }


def step {γ : Type*} [DecidableEq γ] (RelatorSet : Set (FreeGroup γ)) (w₁ w₂ : FreeGroup γ) : Prop :=
  ((CycRed (w₁ * w₂⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet) ∨ ((CycRed (w₂ * w₁⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet)

theorem step_iff_conjugate {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} (x y : FreeGroup G):
    (step R x y) ↔
  x*y⁻¹ ∈ Group.conjugatesOfSet R ∨ y*x⁻¹ ∈ Group.conjugatesOfSet R := by
    sorry

theorem Uncycle_property {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    ∃ (U V : List (α × Bool)), L = U ++ Uncycle L ++ V ∧ FreeGroup.mk (V ++ U) = 1 := by

  match h_L_eq : L with

  | [] =>

    use [], []
    simp
    constructor
    . unfold Uncycle
      simp
    .
     subst h_L_eq
     rfl


  | [x] =>
    use [], []
    simp
    constructor
    . unfold Uncycle
      simp
    .
     subst h_L_eq
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

      have ih := Uncycle_property middle
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


theorem cycRed_is_a_cyclic_permutation {G : Type*} [DecidableEq G] (y : FreeGroup G) :
  CycRed y ∈ CyclicPermutationsOfRelators {y} := by

  let L := FreeGroup.toWord y
  let M := Uncycle L
  unfold CyclicPermutationsOfRelators
  simp

  unfold CycRed

  have h_prop := Uncycle_property L
  rcases h_prop with ⟨U, V, h_decomp, h_vu_is_one⟩


  let p := M ++ V ++ U
  use p


  constructor

  · change p ~r L
    use (M ++ V).length
    dsimp [p]
    rw[h_decomp]
    have h_M_def: Uncycle L = M := by

      rfl
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




-- STUFF FROM AREA2



def CycReduce {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) := Uncycle (FreeGroup.reduce L)
-- Takes a list and returns cyclic reduction of that list's freely-reduced form.





-- reduced word a₁a₂...a_n is cycreduced iff it is reduced and ¬(a₁a_n = 1)

-- The last part can be said for the word as a list also. L represents a reduced word iff :
-- it is "reduced" (as a list, so would need to invoke standard free reduction somehow) and
-- (([L.head].mk) * ([L.getLast].mk) = 1)

-- Lemma : ∃! red and cycred reps for each equiv class that a FG constitutes.
-- pg 176 of pdf has an outline
-- Propn (w, w' cycreduced) : w.conj w' ↔ they are cyclically equivalent



--  have other₁ : True := sorry
--  simp [this₁, this₂, that₁, that₂, that₃]

lemma uncycle_LL_eq_uncycle_L {α : Type*} [DecidableEq α] (L : List (α × Bool)) (a : α) (b : Bool) :
    Uncycle ((a, b) :: L ++ [(a, !b)]) = Uncycle L := by
  -- First, handle the case where L is empty
  cases L with
  | nil =>
    simp [Uncycle]
  | cons hd tl =>
    have this₁: (hd :: (tl ++ [(a, !b)])).dropLast = (hd :: tl ++ [(a, !b)]).dropLast := by exact rfl
    have this₂ : (hd :: tl ++ [(a, !b)]).dropLast = (hd :: tl) := by exact List.dropLast_concat
    -- Now we can simplify the if statement
    have this₃ : (hd :: (tl ++ [(a, !b)])).dropLast = (hd :: tl) := by exact this₂
    -- For non-empty L, we need to analyze Uncycle's behavior
    simp [Uncycle]
    have last_eq : ((hd :: tl) ++ [(a, !b)]).getLast (by simp) = (a, !b) := by simp [this₁, this₂, this₃]
    -- The key step: the condition x.1 = last.1 ∧ x.2 ≠ last.2 is exactly true
    have cond_true : a = a ∧ b ≠ !b := by
      simp [Bool.not_eq_true']
    rw [this₃]

    -- The recursive call now works on the middle part, which is exactly L


lemma if_conj_then_cyc {α : Type*} [DecidableEq α] : ∀ (L : List (α × Bool)), ∀ p : α, ∀ b : Bool, Uncycle L = Uncycle ((p, b) :: L ++ [(p, !b)]) := by
  intros L p b
  simp
  let LL := ((p, b) :: L ++ [(p, !b)])
  rw [<- uncycle_LL_eq_uncycle_L L p b]
  unfold Uncycle
  simp


lemma star {α : Type*} [DecidableEq α]: ∀ (L : List (α × Bool)), (Uncycle (FreeGroup.reduce L)).IsRotated (FreeGroup.reduce (Uncycle L)) := by
  intros L
  induction Uncycle L with
  | nil => sorry
  | cons head tail ih =>
    simp [ih]
    sorry
#check List.rec

lemma form_of_conj {α : Type*} [DecidableEq α] (g y : FreeGroup α): (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]

def one_uncyc {α : Type*} [DecidableEq α] (L : List (α × Bool)) := FreeGroup.reduce (L.rotate 1)

#eval [1,2,3].rotate 3

lemma one_uncyc_lemma {α : Type*} [DecidableEq α] : ∀ (w : FreeGroup α), ∀ p : α, ∀ b : Bool, w.toWord = one_uncyc ((p, b) :: w.toWord ++ [(p, !b)]) := by
  intros w a b
  apply Eq.symm
  calc
    one_uncyc ((a, b) :: w.toWord ++ [(a, !b)]) = FreeGroup.reduce (w.toWord ++ [(a, !b), (a, b)]) := by
      unfold one_uncyc
      simp
    _ = FreeGroup.reduce (FreeGroup.reduce w.toWord ++ FreeGroup.reduce [(a, !b), (a, b)]) := by
      nth_rewrite 1 [<-FreeGroup.reduce_append_reduce_reduce]
      simp
    _ = FreeGroup.reduce (FreeGroup.reduce w.toWord) := by simp!
    _ = w.toWord := by simp!

def n_uncyc {α : Type*} [DecidableEq α] (L : List (α × Bool)) (n : ℕ) := FreeGroup.reduce (L.rotate n)

def uncyc2 {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with

  | [] => []

  | x :: xs =>
    List.reverseRecOn xs
    -- {motive : List (α×Bool) → List (α×Bool)}
    ([])
    (fun ys y ys_red => sorry)
    -- match xs with
    -- | [] => [x]
    -- | ys++[y] => sorry

lemma same_same_but_different {α : Type*} [DecidableEq α] : ∀ (w : FreeGroup α), ∀ p : α, ∀ b : Bool, one_uncyc ((p, b) :: w.toWord ++ [(p, !b)]) = Uncycle ((p, b) :: w.toWord ++ [(p, !b)]) := by
  intros w a b
  rw [<- one_uncyc_lemma]
  let L := w.toWord
  rw [<- if_conj_then_cyc]
  -- dsimp [Uncycle]
  sorry



lemma Uncycleconj_is_reduced_cperm {α : Type*} [DecidableEq α] : ∀ (g y : FreeGroup α), Uncycle (g*y*g⁻¹).toWord ∈ List.map FreeGroup.reduce (y.toWord).cyclicPermutations := by
  intros g y
  rw [form_of_conj]
  simp
  let conju := FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord)
  sorry

#check List.IsRotated






namespace FreeGroup

#check FreeGroup.reduce

def word_to_CycPermList {α : Type*} [DecidableEq α] (L : List (α×Bool)) : List (List (α × Bool)) := (List.map FreeGroup.reduce L.cyclicPermutations)

def IsCycPerm {α : Type*} [DecidableEq α] (L1 L2 : List (α×Bool)) : Prop :=
  (FreeGroup.reduce L1) ∈ (word_to_CycPermList L2)

section
variable {α : Type*} [DecidableEq α] (L1 L2 : List (α × Bool))
instance : Decidable (IsCycPerm L1 L2) :=
  inferInstanceAs (Decidable ((FreeGroup.reduce L1) ∈ (word_to_CycPermList L2)))
end

-- def IsReduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := FreeGroup.reduce L = L

@[simp]
def IsReduced {α : Type*} [DecidableEq α] (l : List (α × Bool)) : Prop :=
  ∀ l' : List (α×Bool), Red l l' → l' = l

theorem IsReduced_nil {α : Type*} [DecidableEq α] : IsReduced ([] : List (α×Bool)) := by
  dsimp [IsReduced]
  intro l
  exact Red.nil_iff.mp

def IsReduced' {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | a::b::as =>
    IsReduced' (b::as) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2)

theorem IsReduced_same {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsReduced L ↔ IsReduced' L := by
  constructor
  · intro h
    induction L using IsReduced'.induct with
    | case1 => rw [IsReduced']; tauto
    | case2 _ => rw [IsReduced']; tauto
    | case3 a b bs ih =>
      rw [IsReduced']
      rw [IsReduced] at h
      sorry
  · sorry

theorem IsReduced_singleton {α : Type*} [DecidableEq α] (a : α×Bool) : IsReduced [a] := by
  dsimp
  intro l
  exact Red.singleton_iff.mp

-- theorem IsReduced_two {α : Type*} [DecidableEq α] (a b : α×Bool) (h : IsReduced [a,b]) :
--   a.1 ≠ b.1 ∨ a.2 = b.2 := by dsimp [IsReduced] at h; exact h.2

-- theorem IsReduced_two_if {α : Type*} [DecidableEq α] (a b : α×Bool) (hab : a.1 ≠ b.1 ∨ a.2 = b.2) : IsReduced [a,b] := by simp [IsReduced,hab]

theorem IsReduced_cons_cons {α : Type*} [DecidableEq α] (a b : α×Bool) (as : List (α × Bool)) (h : IsReduced (a::b::as)) :
  IsReduced (b::as) ∧ (a.1 ≠ b.1 ∨ a.2 = b.2) := h

theorem IsReduced_cons {α : Type*} [DecidableEq α] (a : α×Bool) (as : List (α × Bool)) (has : as ≠ []) (h : IsReduced (a::as)) :
  IsReduced as ∧ (a.1 ≠ (as.head has).1 ∨ a.2 = (as.head has).2) := by
  match as with
  | b::bs =>
    apply IsReduced_cons_cons at h
    simp [h]

-- theorem IsReduced_cons_if1 {α : Type*} [DecidableEq α] (a b : α×Bool) (tl : List (α × Bool)) (htl : IsReduced tl) (hab : a.1 ≠ b.1) : IsReduced (a::b::tl) := by
--   rw [IsReduced]
--   simp [htl,hab]

-- theorem IsReduced_cons_if2 {α : Type*} [DecidableEq α] (a b : α×Bool) (tl : List (α × Bool)) (htl : IsReduced tl) (hab : a.2 = b.2) : IsReduced (a::b::tl) := by
--   rw [IsReduced]
--   simp [htl,hab]

-- #eval (FreeGroup.reduce [])

#print IsReduced

theorem IsReduced_cons_if {α : Type*} [DecidableEq α] (a : α×Bool) (as : List (α × Bool)) (has1 : IsReduced as) (has2 : as ≠ []) (ha : a.1 ≠ (as.head has2).1) : IsReduced (a::as) := by
  induction as using reduce.eq_1
  -- match as with
  -- | b::bs =>
  --   simp at ha
  --   rw [IsReduced]
  --   simp [has1,ha]








theorem IsReduced_iff_step_self {α : Type*} [DecidableEq α] (L : List (α×Bool)) : IsReduced L ↔ Red.Step L L




/-



lemma reduce_l1 {α : Type*} [DecidableEq α] (a b : α×Bool) (l : List (α × Bool)) (hl2 : reduce (b::l) = (b::l)) (hab : a.1 ≠ b.1) :
  reduce (a::b::l) = (a::b::l) := by
  simp [hl2,hab]

lemma reduce_l2 {α : Type*} [DecidableEq α] (a : α×Bool) (l : List (α × Bool)) (hl1 : l ≠ []) (hl2 : reduce l = l) (ha : a.1 ≠ (l.head hl1).1) :
  reduce (a::l) = a::l := by
  match l with
  | [] => contradiction
  | b::bs => exact reduce_l1 a b bs hl2 ha

-- theorem reduce_cons {α : Type*} [DecidableEq α] (a : α×Bool) (l : List (α × Bool)) (hl1 : l ≠ []) (ha = )

-- theorem reduce_length_le {α : Type*} [DecidableEq α] (l : List (α × Bool)) : (reduce l).length ≤ l.length := by
--   induction l with
--   | nil => simp
--   | cons a as ih =>
--     match as with
--     | [] => simp
--     | b::bs =>
--       rw [reduce.cons]
--       sorry
  -- match l with
  -- | [] => simp
  -- | [a] => simp
  -- | a::b::as =>
  --   rw [reduce.cons]
  --   by_cases hab : a.1 = b.1 ∧ a.2 = !b.2
  --   ·
  --   sorry

lemma reduce_l3 {α : Type*} [DecidableEq α] (a b : α×Bool) (l : List (α × Bool)) (hl : l ≠ []) (hab : a.1 ≠ b.1) (hbl : b.1 ≠ (l.head hl).1) :
  reduce (a::b::l) = a::(reduce (b::l)) := by
  -- induction l with
  -- | nil => contradiction
  -- | cons x xs ih =>
  --   sorry
  -- rw [reduce.cons]
  -- have h1 :
  sorry

-- lemma reduce_cons {α : Type*} [DecidableEq α] (a : α×Bool) (L : List (α × Bool)) (hL : (reduce L) ≠ []) (ha : a.1 ≠ ((reduce L).head hL).1) : reduce (a::L) = a::(reduce L) := by

theorem IsReduced_iff_reduce_eq_self {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsReduced L ↔ reduce L = L := by
  induction L using IsReduced.induct with
  | case1 => simp [IsReduced_nil]
  | case2 b => simp [IsReduced_singleton]
  | case3 a b bs ih =>
    by_cases hbs : bs = []
    · rw [hbs] at ih ⊢
      simp [IsReduced]
      tauto
    · constructor
      · intro h
        rw [IsReduced] at h
        have h1 := ih.1 h.1
        rw [reduce.cons,h1]
        simp
        intro h2 h3
        rcases h.2 with h4|h5
        · contradiction
        · rw [Bool.eq_not] at h3
          contradiction
      · intro h
        rw [IsReduced]

        have h1 : reduce (b::bs) = b::bs := by
          apply reduce.min
          apply Red.Step.to_red
          -- rw [Red.cons_cons_iff b]
        rw [reduce.cons] at h
        sorry

    -- dsimp [IsReduced] at hL
    -- have h1 := ih hL.1
    -- rw [reduce.cons]
    -- have h2 : ¬(x.1 = y.1 ∧ x.2 = !y.2) := by
    --   push_neg
    --   rw [@Bool.ne_not]
    --   have := hL.2
    --   rcases this with h3|h4
    --   · intro h; contradiction
    --   · exact fun _ ↦ h4
    -- -- rw [if_neg h2]
    -- sorry

theorem elt_isReduced {α : Type*} [DecidableEq α] (w : FreeGroup α) : IsReduced w.toWord := by
  dsimp [IsReduced]
  exact reduce_toWord w

-- theorem IsReduced_mk {α : Type*} [DecidableEq α] (L : List (α × Bool)) (hL : IsReduced L) : mk L =

theorem IsReduced_Reduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsReduced (reduce L) := by
  dsimp [IsReduced]
  exact reduce.idem

#check List.sublist_of_cons_sublist


theorem IsReduced_cons' {α : Type*} [DecidableEq α] (hd : α×Bool) (tl : List (α × Bool)) (h : IsReduced (hd::tl)) :
  IsReduced tl := by
  unfold IsReduced at h ⊢
  induction tl with
  | nil => simp
  | cons a as ih =>
    sorry


theorem IsReduced_subword {α : Type*} [DecidableEq α] (L : List (α × Bool)) (hL : IsReduced L) {l : List (α×Bool)} (hl : l.Sublist L): IsReduced l := by
  dsimp [IsReduced] at hL ⊢
  induction l with
  | nil => simp
  | cons a as ih =>
    have h1 := ih (List.sublist_of_cons_sublist hl)
    rw [reduce.cons,h1]
    match as with
    | [] => simp
    | b :: bs =>
      simp

theorem IsUncyclic_IsReduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsUncyclic L = IsReduced L := by sorry

theorem IsCycPerm_refl {α : Type*} [DecidableEq α] (L : List (α × Bool)) :IsCycPerm L L := by
  simp [IsCycPerm,word_to_CycPermList]
  use L

theorem IsCycPerm_symm_if_uncyclic {α : Type*} [DecidableEq α] (L1 L2 : List (α × Bool)) (hL1 : IsUncyclic L1) (hL2 : IsUncyclic L2) : IsCycPerm L1 L2 → IsCycPerm L2 L1 := by
  intro h
  simp [IsCycPerm,word_to_CycPermList] at h ⊢
  sorry
  -- exact fun a ↦ id (List.IsRotated.symm a)

theorem isCycPerm_trans {α : Type*} [DecidableEq α] (L1 L2 L3 : List (α × Bool)) (hL1 : uncyclic L1) (hL2 : uncyclic L2) (hL3 : uncyclic L3) :
  isCycPerm L1 L2 hL1 hL2 → isCycPerm L2 L3 hL2 hL3 → isCycPerm L1 L3 hL1 hL3 := by
  dsimp [isCycPerm]
  exact fun a a_1 ↦ List.IsRotated.trans a a_1

-- #synth Decidable (uncyclic L)

-- def FreeGroup.isCPerm {α : Type*} (w1 : FreeGroup )

-- def List.isCPerm {α : Type*} (L1 : List α) (L2 : List α) : Prop := L1 ∈ L2.cyclicPermutations
-- #check List.isro
-- theorem List.isCPerm_refl {α : Type*} (L1 : List α) : isCPerm



-/

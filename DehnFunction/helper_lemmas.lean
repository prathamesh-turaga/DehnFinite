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




def IsRed {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := ∀ J : List (α × Bool), FreeGroup.Red L J → J = L

lemma app_lists_eq_canc_r {k : Type*}: ∀ (P Q R : List k), P ++ Q = R ++ Q → P = R := by exact fun P Q R a ↦ List.append_cancel_right a
lemma app_lists_eq_canc_l {k : Type*}: ∀ (P Q R : List k), Q ++ P = Q ++ R → P = R := by exact fun P Q R a ↦ List.append_cancel_left a

lemma uncyc_is_sublist {α : Type*} [DecidableEq α]  (L : List (α × Bool)) : List.Sublist (Uncycle L) L := by sorry

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

lemma same_same_but_different {α : Type*} [DecidableEq α] : ∀ (w : FreeGroup α), ∀ p : α, ∀ b : Bool, Uncycle (one_uncyc ((p, b) :: w.toWord ++ [(p, !b)])) = Uncycle ((p, b) :: w.toWord ++ [(p, !b)]) := by
  intros w a b
  rw [<- one_uncyc_lemma]
  let L := w.toWord
  rw [<- if_conj_then_cyc]


def cycreduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := (IsRed L) ∧ (Uncycle L = L)

lemma uncyclicmid {α : Type*} [DecidableEq α] (g x : FreeGroup α) (h : cycreduced x.toWord): (IsRed (g.toWord ++ x.toWord)) ∨ (IsRed (x.toWord ++ FreeGroup.invRev g.toWord)) := by sorry

lemma technique {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧(IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by sorry

lemma app_red_still_red {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)) (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) : (IsRed (P++Q++R)) := by sorry

lemma uncyc_on_conj {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : Uncycle (P ++ Q ++ FreeGroup.invRev P) = Uncycle Q := by sorry

lemma uncyc_red_isrotated_red_uncyc {α : Type*} [DecidableEq α] : ∀ (g x  : FreeGroup α), /-cycreduced x.toWord,-/ (Uncycle ((g*x*g⁻¹).toWord)) ~r (FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord))) := by
  intro g x
  rw [form_of_conj]
  let Lg := g.toWord
  let Lx := x.toWord
  have : g⁻¹.toWord = FreeGroup.invRev g.toWord := by exact FreeGroup.toWord_inv g

  have key : FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (x.toWord)) := by calc
    FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ FreeGroup.invRev g.toWord)) := by exact congrArg FreeGroup.reduce (congrArg Uncycle (congrArg (HAppend.hAppend (g.toWord ++ x.toWord)) this))
    _ = FreeGroup.reduce (Uncycle x.toWord) := by rw [uncyc_on_conj g.toWord x.toWord]

  rw [this]
  rw [uncyc_on_conj]
  cases g.toWord with
  | nil =>
      simp
      have this₁ : IsRed x.toWord := by simp [(equiv_of_reds x.toWord)]
      have this₂ : IsRed (Uncycle x.toWord) := by
        simp [uncyc_of_red_is_red x.toWord this₁]
      simp [equiv_of_reds x.toWord] at this₂
      have this₃ : FreeGroup.reduce (Uncycle x.toWord) = (Uncycle x.toWord) := by exact (equiv_of_reds (Uncycle x.toWord)).mp this₂
      rw [this₃]
  | cons head tail => sorry







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

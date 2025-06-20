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

lemma same_same_but_different {α : Type*} [DecidableEq α] : ∀ (w : FreeGroup α), ∀ p : α, ∀ b : Bool, one_uncyc ((p, b) :: w.toWord ++ [(p, !b)]) = Uncycle ((p, b) :: w.toWord ++ [(p, !b)]) := by
  intros w a b
  rw [<- one_uncyc_lemma]
  let L := w.toWord
  rw [<- if_conj_then_cyc]
  sorry




lemma Uncycleconj_is_reduced_cperm {α : Type*} [DecidableEq α] : ∀ (g y : FreeGroup α), Uncycle (g*y*g⁻¹).toWord ∈ List.map FreeGroup.reduce (y.toWord).cyclicPermutations := by
  intros g y
  rw [form_of_conj]
  simp
  let conju := FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord)
  sorry

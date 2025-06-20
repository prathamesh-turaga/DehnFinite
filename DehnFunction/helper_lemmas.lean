-- iff : (step R x y), (xy⁻¹ or yx⁻¹ ∈ ConjSet (R))
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
import DehnFunction.Area2
import DehnFunction.Area_equiv



def step_n₂ {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (n : ℕ) (w1 w2 : FreeGroup α) : Prop :=
  match n with
  | 0 => w1 = w2
  | 1 => step relators w1 w2
  | n+1 => ∃ y, step relators w1 y ∧ step_n relators n y w2


def ReduceMyPairs₂ {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | [x] => [x]
  | (p, b) :: xs =>
    if (FreeGroup.mk [(p,b)]) * (FreeGroup.mk [xs.getLast (sorry)]) == 1 then
      ReduceMyPairs₂ (xs.dropLast)
    else
      (p, b) :: xs
termination_by L.length

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
#check List.rec


lemma Uncycleconj_in_cperm {α : Type*} [DecidableEq α] : ∀ (g y : FreeGroup α), Uncycle (g*y*g⁻¹).toWord ∈ List.map FreeGroup.reduce (y.toWord).cyclicPermutations := by
  intros g y
  have : (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]
  rw [this]
  simp
  let conju := FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord)
  sorry

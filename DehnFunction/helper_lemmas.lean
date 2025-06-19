-- iff : (step R x y), (xy⁻¹ or yx⁻¹ ∈ ConjSet (R))
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
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


def ReduceMyPairs₂ {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | (p, b) :: xs =>
    if xs == [] then
      [(p, b)]
    else
      if p == (xs.getLast (by sorry)).1 && b != (xs.getLast (by sorry)).2 then ReduceMyPairs₂ xs.dropLast
      else (p, b) :: xs
termination_by L.length


def step_n₂ {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (n : ℕ) (w1 w2 : FreeGroup α) : Prop :=
  match n with
  | 0 => w1 = w2
  | 1 => step relators w1 w2
  | n+1 => ∃ y, step relators w1 y ∧ step_n relators n y w2


def ReduceMyPairs₃ {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | [x] => [x]
  | (p, b) :: xs =>
    if (FreeGroup.mk [(p,b)]) * (FreeGroup.mk [xs.getLast sorry]) == 1 then
      ReduceMyPairs (xs.dropLast)
    else
      (p, b) :: xs
termination_by L.length

def Uncyclic {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Bool :=
  match L with
  | [] => true
  | [x] => true
  | (p, b) :: xs =>
    (L == FreeGroup.reduce L) ∧ ((FreeGroup.mk [(p,b)]) * (FreeGroup.mk [xs.getLast (by sorry)]) == 1)

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



lemma if_conj_then_cyc {α : Type*} [DecidableEq α] : ∀ (L : List (α × Bool)), ∀ p : α, ∀ b : Bool, Uncycle L = Uncycle ((p, b) :: L ++ [(p, !b)]) := by
  intros L p b
  simp
  let LL := ((p, b) :: L ++ [(p, !b)])
  have this₁ : LL ≠ [] := by exact List.concat_ne_nil (p, !b) ((p, b) :: L)
  have this₂ : ∀ x : α × Bool, LL ≠ [x] := by aesop
  have that₁ : LL.tail ≠ [] := by exact fun a ↦ this₂ (p, b) (congrArg (List.cons (p, b)) a)
  have that₂ : LL.tail.getLast (that₁) = (p, !b) := by simp [LL]
  have that₃ : LL.head (this₁)= (p, b) := by simp [LL]
  have that₄ : LL.length = L.length + 2 := by aesop
  have that₅ : LL.getLast this₁ = (p, !b) := by exact List.getLast_concat
  induction L.length with
  | zero =>
    unfold Uncycle
    aesop
    unfold Uncycle
    simp
    unfold Uncycle
    simp [List.dropLast]
    have other₁ : (((((fst_1, snd_1) :: ys).getLast (by simp)).1, snd) :: ((fst_1, snd_1) :: (ys ++ [(p, !b)])).dropLast) = ((((fst_1, snd_1) :: ys).getLast (by simp)).1, snd) :: ((fst_1, snd_1) :: ys) := by simp [List.dropLast]
    simp [List.dropLast, other₁]
    · sorry
    · simp [List.dropLast]
      unfold Uncycle
      aesop
  | succ n _ =>
    expose_names
    exact h

--  have other₁ : True := sorry
--  simp [this₁, this₂, that₁, that₂, that₃]

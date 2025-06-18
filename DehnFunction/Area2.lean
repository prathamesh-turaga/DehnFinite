import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Lattice
import DehnFunction.Area1

variable {α : Type*}
variable [DecidableEq α]
variable (trial_set : Set (FreeGroup α))

def CycPermList {α : Type*} [DecidableEq α] : (relator : FreeGroup α) → List (List (α × Bool)):= fun relator => List.cyclicPermutations (FreeGroup.toWord relator)
-- This function takes a freeword (if the underlying type for the freegroup is decidable) and gives us all its cyclic permutations as a list of lists.

def list_to_free {γ : Type*} (l : List (List (γ × Bool))) : List (FreeGroup γ) := List.map FreeGroup.mk l
#check list_to_free
-- Runs through the list of lists from CycPerm and gives us a list of FG elements.

def CycPerm {α : Type*} [DecidableEq α] (w : FreeGroup α) := list_to_free (CycPermList w)

def ReduceMyPairs {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) :=
  match L with
  | [] => []
  | [x] => [x]
  | (p, b) :: xs =>
    match xs.getLast? with
    | some (q, b') =>
      if p == q && b != b' then
        ReduceMyPairs (xs.dropLast)
      else
        (p, b) :: xs
    | none => (p, b) :: xs  -- Shouldn't happen due to first match
termination_by L.length
#check ReduceMyPairs

def CycRed {α : Type*} [DecidableEq α] (w : FreeGroup α) := FreeGroup.mk (ReduceMyPairs (FreeGroup.toWord w))
--Cyclically reduces a freeword


def CyclicPermutationsOfRelators {G : Type*}[DecidableEq G](R : Set (FreeGroup G)) : Set (FreeGroup G) :=
  ⋃ r ∈ R, {w | FreeGroup.toWord w ∈ (FreeGroup.toWord r).cyclicPermutations}
-- Given a set of relators, returns the set of all their cyclic permutations


def step {γ : Type*} [DecidableEq γ] (RelatorSet : Set (FreeGroup γ)) (w₁ w₂ : FreeGroup γ) : Prop :=
  ((CycRed (w₁ * w₂⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet) ∨ ((CycRed (w₂ * w₁⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet)

def step_n {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (n : ℕ) (w1 w2 : FreeGroup α) : Prop :=
  match n with
  | 0 => w1 = w2
  | 1 => step relators w1 w2
  | n+1 => ∃ y, step relators w1 y ∧ step_n relators n y w2


noncomputable def Area2 {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (w : FreeGroup α) : ℕ :=
  -- (step_n relators n w 1) ∧
  sInf {n | step_n relators n w 1}

inductive fg | a | b
   deriving DecidableEq, Repr

namespace fg
def p := FreeGroup.of a
def q := FreeGroup.of b

def R : Set (FreeGroup fg) := {p * q * p⁻¹ * q⁻¹}

def w : FreeGroup fg := p * q * p⁻¹ * q⁻¹

lemma l1 : step_n R 1 w 1 := by
  unfold step_n step
  sorry

lemma l2 : Area2 R w = 1 := by
  unfold Area2
  apply Nat.le_antisymm
  · exact Nat.sInf_le sorry
  · apply Nat.one_le_iff_ne_zero.mpr
    intro h
    simp at h
    rcases h with h1|h2
    · simp [step_n,w] at h1
      revert h1
      exact ne_of_beq_false rfl
    · have h3 : 1 ∈ {n | step_n R n w 1} := by sorry
      aesop


end fg

theorem step_iff_conjugate {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} (x y : FreeGroup G):
    (step R x y) ↔
  x*y⁻¹ ∈ Group.conjugatesOfSet R ∨ y*x⁻¹ ∈ Group.conjugatesOfSet R := by
    sorry

theorem wordArea_eq_zero_iff2 {G : Type*} [DecidableEq G](R : Set (FreeGroup G)) (w : FreeGroup G) :
  Area2 R w = 0 ↔ w = 1 ∨ w ∉ Subgroup.normalClosure R := by

   sorry

lemma prod_conj_implies_step_n {G : Type*} [DecidableEq G] (R : Set (FreeGroup G))

    : ∀ (l : List (FreeGroup G)), (∀ c ∈ l, c ∈ Group.conjugatesOfSet R ∨ c⁻¹ ∈ Group.conjugatesOfSet R) →
      step_n R l.length l.prod 1 := by

  intro l
  induction l with
  | nil =>

    intro h_conj
    simp [step_n]

  | cons x xs ih =>
    intros h_conj
    simp only [List.length_cons, List.prod_cons]
    unfold step_n
    match h_len_xs : xs.length with
    | 0 =>

      simp at h_len_xs
      have h_x: x ∈ Group.conjugatesOfSet R ∨ x⁻¹ ∈ Group.conjugatesOfSet R := by
        aesop
      simp[h_len_xs]
      rw[step_iff_conjugate]
      simp
      exact h_x
    | m + 1 =>
      simp
      use xs.prod
      constructor
      . rw [step_iff_conjugate]
        simp
        have h_x: x ∈ Group.conjugatesOfSet R ∨ x⁻¹ ∈ Group.conjugatesOfSet R := by
          aesop
        exact h_x
      . simp at h_len_xs
        rw[← h_len_xs]
        apply ih
        intro c h_c
        apply h_conj
        simp
        right
        exact h_c


theorem empty_step {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) (w : FreeGroup G) :
  {n | step_n R n w 1} = ∅ → w ∉ Subgroup.normalClosure R := by
  contrapose!
  intro h_mem
  rw[mem_normalClosure_iff_prod_conj] at h_mem
  rcases h_mem with ⟨ l, h_l, h_prod⟩
  use l.length
  simp
  rw[h_prod]
  apply prod_conj_implies_step_n R
  exact h_l

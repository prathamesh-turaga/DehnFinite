import Mathlib.GroupTheory.PresentedGroup

#check Group.conjugatesOfSet

/--
R - subset of FreeGroup G
w - word in FreeGroup G
n - natural number

This predicate states that the word `w` is a product of `n` conjugates of elements from the set `R`.

-/
def IsProductOfNConjugates {G: Type*}(R : Set (FreeGroup G)) (n : ℕ) (w : FreeGroup G) : Prop :=
  ∃ (l : List {c // c ∈ Group.conjugatesOfSet R}),
    l.length = n ∧ w = (l.map Subtype.val).prod

inductive MyGen | a | b
   deriving DecidableEq, Repr

namespace MyGen



def a' : FreeGroup MyGen := FreeGroup.of a
def b' : FreeGroup MyGen := FreeGroup.of b

def R : Set (FreeGroup MyGen) := {a' * b' * a'⁻¹ * b'⁻¹}

def w : FreeGroup MyGen := a' * b' * a'⁻¹ * b'⁻¹

example : IsProductOfNConjugates R 1 w := by
  have h_w_conj : w ∈ Group.conjugatesOfSet R := by
    unfold Group.conjugatesOfSet
    unfold conjugatesOf
    unfold IsConj
    unfold SemiconjBy
    simp
    use w
    constructor
    · exact Set.mem_singleton w
    . use 1
      simp
  use [{val := a' * b' * a'⁻¹ * b'⁻¹, property :=by exact h_w_conj}]
  constructor
  · rfl
  · rfl

end MyGen

noncomputable def wordArea {G: Type*}(R : Set (FreeGroup G)) (w : FreeGroup G) : ℕ :=
  sorry

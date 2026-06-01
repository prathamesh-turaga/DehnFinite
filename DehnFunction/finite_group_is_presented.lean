import Mathlib
import Mathlib.GroupTheory.FinitelyPresentedGroup

-- ...existing code...
open FreeGroup
namespace Group.IsFinitelyPresented

/--Every finite group G is finitely presented.
We state this by asserting the existence of a finite generator type `S`,
and a finite set of relations `R` such that `G` is isomorphic to `PresentedGroup R`.

 An inductive predicate defining the 5 allowed relation structures. -/
inductive IsFiniteGroupRelator (G : Type*) [Group G] : FreeGroup G → Prop
  | mul (g h : G) :
      IsFiniteGroupRelator G (of g * of h * (of (g * h))⁻¹)
  | inv_mul (g h : G) :
      IsFiniteGroupRelator G ((of g)⁻¹ * (of h)⁻¹ * (of (g⁻¹ * h⁻¹))⁻¹)
  | inv_left (g h : G) :
      IsFiniteGroupRelator G ((of g)⁻¹ * of h * (of (g⁻¹ * h))⁻¹)
  | inv_right (g h : G) :
      IsFiniteGroupRelator G (of g * (of h)⁻¹ * (of (g * h⁻¹))⁻¹)

/-- The final set, cleanly wrapping the inductive predicate. -/
def finite_group_relators (G : Type*) [Group G] : Set (FreeGroup G) :=
  {r | IsFiniteGroupRelator G r}

#check IsFinitelyPresented
#print IsFinitelyPresented

def fromFiniteGroup (G : Type*) [Group G] : G → PresentedGroup (finite_group_relators G) :=
  PresentedGroup.of


#print MulEquiv
#print PresentedGroup.toGroup
#print PresentedGroup.mk_eq_one_iff
#print QuotientGroup.eq_one_iff
#print map_one
#print PresentedGroup.mk_eq_one_iff
#print FreeGroup.one_eq_mk

def toFiniteGroup (G : Type*) [Group G] : PresentedGroup (finite_group_relators G) →* G
 :=
  PresentedGroup.toGroup (f := id) (by
  intro r hr
  rcases hr <;> simp
  )

/-Maybe useful: To add lemmas pertaining to the following sorry's below-/
lemma presentedGroup_of_one (G : Type*) [Group G] :
    (PresentedGroup.mk (finite_group_relators G)) (FreeGroup.of 1) = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  apply Subgroup.subset_normalClosure
  simp only [finite_group_relators, Set.mem_setOf_eq]
  have h_rel := IsFiniteGroupRelator.mul (1: G) 1
  rw [mul_one] at h_rel
  simp at h_rel
  exact h_rel

def finite_group_is_finitely_presented (G : Type*) [Group G] [Finite G] :
    G ≃* (PresentedGroup (finite_group_relators G)) where
    toFun := fromFiniteGroup G
    invFun := toFiniteGroup G
    left_inv x := by
        exact PresentedGroup.toGroup.of _
    right_inv x := by
        simp[toFiniteGroup, fromFiniteGroup]
        have h : ∀ r ∈ finite_group_relators G, FreeGroup.lift id r = 1 := by
            intro r hr;
            simp only [finite_group_relators, Set.mem_setOf_eq] at hr
            induction hr with |_ => simp
        induction x using Quotient.inductionOn with
        | h a =>
         induction a using FreeGroup.induction_on with
         | C1 =>
          have ds: (PresentedGroup.toGroup h  ⟦1⟧) = 1 := by
            unfold PresentedGroup.toGroup
            simp
            exact map_one _
          have ds2: (PresentedGroup.of 1 : PresentedGroup (finite_group_relators G)) = ⟦1⟧ :=   by
            simp
            unfold PresentedGroup.of
            rw[presentedGroup_of_one]
            rfl
          rw[ds, ds2]
         | of a =>
           have ds: (PresentedGroup.toGroup h  ⟦(FreeGroup.mk [(a, true)])⟧) = a := by
            unfold PresentedGroup.toGroup
            sorry
           sorry
         | inv_of a h_inv => sorry
         | mul a b ha hb =>
           sorry
    map_mul' :=  (by
    intro x y
    simp[fromFiniteGroup]
    unfold PresentedGroup.of
    unfold PresentedGroup.mk
    unfold FreeGroup.of
    unfold FreeGroup.mk
    sorry
    )

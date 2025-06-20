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
  | [_] => L

  | x :: y :: ys =>

      let xs := y :: ys

      let last := xs.getLast (by simp)
      let middle := xs.dropLast

      if x.1 = last.1 ∧ x.2 ≠ last.2 then
        ReduceMyPairs middle
      else
        L
termination_by L.length


#check ReduceMyPairs

def CycRed {α : Type*} [DecidableEq α] (w : FreeGroup α) := FreeGroup.mk (ReduceMyPairs (FreeGroup.toWord w))
--Cyclically reduces a freeword

def CyclicPermutationsOfRelators {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) : Set (FreeGroup G) :=

  ⋃ r ∈ R,
    { elem |
      ∃ word ∈ (FreeGroup.toWord r).cyclicPermutations,
      elem = FreeGroup.mk word
    }


def step {γ : Type*} [DecidableEq γ] (RelatorSet : Set (FreeGroup γ)) (w₁ w₂ : FreeGroup γ) : Prop :=
  ((CycRed (w₁ * w₂⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet) ∨ ((CycRed (w₂ * w₁⁻¹)) ∈ CyclicPermutationsOfRelators RelatorSet)

def step_n {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (n : ℕ) (w1 w2 : FreeGroup α) : Prop :=
  match n with
  | 0 => w1 = w2

  | n+1 => ∃ y, step relators w1 y ∧ step_n relators n y w2


noncomputable def Area2 {α : Type*} [DecidableEq α] (relators : Set (FreeGroup α)) (w : FreeGroup α) : ℕ :=
  -- (step_n relators n w 1) ∧
  sInf {n | step_n relators n w 1}



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
      use 1
      simp at h_len_xs
      have h_x: x ∈ Group.conjugatesOfSet R ∨ x⁻¹ ∈ Group.conjugatesOfSet R := by
        aesop
      simp[h_len_xs]
      constructor
      .
        rw[step_iff_conjugate]
        simp
        exact h_x
      .
        unfold step_n
        simp


    | m + 1 =>

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




theorem isConjugate_of_prod {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} {n: ℕ } (x y : FreeGroup G)
    (h : IsProductOfNConjugates R n y) (h_prod : x * y⁻¹ ∈ Group.conjugatesOfSet R ∨ y * x⁻¹ ∈ Group.conjugatesOfSet R) :
  IsProductOfNConjugates R (n+1) x:= by
    rcases h with ⟨ l_y, h_ly_conj, h_ly_len, h_ly_prod⟩
    cases h_prod with
    | inl h_conj =>
        use (x* y⁻¹) :: l_y
        aesop

    | inr h_conj =>
        use (y * x⁻¹)⁻¹ :: l_y
        aesop



lemma step_n_implies_IsProductOfNConjugates {G : Type*} [DecidableEq G] (R : Set (FreeGroup G))(n : ℕ):
    ∀ (w : FreeGroup G),(step_n R n w 1) →
  IsProductOfNConjugates R n w := by
  induction n with

  | zero =>
    intros w h_step
    simp [step_n] at h_step
    rw [h_step]
    use []
    simp

  | succ n ih =>
    intros w h_step
    unfold step_n at h_step
    cases n with
        | zero =>
            rcases h_step with ⟨y, h_step, h_y_1_path⟩
            simp[step_n] at h_y_1_path
            rw[h_y_1_path] at h_step
            have h_conj: w ∈ Group.conjugatesOfSet R ∨ w⁻¹ ∈ Group.conjugatesOfSet R := by
              have h_w_id : w = w* 1⁻¹ := by
                simp
              have h_id_w : w⁻¹ = 1 * w⁻¹ := by
                simp
              nth_rw 1 [h_w_id, h_id_w]
              rw [← step_iff_conjugate w 1]
              exact h_step
            use [w]
            aesop
        | succ m =>
            rcases h_step with ⟨y, h_step_wy, h_stepn_y1⟩
            have h_y_prod: IsProductOfNConjugates R (m+1) y := by
                apply ih
                exact h_stepn_y1

            have h_prod: w * y⁻¹ ∈ Group.conjugatesOfSet R ∨ y * w⁻¹ ∈ Group.conjugatesOfSet R := by
                rw[ ← step_iff_conjugate]
                exact h_step_wy
            exact isConjugate_of_prod w y h_y_prod h_prod


theorem step_empty {G : Type*} [DecidableEq G] (R : Set (FreeGroup G)) :
  ∀ w, w ∉ Subgroup.normalClosure R  → {n | step_n R n w 1} = ∅ := by

  intro w
  contrapose!

  intro h_nonempty

  rcases h_nonempty with ⟨n, h_step_n_path⟩
  simp at h_step_n_path
  have h_is_prod : IsProductOfNConjugates R n w := by
    exact step_n_implies_IsProductOfNConjugates R n w h_step_n_path

  rw [mem_normalClosure_iff_prod_conj]

  rcases h_is_prod with ⟨l, h_l_conj, h_l_len, h_l_prod⟩


  use l


theorem reduceMyPairs_property {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    ∃ (U V : List (α × Bool)), L = U ++ ReduceMyPairs L ++ V ∧ FreeGroup.mk (V ++ U) = 1 := by

  match h_L_eq : L with

  | [] =>

    use [], []
    simp
    constructor
    . unfold ReduceMyPairs
      simp
    .
     subst h_L_eq
     rfl


  | [x] =>
    use [], []
    simp
    constructor
    . unfold ReduceMyPairs
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
      have h_def : ReduceMyPairs L = ReduceMyPairs middle := by
        rw [ReduceMyPairs.eq_def]
        rw [h_L_form]
        aesop

      have ih := reduceMyPairs_property middle
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
      have h_def : ReduceMyPairs L = L := by
        rw [h_L_eq]
        simp [ReduceMyPairs, h_if]
        aesop


      use [], []
      rw[← h_L_eq]
      rw [h_def]
      aesop
  termination_by L.length


theorem cycRed_is_a_cyclic_permutation {G : Type*} [DecidableEq G] (y : FreeGroup G) :
  CycRed y ∈ CyclicPermutationsOfRelators {y} := by

  let L := FreeGroup.toWord y
  let M := ReduceMyPairs L
  unfold CyclicPermutationsOfRelators
  simp

  unfold CycRed

  have h_prop := reduceMyPairs_property L
  rcases h_prop with ⟨U, V, h_decomp, h_vu_is_one⟩


  let p := M ++ V ++ U
  use p


  constructor

  · change p ~r L
    use (M ++ V).length
    dsimp [p]
    rw[h_decomp]
    have h_M_def: ReduceMyPairs L = M := by

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

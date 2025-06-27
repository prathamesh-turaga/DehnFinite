import DehnFunction.helper_lemmas

lemma uncycled_of_Uncycle {G: Type*} [DecidableEq G] (L : List (G × Bool)) :
  uncycled (Uncycle L) := by

  unfold Uncycle
  match hL: L with
  | [] => aesop
  | [_] => aesop
  | x :: y :: ys =>
    let xs := y :: ys
    have hL_form : L = x :: xs := by simp [hL, xs]
    let last := xs.getLast (by simp [hL, xs])
    let middle := xs.dropLast

    let cond := x.1 = last.1 ∧ x.2 ≠ last.2
    have h_xs : xs = y :: ys := by
        rfl
    have h_last : last = (y :: ys).getLast (by simp [hL, xs]) := by
            have h_temp: (xs).getLast (by simp [hL, xs]) = (y :: ys).getLast (by simp [hL, xs]) := by
              rfl

            rw [h_temp]

    by_cases h_if : cond


    ·
      unfold cond at h_if
      simp

      have h_inner_eval : (if x.1 = last.1 ∧ x.2 ≠ last.2 then Uncycle middle else L) = Uncycle middle := by
        apply if_pos h_if
      rw[← h_last, ← h_xs, ← hL_form]

      rw [h_inner_eval]
      exact uncycled_of_Uncycle middle


    ·
      unfold cond at h_if
      simp

      have h_inner_eval : (if x.1 = last.1 ∧ x.2 ≠ last.2 then Uncycle middle else L) = L := by
        apply if_neg h_if
      rw[← h_last, ← h_xs, ← hL_form]
      rw [h_inner_eval]
      unfold uncycled
      rw[hL]
      simp
      simp at h_if
      exact Decidable.not_or_of_imp h_if

termination_by L.length

theorem Red_over_three {G: Type*} [DecidableEq G] (A B C: List (G × Bool)): FreeGroup.reduce (A ++ B ++ C) = FreeGroup.reduce (FreeGroup.reduce A ++ FreeGroup.reduce B ++ FreeGroup.reduce C) :=by
  rw[← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk]
  rw[FreeGroup.toWord_inj]

  rw[← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  repeat rw[FreeGroup.reduce.self]

theorem isRed_of_reduce {G: Type*} [DecidableEq G] (w : List (G × Bool)) : IsRed (FreeGroup.reduce w) := by
  rw[equiv_of_reds]
  exact FreeGroup.reduce.idem

#check uncyc_then_comm_lists₂
#check uncyclicmid
#check app_red_still_red

--basic theorem for freegroup
theorem Red_sum_invRev {G: Type*} [DecidableEq G] (A : List (G × Bool)) : FreeGroup.reduce ( FreeGroup.invRev A ++ A) = [] := by
  rw[← FreeGroup.toWord_mk]
  rw[← FreeGroup.toWord_one]
  rw[FreeGroup.toWord_inj, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  exact inv_mul_cancel (FreeGroup.mk A)

theorem Red_sum_invRev' {G: Type*} [DecidableEq G] (A : List (G × Bool)) : FreeGroup.reduce (A ++ FreeGroup.invRev A) = [] := by
  rw[← FreeGroup.toWord_mk]
  rw[← FreeGroup.toWord_one]
  rw[FreeGroup.toWord_inj, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  exact Eq.symm (eq_mul_inv_of_mul_eq rfl)


theorem uncycred_to_red {G: Type*} [DecidableEq G] (A B: List (G × Bool)) (h_cycred: cycreduced B) (h_red: IsRed A): ∃ (g: List (G × Bool) ), IsRed g ∧ Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) = FreeGroup.reduce (g ++ B ++ FreeGroup.invRev g) := by
  by_cases h_empty_B: B = []
  . use A
    rw[h_empty_B]
    simp
    rw[Red_sum_invRev']
    constructor
    . exact h_red
    . unfold Uncycle
      rfl
  . have h_or := uncyclicmid B A h_cycred
    by_cases h_red3: IsRed (A ++ B ++ FreeGroup.invRev A)
    . rw[equiv_of_reds] at h_red3
      rw[h_red3, uncycle_conj]
      use []
      simp
      constructor
      . exact IsRed.nil
      . unfold cycreduced at h_cycred
        have h_unc: Uncycle (B) = B :=by
          exact h_cycred.2
        have h_red_B: FreeGroup.reduce (B) = B := by
          rw[← equiv_of_reds]
          exact h_cycred.1
        rw[h_unc, h_red_B]
    by_cases h_red2: IsRed (A++B)
    sorry

theorem cycred_conj_to_cyc {G: Type*} [DecidableEq G] (A B: List (G × Bool)) (h_cycred: cycreduced B) (h_red: IsRed A): Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B := by
  have lem := uncycred_to_red A B h_cycred h_red
  rcases lem with ⟨g, h_red_g, h_uncyc⟩
  rw[h_uncyc]
  let r := FreeGroup.reduce (g ++ B ++ FreeGroup.invRev g)
  have h_r_cycred: cycreduced r := by
    unfold cycreduced
    constructor
    . rw[equiv_of_reds]
      unfold r
      exact FreeGroup.reduce.idem

    . rw[← uncycled_iff]
      unfold r
      rw[← h_uncyc]
      exact uncycled_of_Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A))
  exact
    prathamesh_lemma (FreeGroup.reduce (g ++ B ++ FreeGroup.invRev g)) B g h_r_cycred h_cycred
      h_red_g rfl




theorem cyc_if_conj_list {G: Type*} [DecidableEq G] (r : FreeGroup G): ∀ (g : FreeGroup G),
  ∃ (L: List (G × Bool)), L ~r (FreeGroup.toWord r)∧  Uncycle ((g*r*(g⁻¹)).toWord) = FreeGroup.reduce (L) := by
  intro g
  have h_towrd_reduce: (g*r*(g⁻¹)).toWord = FreeGroup.reduce (g.toWord ++ r.toWord ++ FreeGroup.invRev g.toWord) := by
    rw[← FreeGroup.toWord_mk]
    rw[FreeGroup.toWord_inj]
    rw[← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw[FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    rw[← FreeGroup.inv_mk]
    rw[FreeGroup.mk_toWord]

  rw[ h_towrd_reduce]
  have h_r_uncyc := Uncycle_property r.toWord
  rcases h_r_uncyc with ⟨U, V, h_r_conj, h_inv⟩
  have h_uv_inv: FreeGroup.reduce (V ++ U) = [] := by
    rw[← FreeGroup.toWord_mk, h_inv]
    exact rfl

  rw[h_r_conj]
  have h_assoc_simp: g.toWord ++ (U ++ Uncycle r.toWord ++ V) ++ FreeGroup.invRev g.toWord = (g.toWord ++ U) ++ Uncycle r.toWord ++ (V ++ FreeGroup.invRev g.toWord) := by
    simp

  have h_red_uncyc_r: FreeGroup.reduce (Uncycle r.toWord) = Uncycle r.toWord := by
    rw[← equiv_of_reds]
    apply uncyc_of_red_is_red
    rw[equiv_of_reds]
    exact FreeGroup.reduce_toWord r

  have h_red_dist: FreeGroup.reduce (g.toWord ++ (U ++ Uncycle r.toWord ++ V) ++ FreeGroup.invRev g.toWord) = FreeGroup.reduce (FreeGroup.reduce (g.toWord ++ U) ++ Uncycle r.toWord ++ FreeGroup.reduce (V ++ FreeGroup.invRev g.toWord)) := by
    rw[h_assoc_simp]
    rw[Red_over_three]
    rw[h_red_uncyc_r]

  rw[h_red_dist]
  let x := FreeGroup.reduce (g.toWord ++ U)
  have h_x: x = FreeGroup.reduce (g.toWord ++ U) := by
    rfl
  have h_inv2 : FreeGroup.mk (V) = FreeGroup.mk (FreeGroup.invRev U) := by
    rw[← FreeGroup.inv_mk]
    exact eq_inv_of_mul_eq_one_left h_inv


  have h_x_inv : FreeGroup.invRev x = FreeGroup.reduce (V ++ FreeGroup.invRev g.toWord) := by
    rw[ h_x, ← FreeGroup.reduce_invRev, ← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk, ← FreeGroup.mul_mk]
    rw[FreeGroup.invRev_append, ← FreeGroup.mul_mk, FreeGroup.toWord_inj]
    rw[h_inv2]

  rw[← h_x, ← h_x_inv]
  have h_cycred: cycreduced (Uncycle r.toWord) := by
    unfold cycreduced
    constructor
    . exact (IsRed.iff_reduce_self (Uncycle r.toWord)).mpr h_red_uncyc_r

    . rw[← uncycled_iff]
      exact uncycled_of_Uncycle r.toWord



  have h_red: IsRed x := by

    dsimp[x]
    exact isRed_of_reduce (g.toWord ++ U)


  have h_main := cycred_conj_to_cyc x (Uncycle r.toWord) h_cycred h_red
  rw[List.isRotated_iff_mod] at h_main
  rcases h_main with ⟨n, h_length, h_main⟩
  let S := Uncycle (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x))
  have h_S: S = Uncycle (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)) := by
    rfl
  rw[← h_S] at h_main
  rw[← h_S] at h_length
  rw[← h_S]
  rw[List.rotate_eq_drop_append_take h_length] at h_main
  have h_r: r.toWord = U ++ (List.drop n S ++ List.take n S) ++ V := by
    rw[ h_main]
    exact h_r_conj

  use (List.take n S) ++ V ++ U ++ List.drop n S
  have h_S_red: FreeGroup.reduce S = S := by
    rw[← equiv_of_reds]
    unfold S
    have h_isRed: IsRed (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x))
      := by
      exact isRed_of_reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)
    exact
      uncyc_of_red_is_red (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)) h_isRed
  have h_isred_s: IsRed S := by
    rw[equiv_of_reds]
    exact h_S_red

  have h_red_both : IsRed (List.take n S) ∧ IsRed (List.drop n S) := by
    apply isredsubl
    simp
    exact h_isred_s


  have h_Stake_red: FreeGroup.reduce (List.take n S) = List.take n S := by
    rw[← equiv_of_reds]

    exact h_red_both.1
  have h_Sdrop_red: FreeGroup.reduce (List.drop n S) = List.drop n S := by
    rw[← equiv_of_reds]

    exact h_red_both.2
  constructor
  . rw[← h_main]
    have h_assoc1: List.take n S ++ V ++ U ++ List.drop n S = (List.take n S ++ V) ++ (U ++ List.drop n S) := by
      simp
    have h_assoc2: U ++ (List.drop n S ++ List.take n S) ++ V = (U ++ List.drop n S) ++ (List.take n S ++ V) := by
      simp
    rw[h_assoc1, h_assoc2]
    exact List.isRotated_append

  . rw[← FreeGroup.reduce_append_reduce_reduce]
    rw [List.append_assoc]
    have h_temp: FreeGroup.reduce (List.take n S ++ (V ++ U)) = List.take n S :=
      by
      rw[← FreeGroup.reduce_append_reduce_reduce]
      rw[h_Stake_red]
      rw[h_uv_inv]
      simp
      apply h_Stake_red

    rw[h_temp]
    rw[h_Sdrop_red]
    simp
    rw[h_S_red]



theorem conj_iff_cyc {G: Type*} [DecidableEq G] (w r : FreeGroup G): (∃ (g: FreeGroup G), w = g * r * g⁻¹) ↔
  ∃ (word: List (G × Bool)), word ~r (FreeGroup.toWord r)∧  (CycRed w) = FreeGroup.mk word := by
  constructor
  . intro h_w_conj_r
    rcases h_w_conj_r with ⟨g, h_g⟩
    rw [h_g]
    unfold CycRed
    have h_L := cyc_if_conj_list r g
    rcases h_L with ⟨L, h_Lr, h_Le⟩
    use L
    constructor
    . exact h_Lr
    . rw [h_Le]
      exact FreeGroup.reduce.self

  . exact conj_if_cyc w r



theorem step_iff_conjugate {G : Type*} [DecidableEq G] {R : Set (FreeGroup G)} (x y : FreeGroup G):
    (step R x y) ↔
  x*y⁻¹ ∈ Group.conjugatesOfSet R ∨ y*x⁻¹ ∈ Group.conjugatesOfSet R := by
    unfold step
    apply or_congr
    . unfold CyclicPermutationsOfRelators
      unfold Group.conjugatesOfSet
      rw[ Set.mem_iUnion₂]
      rw[ Set.mem_iUnion₂]
      apply exists_congr
      intro r
      simp
      intro h_r
      apply Iff.symm
      unfold conjugatesOf
      simp
      have h_symm: (∃ c,c * r * c⁻¹ = x * y⁻¹) ↔ (∃ c,x * y⁻¹ =c * r * c⁻¹)  :=by
        apply Iff.intro
        · intro a
          obtain ⟨w, h⟩ := a
          use w
          apply Eq.symm
          exact h
        · intro a
          obtain ⟨w, h⟩ := a
          simp_all only [exists_apply_eq_apply]

      rw[h_symm]
      apply conj_iff_cyc (x*y⁻¹) r
    . unfold CyclicPermutationsOfRelators
      unfold Group.conjugatesOfSet
      rw[ Set.mem_iUnion₂]
      rw[ Set.mem_iUnion₂]
      apply exists_congr
      intro r
      simp
      intro h_r
      apply Iff.symm
      unfold conjugatesOf
      simp
      have h_symm: (∃ c,c * r * c⁻¹ = y * x⁻¹) ↔ (∃ c,y * x⁻¹ =c * r * c⁻¹)  :=by
        apply Iff.intro
        · intro a
          obtain ⟨w, h⟩ := a
          use w
          apply Eq.symm
          exact h
        · intro a
          obtain ⟨w, h⟩ := a
          simp_all only [exists_apply_eq_apply]
      rw[h_symm]
      apply conj_iff_cyc (y*x⁻¹) r

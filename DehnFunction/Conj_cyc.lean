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
#check technique

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

#check isredsubl


theorem cycred_conj_to_cyc' {G: Type*} [DecidableEq G] (B: List (G × Bool)) (h_cycred: cycreduced B) : ∀ (A : List (G × Bool)), (IsRed A) → Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B := by
  intro A
  induction hA: A.length using Nat.strong_induction_on  generalizing A with
  | h n ih =>
  intro h_red
  by_cases h_empty_B: B = []
  . rw[h_empty_B]
    simp
    rw[Red_sum_invRev']
    unfold Uncycle
    rfl
  by_cases h_empty_A: A = []
  . rw[h_empty_A]
    simp
    unfold cycreduced at h_cycred
    have h_redB: FreeGroup.reduce (B) = B := by
      rw[← equiv_of_reds]
      exact h_cycred.1
    rw[h_redB, h_cycred.2]

  by_cases h_red3: IsRed (A ++ B ++ FreeGroup.invRev A)
  . rw[equiv_of_reds] at h_red3
    rw[h_red3, uncycle_conj]
    unfold cycreduced at h_cycred
    rw[h_cycred.2]
  unfold cycreduced at h_cycred
  have h_red_A_inv : IsRed (FreeGroup.invRev A) := by
    sorry
  by_cases h_red_AB: IsRed (A ++ B)
  . have h_not_red2: ¬ IsRed (B ++ FreeGroup.invRev A) := by
      by_contra h_temp
      have h_contra := app_red_still_red A B (FreeGroup.invRev A) h_red h_cycred.1 h_red_A_inv h_red_AB h_temp h_empty_B
      contradiction
    have h_app_tech := technique B (FreeGroup.invRev A) h_cycred.1 h_red_A_inv  h_not_red2
    rcases h_app_tech with ⟨I, J, K, h_red_I, h_red_J, h_J_ne, h_red_K, h_red_IK, h_eq_IJ, h_eq_invRevJ_K⟩
    rw[h_eq_IJ, h_eq_invRevJ_K]
    have h_A: A = ((FreeGroup.invRev K) ++ J) := by
      have h_inv_inv : FreeGroup.invRev (FreeGroup.invRev A) = A := FreeGroup.invRev_invRev
      rw[← h_inv_inv, h_eq_invRevJ_K, FreeGroup.invRev_append, FreeGroup.invRev_invRev]

    have h_cancel: FreeGroup.reduce (A ++ (I ++ J) ++ (FreeGroup.invRev J ++ K)) = FreeGroup.reduce (FreeGroup.reduce (A ++ I) ++ K) := by
      calc
        FreeGroup.reduce (A ++ (I ++ J) ++ (FreeGroup.invRev J ++ K)) = FreeGroup.reduce ((A ++ I) ++ (J ++ FreeGroup.invRev J) ++ K) := by
            simp
        _ = FreeGroup.reduce ( FreeGroup.reduce (A ++ I) ++ FreeGroup.reduce (J ++ FreeGroup.invRev J) ++ FreeGroup.reduce K) := by
          rw[Red_over_three]
        _ = FreeGroup.reduce (FreeGroup.reduce (A ++ I) ++ FreeGroup.reduce (K)) := by
          rw[Red_sum_invRev']
          simp
      have h_kred: FreeGroup.reduce K = K := by
        rw[← equiv_of_reds]
        exact h_red_K
      rw[h_kred]
    rw[h_cancel]
    have h_Kinv_red: IsRed (FreeGroup.invRev K) := by
      sorry
    have h_kinvinv: FreeGroup.invRev (FreeGroup.invRev K) = K := FreeGroup.invRev_invRev
    by_cases h_empty_I: I = []
    . rw[h_empty_I]
      simp
      rw[equiv_of_reds] at h_red
      rw[h_red]

      rw[h_A]
      rw[h_empty_I] at h_eq_IJ
      simp at h_eq_IJ
      rw[← h_eq_IJ]
      have h_Klen: (FreeGroup.invRev (K)).length < A.length := by
        have h_lensum: (FreeGroup.invRev K).length + J.length = A.length := by
          rw[h_A]
          exact Eq.symm List.length_append
        have h_lenJ : J.length >0 := by
          exact List.length_pos_iff.mpr h_J_ne
        have h_len_subt: A.length - (FreeGroup.invRev K).length > 0 := by
          rw[← h_lensum]
          simp
          exact h_lenJ
        exact Nat.lt_of_sub_pos h_len_subt

      let m := (FreeGroup.invRev K).length
      have h_m: m = (FreeGroup.invRev K).length := by
        rfl
      rw[hA, ← h_m] at h_Klen
      symm at h_m

      nth_rewrite 2 [← h_kinvinv]
      exact ih m h_Klen (FreeGroup.invRev K) h_m h_Kinv_red

    have h_red_AI : IsRed (A ++ I) := by
      rw[h_eq_IJ, ← List.append_assoc] at h_red_AB
      apply isredsubl at h_red_AB
      exact h_red_AB.1
    rw[equiv_of_reds] at h_red_AI
    rw[h_red_AI]
    rw[← equiv_of_reds] at h_red_AI
    have h_red_aik: IsRed (A ++ I ++ K) := app_red_still_red A I K h_red h_red_I h_red_K h_red_AI h_red_IK h_empty_I
    rw[equiv_of_reds] at h_red_aik
    rw[h_red_aik]
    rw[h_A]
    have h_rw: FreeGroup.invRev K ++ J ++ I ++ K = FreeGroup.invRev K ++ (J ++ I) ++ K := by
      simp
    rw[h_rw]
    nth_rewrite 2 [← h_kinvinv]
    rw[uncycle_conj]
    have h_uncyc_ji: cycreduced (J++I):=by
      sorry
    unfold cycreduced at h_uncyc_ji
    rw[h_uncyc_ji.2]
    exact List.isRotated_append



  sorry


theorem cycred_conj_to_cyc {G: Type*} [DecidableEq G] (A B: List (G × Bool)) (h_cycred: cycreduced B) (h_red: IsRed A): Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B := by
  exact cycred_conj_to_cyc' B h_cycred A h_red




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

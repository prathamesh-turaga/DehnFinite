import DehnFunction.helper_lemmas

namespace FreeGroup

lemma Uncycle.isUncycled {G: Type*} [DecidableEq G] (L : List (G × Bool)) :
  IsUncycled (Uncycle L) := by
  unfold Uncycle
  match hL: L with
  | [] => simp [IsUncycled]
  | [_] => simp [IsUncycled]
  | x :: y :: ys =>
    let xs := y :: ys
    have hL_form : L = x :: xs := by simp [hL, xs]
    let last := xs.getLast (by simp [hL, xs])
    let middle := xs.dropLast

    let cond := x.1 = last.1 ∧ x.2 ≠ last.2
    have h_xs : xs = y :: ys := by
        rfl
    have h_last : last = (y :: ys).getLast (by simp [hL, xs]) := by
            have h_temp: (xs).getLast (by simp [hL, xs]) = (y :: ys).getLast (by simp [hL, xs]) := rfl
            rw [h_temp]
    by_cases h_if : cond
    · unfold cond at h_if
      simp
      have h_inner_eval : (if x.1 = last.1 ∧ x.2 ≠ last.2 then Uncycle middle else L) = Uncycle middle := if_pos h_if
      rw[← h_last, ← h_xs, ← hL_form]
      rw [h_inner_eval]
      exact Uncycle.isUncycled middle
    · unfold cond at h_if
      simp
      have h_inner_eval : (if x.1 = last.1 ∧ x.2 ≠ last.2 then Uncycle middle else L) = L := if_neg h_if
      rw[← h_last, ← h_xs, ← hL_form,h_inner_eval]
      unfold IsUncycled
      rw [hL]
      simp
      simp at h_if
      exact Decidable.not_or_of_imp h_if
termination_by L.length

theorem reduce_over_append_three {G: Type*} [DecidableEq G] (A B C: List (G × Bool)): FreeGroup.reduce (A ++ B ++ C) = FreeGroup.reduce (FreeGroup.reduce A ++ FreeGroup.reduce B ++ FreeGroup.reduce C) :=by
  rw[← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk]
  rw[FreeGroup.toWord_inj]

  rw[← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  repeat rw[FreeGroup.reduce.self]

theorem IsRed.of_reduce {G: Type*} [DecidableEq G] (w : List (G × Bool)) : IsRed (FreeGroup.reduce w) := by
  rw[equiv_of_reds]
  exact FreeGroup.reduce.idem

theorem reduce_inv' {G: Type*} [DecidableEq G] (A : List (G × Bool)) : FreeGroup.reduce ( FreeGroup.invRev A ++ A) = [] := by
  rw[← FreeGroup.toWord_mk]
  rw[← FreeGroup.toWord_one]
  rw[FreeGroup.toWord_inj, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  exact inv_mul_cancel (FreeGroup.mk A)

theorem cycred_conj_to_cyc' {G: Type*} [DecidableEq G] (B: List (G × Bool)) (h_cycred: IsCycReduced B) : ∀ (A : List (G × Bool)), (IsRed A) → Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B := by
  intro A
  induction hA: A.length using Nat.strong_induction_on  generalizing A with
  | h n ih =>
  intro h_red
  by_cases h_empty_B: B = []
  . rw[h_empty_B]
    simp
    rw[reduce_inv]
    unfold Uncycle
    rfl
  by_cases h_empty_A: A = []
  . rw[h_empty_A]
    simp
    unfold IsCycReduced at h_cycred
    have h_redB: FreeGroup.reduce (B) = B := by
      rw[← IsRed.equiv_of_reds]
      exact h_cycred.1
    rw[h_redB, h_cycred.2]

  by_cases h_red3: IsRed (A ++ B ++ FreeGroup.invRev A)
  . rw[IsRed.equiv_of_reds] at h_red3
    rw[h_red3, Uncycle.conj]
    unfold IsCycReduced at h_cycred
    rw[h_cycred.2]
  unfold IsCycReduced at h_cycred
  have h_red_A_inv : IsRed (FreeGroup.invRev A) := IsRed.invRev_IsRed A h_red
  by_cases h_red_AB: IsRed (A ++ B)
  . have h_not_red2: ¬ IsRed (B ++ FreeGroup.invRev A) := by
      by_contra h_temp
      have h_contra := IsRed.app_red_still_red A B (FreeGroup.invRev A) h_red h_cycred.1 h_red_A_inv h_red_AB h_temp h_empty_B
      contradiction
    have h_app_tech := IsRed.append_largest_cancel_nonempty B (FreeGroup.invRev A) h_cycred.1 h_red_A_inv  h_not_red2
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
          rw[reduce_over_append_three]
        _ = FreeGroup.reduce (FreeGroup.reduce (A ++ I) ++ FreeGroup.reduce (K)) := by
          rw[reduce_inv]
          simp
      have h_kred: FreeGroup.reduce K = K := by
        rw[← IsRed.equiv_of_reds]
        exact h_red_K
      rw[h_kred]
    rw[h_cancel]
    have h_Kinv_red: IsRed (FreeGroup.invRev K) := IsRed.invRev_IsRed K h_red_K
    have h_kinvinv: FreeGroup.invRev (FreeGroup.invRev K) = K := FreeGroup.invRev_invRev
    by_cases h_empty_I: I = []
    . rw[h_empty_I]
      simp
      rw[IsRed.equiv_of_reds] at h_red
      rw[h_red,h_A]
      rw[h_empty_I] at h_eq_IJ
      simp at h_eq_IJ
      rw[← h_eq_IJ]
      have h_Klen: (FreeGroup.invRev (K)).length < A.length := by
        have h_lensum: (FreeGroup.invRev K).length + J.length = A.length := by
          rw[h_A]
          exact Eq.symm List.length_append
        have h_lenJ : J.length >0 := List.length_pos_iff.mpr h_J_ne
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
      exact IsRed.prefix_IsRed (A ++ I) J h_red_AB
    rw[IsRed.equiv_of_reds] at h_red_AI
    rw[h_red_AI]
    rw[← IsRed.equiv_of_reds] at h_red_AI
    have h_red_aik: IsRed (A ++ I ++ K) := IsRed.app_red_still_red A I K h_red h_red_I h_red_K h_red_AI h_red_IK h_empty_I
    rw[IsRed.equiv_of_reds] at h_red_aik
    rw[h_red_aik]
    rw[h_A]
    have h_rw: FreeGroup.invRev K ++ J ++ I ++ K = FreeGroup.invRev K ++ (J ++ I) ++ K := by simp
    rw[h_rw]
    nth_rewrite 2 [← h_kinvinv]
    rw[Uncycle.conj]
    have h_uncyc_ji: IsCycReduced (J++I):=by
      rw[← IsCycReduced] at h_cycred
      rw[h_eq_IJ] at h_cycred
      exact isCycReduced_cycPerm_IsCycReduced I J h_cycred
    unfold IsCycReduced at h_uncyc_ji
    rw[h_uncyc_ji.2]
    exact List.isRotated_append
  have h_red_BAinv: IsRed (B ++ FreeGroup.invRev A) := by
    rw[← IsCycReduced] at h_cycred
    have h_temp := IsRed.append_or_inv_append B A h_cycred h_red
    simp_all only [false_or]
  have h_app_tech := IsRed.append_largest_cancel_nonempty A B h_red h_cycred.1 h_red_AB
  rcases h_app_tech with ⟨I, J, K, h_red_I, h_red_J, h_J_ne, h_red_K, h_red_IK, h_eq_IJ, h_eq_invRevJ_K⟩
  rw[ h_eq_invRevJ_K]
  nth_rewrite 1 [h_eq_IJ]
  have h_Ainv: FreeGroup.invRev A = (FreeGroup.invRev J) ++ (FreeGroup.invRev I) := by rw[h_eq_IJ, FreeGroup.invRev_append]
  have h_red_kainv: IsRed (K ++ FreeGroup.invRev A) := by
    rw[h_eq_invRevJ_K, List.append_assoc] at h_red_BAinv
    exact IsRed.suffix_IsRed (FreeGroup.invRev J) (K ++ FreeGroup.invRev A) h_red_BAinv
  rw[IsRed.equiv_of_reds] at h_red_kainv h_red_I
  have h_cancel: FreeGroup.reduce (I ++ J ++ (FreeGroup.invRev J ++ K) ++ FreeGroup.invRev A) = FreeGroup.reduce (I  ++ K ++ FreeGroup.invRev A) := by
    calc
    FreeGroup.reduce (I ++ J ++ (FreeGroup.invRev J ++ K) ++ FreeGroup.invRev A) = FreeGroup.reduce (I ++ (J ++ FreeGroup.invRev J) ++ (K ++ FreeGroup.invRev A)) := by
      simp
    _ = FreeGroup.reduce (FreeGroup.reduce I ++ FreeGroup.reduce (J ++ FreeGroup.invRev J) ++ FreeGroup.reduce (K ++ FreeGroup.invRev A)) := by
      rw[reduce_over_append_three]

    _ = FreeGroup.reduce (FreeGroup.reduce I ++ FreeGroup.reduce (K ++ FreeGroup.invRev A)) := by
      rw[reduce_inv]
      simp
    _ = FreeGroup.reduce (FreeGroup.reduce I ++ (K ++ FreeGroup.invRev A)) := by rw[h_red_kainv]

    _ = FreeGroup.reduce (FreeGroup.reduce I ++ K ++ FreeGroup.invRev A) := by
      simp
    _ = FreeGroup.reduce (I ++ K ++ FreeGroup.invRev A) := by
      rw[h_red_I]

  rw[h_cancel]
  by_cases h_empty_K: K = []
  . rw[h_empty_K]
    simp
    rw[h_Ainv, ← List.append_assoc]
    have h_lensum: A.length = I.length + J.length   := by
      rw[h_eq_IJ]
      exact List.length_append
    have h_Ilen: (I).length < A.length := by
      have h_lenJ : J.length >0 := List.length_pos_iff.mpr h_J_ne
      have h_len_subt: A.length - ( I).length > 0 := by
        rw[h_lensum]
        simp
        exact h_lenJ
      exact Nat.lt_of_sub_pos h_len_subt
    let m := (I).length
    have h_m: m = (I).length := by
      rfl
    rw[h_empty_K] at h_eq_invRevJ_K
    simp at h_eq_invRevJ_K
    rw[← h_eq_invRevJ_K]
    rw[← h_m, hA] at h_Ilen
    rw[← IsRed.equiv_of_reds] at h_red_I
    exact ih m h_Ilen I h_m h_red_I
  rw[← IsRed.equiv_of_reds] at h_red_kainv h_red_I
  have h_total_red: IsRed (I ++ K ++ FreeGroup.invRev A) := IsRed.app_red_still_red I K (FreeGroup.invRev A) h_red_I h_red_K h_red_A_inv h_red_IK h_red_kainv h_empty_K
  rw[IsRed.equiv_of_reds] at h_total_red
  rw[h_total_red, h_Ainv]
  have h_assoc: I ++ K ++ (FreeGroup.invRev J ++ FreeGroup.invRev I) = I ++ (K ++ FreeGroup.invRev J) ++ FreeGroup.invRev I :=by simp
  rw[h_assoc]
  rw[Uncycle.conj]
  rw[← IsCycReduced, h_eq_invRevJ_K] at h_cycred
  have h_new_cycred : IsCycReduced (K ++ FreeGroup.invRev J) := isCycReduced_cycPerm_IsCycReduced (invRev J) K h_cycred
  unfold IsCycReduced at h_new_cycred
  rw[h_new_cycred.2]
  exact List.isRotated_append

theorem cycred_conj_to_cyc {G: Type*} [DecidableEq G] (A B: List (G × Bool)) (h_cycred: IsCycReduced B) (h_red: IsRed A): Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B :=
  cycred_conj_to_cyc' B h_cycred A h_red

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
  have h_r_uncyc := Uncycle.property r.toWord
  rcases h_r_uncyc with ⟨U, V, h_r_conj, h_inv⟩
  have h_uv_inv: FreeGroup.reduce (V ++ U) = [] := by
    rw[← FreeGroup.toWord_mk, h_inv]
    rfl
  rw[h_r_conj]
  have h_assoc_simp: g.toWord ++ (U ++ Uncycle r.toWord ++ V) ++ FreeGroup.invRev g.toWord = (g.toWord ++ U) ++ Uncycle r.toWord ++ (V ++ FreeGroup.invRev g.toWord) := by
    simp
  have h_red_uncyc_r: FreeGroup.reduce (Uncycle r.toWord) = Uncycle r.toWord := by
    rw[← IsRed.equiv_of_reds]
    apply Uncycle.isRed_IsRed
    rw[IsRed.equiv_of_reds]
    exact FreeGroup.reduce_toWord r
  have h_red_dist: FreeGroup.reduce (g.toWord ++ (U ++ Uncycle r.toWord ++ V) ++ FreeGroup.invRev g.toWord) = FreeGroup.reduce (FreeGroup.reduce (g.toWord ++ U) ++ Uncycle r.toWord ++ FreeGroup.reduce (V ++ FreeGroup.invRev g.toWord)) := by
    rw[h_assoc_simp]
    rw[reduce_over_append_three]
    rw[h_red_uncyc_r]
  rw[h_red_dist]
  let x := FreeGroup.reduce (g.toWord ++ U)
  have h_x: x = FreeGroup.reduce (g.toWord ++ U) := rfl
  have h_inv2 : FreeGroup.mk (V) = FreeGroup.mk (FreeGroup.invRev U) := by
    rw[← FreeGroup.inv_mk]
    exact eq_inv_of_mul_eq_one_left h_inv
  have h_x_inv : FreeGroup.invRev x = FreeGroup.reduce (V ++ FreeGroup.invRev g.toWord) := by
    rw[ h_x, ← FreeGroup.reduce_invRev, ← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk, ← FreeGroup.mul_mk]
    rw[FreeGroup.invRev_append, ← FreeGroup.mul_mk, FreeGroup.toWord_inj]
    rw[h_inv2]
  rw[← h_x, ← h_x_inv]
  have h_cycred: IsCycReduced (Uncycle r.toWord) := by
    unfold IsCycReduced
    constructor
    . exact (IsRed.equiv_of_reds (Uncycle r.toWord)).mpr h_red_uncyc_r
    . rw [← isUncycled_iff]
      exact Uncycle.isUncycled r.toWord
  have h_red: IsRed x := by
    dsimp[x]
    exact IsRed.of_reduce (g.toWord ++ U)
  have h_main := cycred_conj_to_cyc x (Uncycle r.toWord) h_cycred h_red
  rw[List.isRotated_iff_mod] at h_main
  rcases h_main with ⟨n, h_length, h_main⟩
  let S := Uncycle (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x))
  have h_S: S = Uncycle (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)) := by
    rfl
  rw[← h_S] at h_main h_length ⊢
  rw[List.rotate_eq_drop_append_take h_length] at h_main
  have h_r: r.toWord = U ++ (List.drop n S ++ List.take n S) ++ V := by
    rw[ h_main]
    exact h_r_conj
  use (List.take n S) ++ V ++ U ++ List.drop n S
  have h_S_red: FreeGroup.reduce S = S := by
    rw[← IsRed.equiv_of_reds]
    unfold S
    have h_isRed: IsRed (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x))
      := IsRed.of_reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)
    exact Uncycle.isRed_IsRed (FreeGroup.reduce (x ++ Uncycle r.toWord ++ FreeGroup.invRev x)) h_isRed
  have h_isred_s: IsRed S := by
    rw[IsRed.equiv_of_reds]
    exact h_S_red
  have h_red_both : IsRed (List.take n S) ∧ IsRed (List.drop n S) := by
    constructor
    · apply IsRed.prefix_IsRed (List.take n S) (List.drop n S)
      simp [h_isred_s]
    · apply IsRed.suffix_IsRed (List.take n S) (List.drop n S)
      simp [h_isred_s]
  have h_Stake_red: FreeGroup.reduce (List.take n S) = List.take n S := by
    rw[← IsRed.equiv_of_reds]
    exact h_red_both.1
  have h_Sdrop_red: FreeGroup.reduce (List.drop n S) = List.drop n S := by
    rw[← IsRed.equiv_of_reds]
    exact h_red_both.2
  constructor
  . rw[← h_main]
    have h_assoc1: List.take n S ++ V ++ U ++ List.drop n S = (List.take n S ++ V) ++ (U ++ List.drop n S) := by simp
    have h_assoc2: U ++ (List.drop n S ++ List.take n S) ++ V = (U ++ List.drop n S) ++ (List.take n S ++ V) := by simp
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
  ∃ (wrd: List (G × Bool)), wrd ~r (FreeGroup.toWord r)∧  (CycRed w) = FreeGroup.mk wrd := by
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

lemma CycReduce_is_cycreduced {G: Type*} [DecidableEq G] (l : List (G × Bool)) : IsCycReduced (CycReduce l) := by
  rw [CycReduce]
  have h := IsRed.of_reduce l
  generalize FreeGroup.reduce l = L at *
  rw [Uncycle_eq_Uncycle']
  induction L using Uncycle'.induct with
  | case1 => simp [Uncycle',Uncycle,IsCycReduced,IsRed.nil]
  | case2 a => simp [Uncycle',Uncycle,IsCycReduced,IsRed.singleton]
  | case3 a as has ha ih =>
    have h1 := IsRed.tail _ h
    simp [Uncycle',has,ha]
    have h2 := List.concat_if_not_empty as has
    rw [h2] at h
    exact ih (IsRed.prefix_IsRed _ _ (IsRed.tail _ h))
  | case4 a as has ha =>
    simp [Uncycle',has,ha]
    constructor
    · exact h
    · rw [← isUncycled_iff]
      match as with
      | [] => simp[IsUncycled]
      | b::bs => simp [IsUncycled,ha]

lemma CycReduce_idem {G: Type*} [DecidableEq G] (l : List (G × Bool)) : CycReduce (CycReduce l) = CycReduce l := by
  have ⟨h1,h2⟩ := CycReduce_is_cycreduced l
  rw [CycReduce]
  rw [IsRed.equiv_of_reds] at h1
  rw [h1]
  exact h2

lemma IsRed.append_rotation_uncycled {G: Type*} [DecidableEq G] (l1 l2 : List (G × Bool)) (hl1e : l1 ≠ []) (hl2e : l2 ≠ []) (hl : IsRed (l1++l2)) : IsUncycled (l2++l1) := by
  match l2 with
  | [] => contradiction
  | a::as =>
    rw [isUncycled_iff,Uncycle_eq_Uncycle']
    rw [IsRed.append_nonempty_iff _ _ (IsRed.prefix_IsRed l1 (a :: as) hl) (IsRed.suffix_IsRed l1 (a :: as) hl) (hl1e) (by simp)] at hl
    simp at hl
    simp [Uncycle',hl1e]
    tauto

theorem conj_iff_cyc' {G: Type*} [DecidableEq G] (L₁ L₂ : List (G × Bool)): IsConj (FreeGroup.mk L₁) (FreeGroup.mk L₂) ↔ CycReduce L₁ ~r CycReduce L₂:= by
  constructor
  · intro h
    rw [IsConj] at h
    rcases h with ⟨g,hg⟩
    rw [SemiconjBy] at hg
    have h1 : FreeGroup.mk L₂ = (g.1) * FreeGroup.mk L₁ * (↑g)⁻¹ := eq_mul_inv_of_mul_eq (Eq.symm hg)
    rcases (conj_iff_cyc (FreeGroup.mk L₂) (FreeGroup.mk L₁)).mp ⟨g.1,h1⟩ with ⟨w,hw1,hw2⟩
    rw [FreeGroup.toWord_mk] at hw1
    rw [CycRed,FreeGroup.toWord_mk,← CycReduce] at hw2
    apply FreeGroup.toWord_inj.mpr at hw2
    rw [FreeGroup.toWord_mk,FreeGroup.toWord_mk] at hw2
    have h2 := congrArg Uncycle hw2
    rw [← CycReduce,← CycReduce,CycReduce_idem] at h2
    rw [h2]
    symm at hw1
    rw [List.isRotated_iff_mod] at hw1
    rcases hw1 with ⟨n,hn1,hn2⟩
    set l1 := (List.splitAt n (FreeGroup.reduce L₁)).1 with hl1
    set l2 := (List.splitAt n (FreeGroup.reduce L₁)).2 with hl2
    have h2 : (FreeGroup.reduce L₁) = l1++l2 := by simp [hl1,hl2]
    have h3 : n = l1.length := by rw [hl1]; simp [hn1]
    have h4 : w = l2++l1 := by rw [← hn2,h2,h3,List.rotate_append_length_eq l1]
    rw [h4,CycReduce,h2]
    have h5 := IsRed.of_reduce L₁
    rw [h2] at h5
    have h6 := IsRed.prefix_IsRed _ _ h5
    have h7 := IsRed.suffix_IsRed _ _ h5
    rcases IsRed.append_largest_cancel l2 l1 h7 h6 with ⟨I,J,K,hIK,hIJ,hJK⟩
    rw [hIJ,hJK]
    have h8 : FreeGroup.invRev J ++ K ++ (I ++ J) = FreeGroup.invRev J ++ (K ++ I) ++ J := by simp
    have h9 : Uncycle (FreeGroup.invRev J ++ (K ++ I) ++ J) = Uncycle (K++I) := by
      have := Uncycle.conj (FreeGroup.invRev J) (K++I)
      rwa [FreeGroup.invRev_invRev] at this
    rw [h8,h9,CycReduce,← List.append_assoc,distrib_reduce]
    have hI : IsRed I := IsRed.prefix_IsRed I K hIK
    have hK : IsRed K := IsRed.suffix_IsRed I K hIK
    rw [IsRed.equiv_of_reds] at hI hK hIK
    rw [hI,hK,hIK]
    rw [hIJ,hJK] at h5
    have h10 : FreeGroup.invRev J ++ K ++ (I ++ J) = FreeGroup.invRev J ++ (K ++ I) ++ J := by simp
    rw [h10] at h5
    have h11 : IsRed (K++I) := by exact IsRed.infix_IsRed (FreeGroup.invRev J) J (K ++ I) h5
    by_cases hIe : I = []
    · by_cases hKe : K = []
      · rw [hIe,hKe]
      · simp [hIe]; rfl
    · by_cases hKe : K = []
      · simp [hKe]; rfl
      · rw [← IsRed.equiv_of_reds] at hIK
        have h1 := IsRed.append_rotation_uncycled I K hIe hKe hIK
        have h2 := IsRed.append_rotation_uncycled _ _ hKe hIe h11
        rw [isUncycled_iff] at h1 h2
        rw [h1,h2]
        exact List.isRotated_append
  · intro h
    rw [CycReduce,CycReduce] at h
    have h1 := conj_if_cyc (FreeGroup.mk (Uncycle (FreeGroup.reduce L₁))) (FreeGroup.mk (Uncycle (FreeGroup.reduce L₂)))
    rw [FreeGroup.toWord_mk] at h1
    have h2 : IsRed (Uncycle (FreeGroup.reduce L₁)) := Uncycle.isRed_IsRed (FreeGroup.reduce L₁) (IsRed.of_reduce L₁)
    have h3 : IsRed (Uncycle (FreeGroup.reduce L₂)) := Uncycle.isRed_IsRed (FreeGroup.reduce L₂) (IsRed.of_reduce L₂)
    rw [IsRed.equiv_of_reds] at h3
    rw [h3] at h1
    have h4 : (∃ wrd, wrd ~r Uncycle (FreeGroup.reduce L₂) ∧ CycRed (FreeGroup.mk (Uncycle (FreeGroup.reduce L₁))) = FreeGroup.mk wrd) := by
      use Uncycle (FreeGroup.reduce L₁)
      constructor
      · exact h
      · rw [CycRed,FreeGroup.toWord_mk,← CycReduce,← CycReduce,CycReduce_idem]
    rcases h1 h4 with ⟨g,hg⟩
    have h5 : IsConj (FreeGroup.mk (Uncycle (FreeGroup.reduce L₁))) (FreeGroup.mk (Uncycle (FreeGroup.reduce L₂))) := by
      use ⟨g⁻¹,g,inv_mul_cancel g,Eq.symm (eq_mul_inv_of_mul_eq (one_mul g))⟩
      simp [SemiconjBy,mul_assoc,hg]
    have hl1u := Uncycle.isConj_to_self (FreeGroup.reduce L₁)
    have hl2u := Uncycle.isConj_to_self (FreeGroup.reduce L₂)
    symm at hl2u
    have h6 := IsConj.trans (IsConj.trans hl1u h5) hl2u
    rwa [FreeGroup.reduce.self,FreeGroup.reduce.self] at h6

example : IsConj (FreeGroup.mk [(1, True), (3, True), (2, False), (2, False), (1, False)]) (FreeGroup.mk [(2, False), (2, False), (3, True)]) := by
  rw[conj_iff_cyc']
  dsimp[CycReduce]
  simp[Uncycle]
  simp[← List.mem_cyclicPermutations_iff]
  exact List.mem_of_elem_eq_true rfl

#eval ([1,2,3] ~r [2,3, -1])

section Decidable

instance isConjugateDecidable {α : Type} [DecidableEq α] (l l' : List (α × Bool)) : Decidable (IsConj (FreeGroup.mk l) (FreeGroup.mk l')) := by
  rw[conj_iff_cyc']
  dsimp[CycReduce]
  exact (Uncycle (FreeGroup.reduce l)).isRotatedDecidable (Uncycle (FreeGroup.reduce l'))

end Decidable

open Lean.Elab.Tactic

/-! The following tactic conj_decide, decides if two given words, inputted as lists, are conjugate-/

syntax (name := conj_decide) "conj_decide" : tactic

@[tactic conj_decide]
def evalApplyConjCycSimp : Tactic := fun _stx => do
  evalTactic (← `(tactic| rw [conj_iff_cyc']))
  evalTactic (← `(tactic| dsimp [CycReduce]))
  evalTactic (← `(tactic| simp [Uncycle]))
  evalTactic (← `(tactic| simp[← List.mem_cyclicPermutations_iff]))
  evalTactic (← `(tactic| exact List.mem_of_elem_eq_true rfl))

--an application of the above tactic
example:  IsConj (FreeGroup.mk [(1, True), (3, True), (4, False), (2, False), (2, False), (1, False)]) (FreeGroup.mk [(4, False), (2, False), (2, False), (3, True)]) := by native_decide


/-Things that can be improved in the above tactic
  1. Capacity to handle abstract terms not just concrete examples, expand it to potentially prove results like  (e.g: x::y::ls +++ [x^-1] is conjugate to ls ++ [y]
  2. Show IsConj to be a decidable instance
  3. Make it an instance of native decide
-/

import DehnFunction.helper_lemmas



theorem Red_over_three {G: Type*} [DecidableEq G] (A B C: List (G × Bool)): FreeGroup.reduce (A ++ B ++ C) = FreeGroup.reduce (FreeGroup.reduce A ++ FreeGroup.reduce B ++ FreeGroup.reduce C) :=by
  rw[← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk]
  rw[FreeGroup.toWord_inj]

  rw[← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  repeat rw[FreeGroup.reduce.self]


theorem cycred_conj_to_cyc {G: Type*} [DecidableEq G] (A B: List (G × Bool)) (h_cycred: cycreduced B) (h_red: IsRed A): Uncycle (FreeGroup.reduce (A ++ B ++ FreeGroup.invRev A)) ~r B := by
  sorry

--basic theorem for freegroup
theorem Red_sum_invRev {G: Type*} [DecidableEq G] (A : List (G × Bool)) : FreeGroup.reduce ( FreeGroup.invRev A ++ A) = [] := by
  rw[← FreeGroup.toWord_mk]
  rw[← FreeGroup.toWord_one]
  rw[FreeGroup.toWord_inj, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  exact inv_mul_cancel (FreeGroup.mk A)


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

    .
      sorry


  have h_red: IsRed x := by

    sorry
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
    sorry
  have h_Stake_red: FreeGroup.reduce (List.take n S) = List.take n S := by
    sorry
  have h_Sdrop_red: FreeGroup.reduce (List.drop n S) = List.drop n S := by
    sorry
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

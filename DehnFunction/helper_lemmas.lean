import DehnFunction.Area1
import DehnFunction.Cyc_conj
import DehnFunction.IsRed

namespace FreeGroup

variable {α : Type*} [DecidableEq α] (L l P Q R : List (α × Bool))

omit [DecidableEq α] in
lemma invRev_concat (a : α×Bool) : invRev (L++[a]) = (a.1,!a.2)::(invRev L) := by simp [invRev]

omit [DecidableEq α] in
lemma invRev_singleton (a : α×Bool) : invRev [a] = [(a.1,!a.2)] := rfl

def CycReduce : List (α × Bool) := Uncycle (FreeGroup.reduce L)
-- Takes a list and returns cyclic reduction of that list's freely-reduced form.

lemma Uncycle.isRed_IsRed : IsRed L → IsRed (Uncycle L) := by
  intro hypo
  unfold IsRed at hypo
  unfold IsRed
  by_contra
  expose_names; simp at h
  rcases h with ⟨L', h₁,h₂⟩;
  apply Uncycle.property at L; rcases L with ⟨U,V,p₁,p₂⟩
  rw [<- FreeGroup.Red.append_append_left_iff U] at h₁
  have tempp : FreeGroup.Red V V := by exact FreeGroup.Red.refl
  have this_one : FreeGroup.Red (U ++ Uncycle L ++ V) (U ++ L' ++ V) := by apply FreeGroup.Red.append_append h₁ tempp
  rw [<-p₁] at this_one
  specialize hypo (U ++ L' ++ V)
  have this₁ : (U ++ L' ++ V) = L := by exact hypo this_one
  have this₂ : (U ++ L' ++ V) = (U ++ (Uncycle L) ++ V) := by rw [p₁] at this₁; exact this₁
  have this₃ : L' = Uncycle L := by
    apply List.append_cancel_right at this₂
    apply List.append_cancel_left at this₂; exact this₂
  contradiction

lemma form_of_conj (g y : FreeGroup α): (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]

def IsCycReduced (L : List (α × Bool)) : Prop := (IsRed L) ∧ (Uncycle L = L)

namespace IsRed

omit [DecidableEq α] in
lemma join_at_nonempty_left (hQ : IsRed Q) (h₁ : P = []) : IsRed (P ++ Q) := by
  rw [h₁]; simp [List.nil_append]; exact hQ

omit [DecidableEq α] in
lemma join_at_nonempty_right (hP : IsRed P) (h₂ : Q = []) : IsRed (P ++ Q) := by
  rw [h₂]; simp [List.nil_append]; exact hP

lemma append_IsRed_IsRed_if (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2  → IsRed (P ++ Q) := by
  induction P generalizing Q with
  | nil =>
    by_contra
    aesop
  | cons head tail ih =>
    specialize ih Q
    have this₁ : (head :: tail) = [head]++tail := by simp!
    rw [this₁] at hP
    have prelim : IsRed tail := IsRed.suffix_IsRed [head] tail hP
    simp [prelim, hQ] at ih
    have case_maker : tail = [] ∨ tail ≠ [] := by exact eq_or_ne tail []
    cases case_maker with
    | inl h =>
      rw [h] at hP; simp at hP
      simp [h]
      rw [equiv_of_reds]
      intros hypo₁
      rw [<-equiv_of_reds]
      exact (IsRed.cons_iff_not_red_pair Q h₂).mpr ⟨hQ,hypo₁⟩
    | inr h =>
      simp [h, h₂] at ih
      have tail_is_the_player : ((head :: tail).getLast h₁) = (tail.getLast h) := by exact List.getLast_cons h
      rw [tail_is_the_player]
      intro hypo_last
      apply ih at hypo_last
      rw [←this₁] at hP
      rw [IsRed.cons_iff_not_red_pair _ h] at hP
      exact (IsRed.cons_iff_not_red_pair (tail++Q) (List.append_ne_nil_of_left_ne_nil h Q)).mpr ⟨hypo_last,by convert hP.2 using 2 <;> simp [List.head_append,h]⟩

lemma invRev_IsRed (hl : IsRed l) : IsRed (FreeGroup.invRev l) := by
  induction l with
  | nil => simp [nil]
  | cons a as ih =>
    match as with
    | [] => simp [FreeGroup.invRev,singleton]
    | b::bs =>
      rw [FreeGroup.invRev_cons,FreeGroup.invRev_cons,FreeGroup.invRev_singleton,FreeGroup.invRev_singleton,← concat_iff_end_not_red_pair]
      constructor
      · rw [← FreeGroup.invRev_singleton,← FreeGroup.invRev_cons]
        exact ih (tail (b :: bs) hl)
      · rw [cons_cons_iff_not_red_pair] at hl
        aesop

theorem iff_invRev_IsRed : IsRed l ↔ IsRed (FreeGroup.invRev l) :=
  ⟨fun h => invRev_IsRed _ h,fun h => (Eq.symm (FreeGroup.invRev_invRev (L₁:=l))) ▸ invRev_IsRed _ h⟩

lemma append_or_inv_append (L₁ L₂ : List (α × Bool)) (h₁ : IsCycReduced L₁) (h₂ : IsRed L₂):
  (IsRed (L₂ ++ L₁)) ∨ (IsRed (L₁ ++ FreeGroup.invRev L₂)) := by
  match L₁ with
  | [] => simp [h₂]
  | a::as =>
    by_cases h2 : L₂ = []
    · simp [h2,h₁.1]
    · by_cases hab : a.1 = (L₂.getLast h2).1 ∧ a.2 = !(L₂.getLast h2).2
      · right
        have h3 : IsUncycled (a::as) := by refine (isUncycled_iff (a :: as)).mpr h₁.2
        match as with
        | [] =>
          have h2c := List.concat_if_not_empty _ h2
          rw [h2c]
          simp [List.cons_append,FreeGroup.invRev_singleton]
          rw [IsRed.cons_cons_iff_not_red_pair]
          constructor
          · rw [← FreeGroup.invRev_concat,← h2c]
            exact IsRed.invRev_IsRed _ h₂
          · right
            exact hab.2
        | b::bs =>
          simp [IsUncycled] at h3
          apply append_IsRed_IsRed_if _ _ h₁.1 (IsRed.invRev_IsRed _ h₂) (by simp) (by simp [FreeGroup.invRev,h2])
          have h4 : ((a::b::bs).getLast (by simp)) = ((b::bs).getLast (by simp)) := by exact List.getLast_cons (by simp)
          simp_rw [h4]
          have h5 : (FreeGroup.invRev L₂).head (by simp [FreeGroup.invRev,h2]) = ((L₂.getLast h2).1,!(L₂.getLast h2).2) := by simp [FreeGroup.invRev]
          rw [h5]
          aesop
      · left
        apply append_IsRed_IsRed_if _ _ h₂ h₁.1 h2 (by simp only [ne_eq, reduceCtorEq,not_false_eq_true])
        rw [not_and_or] at hab
        aesop

lemma append_largest_cancel (h₁ : IsRed P) (h₂ : IsRed Q) : ∃ (I J K : List (α × Bool)), (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by
  induction P using IsRed_inductive.induct with
  | case1 =>
    use []
    use []
    use Q
    simp [h₂]
  | case2 g =>
    by_cases hQ : Q = []
    · use [g]
      use []
      use []
      simp [h₁,hQ]
    · by_cases hg : g.1 = (Q.head hQ).1 ∧ g.2 = !(Q.head hQ).2
      · use []
        use [g]
        use Q.tail
        simp
        constructor
        · rw [← List.head_cons_tail Q hQ] at h₂
          exact IsRed.tail Q.tail h₂
        · rw [FreeGroup.invRev_singleton]
          simp [hg]
      · use [g]
        use []
        use Q
        simp
        rw [not_and_or,Bool.eq_not_iff] at hg
        push_neg at hg
        exact (IsRed.cons_iff_not_red_pair Q hQ).mpr ⟨h₂,hg⟩
  | case3 g h gs ih =>
    rw [IsRed.cons_cons_iff_not_red_pair] at h₁
    rcases ih h₁.1 with ⟨a,b,c,hac,hab,hbc⟩
    by_cases hae : a = []
    · match c with
      | [] =>
        use [g]
        use b
        use []
        simp [hae] at hab hbc
        simp [hab,hbc]
        exact IsRed.singleton
      | j::js =>
        simp [hae] at hab
        rw [hbc,← hab,FreeGroup.invRev_cons,FreeGroup.invRev_singleton] at h₂
        have h1 : IsRed ([(h.1, !h.2),j]) := by
          apply IsRed.prefix_IsRed _ js
          apply IsRed.suffix_IsRed (FreeGroup.invRev gs) _
          aesop
        rw [IsRed.two_iff_not_red_pair] at h1
        simp at h1
        by_cases hgc : g.1 = j.1 ∧ g.2 = !j.2
        · use []
          use g::h::gs
          use js
          simp
          constructor
          · exact IsRed.tail _ (IsRed.suffix_IsRed _ _ hac)
          · rw [FreeGroup.invRev_cons,hab,FreeGroup.invRev_singleton]
            simp [hgc,hbc]
        · use [g]
          use h::gs
          use j::js
          simp
          constructor
          · simp [hae] at hac
            rw [not_and_or,Bool.eq_not_iff] at hgc
            push_neg at hgc
            exact (IsRed.cons_cons_iff_not_red_pair js).mpr ⟨hac,hgc⟩
          · simp [hab,hbc]
    · use g::a
      use b
      use c
      simp
      constructor
      · have h1 : (a++c).head (List.append_ne_nil_of_left_ne_nil hae c) = (h::gs).head (List.cons_ne_nil h gs) := by
          simp_rw [hab]
          rw [List.head_append_left (hae),List.head_append_of_ne_nil hae]
        rw [List.head_cons] at h1
        rw [← h1] at h₁
        rw [IsRed.cons_iff_not_red_pair]
        exact ⟨hac,h₁.2⟩
      · exact ⟨hab,hbc⟩

lemma append_largest_cancel_nonempty (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧ (J ≠ []) ∧ (IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by
  intro h
  have h1 := append_largest_cancel _ _ h₁ h₂
  rcases h1 with ⟨I,J,K,hIK,hIJ,hJK⟩
  use I
  use J
  use K
  rw [hIJ] at h₁
  constructor
  · exact IsRed.prefix_IsRed I J h₁
  · constructor
    · exact IsRed.suffix_IsRed I J h₁
    · constructor
      · by_cases hJ : J = []
        · rw [hJ] at h₁ hIJ hJK
          simp at *
          rw [hIJ,hJK] at h
          contradiction
        · exact hJ
      · constructor
        · exact IsRed.suffix_IsRed I K hIK
        · exact ⟨hIK,hIJ,hJK⟩

end IsRed

lemma reduce_inv : FreeGroup.reduce (P ++ FreeGroup.invRev P) = [] := by
  induction P with
  | nil => simp
  | cons head tail ih =>
    have this₁ : head :: tail = [head] ++ tail := by rfl
    rw [this₁,invRev_append]
    have this₂ : [head] ++ tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]) = [head] ++ (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head])) := by simp
    rw [this₂]
    have this₃ : FreeGroup.reduce ([head] ++ (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) = FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) := by simp [FreeGroup.reduce_append_reduce_reduce]
    rw [this₃]
    have this₄ : FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) = FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (FreeGroup.reduce (tail ++ (FreeGroup.invRev tail)) ++ FreeGroup.reduce (FreeGroup.invRev [head]))) := by simp [FreeGroup.reduce_append_reduce_reduce]
    rw [this₄,ih]
    simp only [List.nil_append, FreeGroup.reduce_append_reduce_reduce]
    simp only [FreeGroup.reduce_invRev]
    have : FreeGroup.reduce [head] = [head] := by exact rfl
    rw [this]
    cases head with
    | mk fst snd => simp [FreeGroup.invRev]

lemma distrib_reduce : FreeGroup.reduce (P++ Q ++ FreeGroup.invRev Q ++ R) = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (R)) := by calc
  FreeGroup.reduce (P++ Q ++ FreeGroup.invRev Q ++ R) = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (Q ++ FreeGroup.invRev Q ++ R)) := by simp [FreeGroup.reduce_append_reduce_reduce]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (FreeGroup.reduce (Q ++ FreeGroup.invRev Q) ++ FreeGroup.reduce R)) := by simp [FreeGroup.reduce_append_reduce_reduce]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce ([] ++ FreeGroup.reduce R)) := by simp [reduce_inv]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (FreeGroup.reduce R)) := by simp!
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce R) := by simp [invRev_invRev]

lemma IsRed.append_nonempty (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) → (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
  intro hypo
  by_contra
  expose_names
  simp at h
  have P_is_like : P = (P.dropLast) ++ [P.getLast h₁] := by exact Eq.symm (List.dropLast_concat_getLast h₁)
  have Q_is_like : Q = [Q.head h₂] ++ Q.tail := by simp
  have P_end_end : (P.getLast h₁).2 ≠ (Q.head h₂).2 := by simp [h.2]
  have P_end_end_end : (P.getLast h₁).2 = !(Q.head h₂).2 := by exact Bool.eq_not.mpr P_end_end
  have P_end : [P.getLast h₁] = [((Q.head h₂).1, !(Q.head h₂).2)] := by calc
    [P.getLast h₁] = [((P.getLast h₁).1, (P.getLast h₁).2)] := by simp
    _ = [((Q.head h₂).1, !(Q.head h₂).2)] := by
      rw [h.1]
      rw [P_end_end_end]
  have Q_end : [Q.head h₂] = [((Q.head h₂).1, (Q.head h₂).2)] := by simp
  have this₁ : (P ++ Q) = P.dropLast ++ [((Q.head h₂).1, !(Q.head h₂).2)] ++ [((Q.head h₂).1, (Q.head h₂).2)] ++ Q.tail := by
    nth_rewrite 1 [P_is_like, Q_is_like, P_end, Q_end]
    simp
  have scandal : [((Q.head h₂).1, (Q.head h₂).2)] = FreeGroup.invRev [((Q.head h₂).1, !(Q.head h₂).2)] := by
    unfold FreeGroup.invRev
    simp
  rw [scandal] at this₁
  have this₂ : FreeGroup.reduce (P.dropLast ++ [((Q.head h₂).1, !(Q.head h₂).2)] ++ FreeGroup.invRev [((Q.head h₂).1, !(Q.head h₂).2)] ++ Q.tail) = FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce Q.tail) := by rw [distrib_reduce (P.dropLast) [((Q.head h₂).1, !(Q.head h₂).2)] Q.tail]

  rw [<-scandal] at this₁ this₂
  rw [<- this₁] at this₂
  rw [equiv_of_reds] at hypo
  rw [hypo] at this₂
  let n₁ : ℕ := P.length
  let n₂ : ℕ := Q.length
  have a₁ : P.length > (P.dropLast).length := by calc
    P.length = (P.dropLast ++ [P.getLast h₁]).length := by exact congrArg List.length P_is_like
    _ = (P.dropLast).length + [P.getLast h₁].length := by exact List.length_append
    _ > (P.dropLast).length := by simp
  have a₂ : Q.length > (Q.tail).length := by calc
    Q.length = ([Q.head h₂] ++ (Q.tail)).length := by simp
    _ = [Q.head h₂].length + Q.tail.length := by exact List.length_append
    _ > Q.tail.length := by simp
  have a₃ : FreeGroup.Red (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail) (FreeGroup.reduce (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) := by exact
    FreeGroup.reduce.red
  have a₄ : ∃ n, List.length ((FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) = List.length (FreeGroup.reduce (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail)) + 2 * n := by exact FreeGroup.Red.length a₃
  rcases a₄ with ⟨m, a₄⟩
  have a₅_1 : FreeGroup.Red P.dropLast (FreeGroup.reduce P.dropLast) := by exact FreeGroup.reduce.red
  have a₅_2 : ∃ n, List.length (P.dropLast) = List.length ((FreeGroup.reduce P.dropLast)) + 2 * n := by exact FreeGroup.Red.length a₅_1
  rcases a₅_2 with ⟨m₁, a₅⟩
  have a₆_1 : FreeGroup.Red Q.tail (FreeGroup.reduce Q.tail) := by exact FreeGroup.reduce.red
  have a₆_2 : ∃ n, List.length (Q.tail) = List.length ((FreeGroup.reduce Q.tail)) + 2 * n := by exact FreeGroup.Red.length a₆_1
  rcases a₆_2 with ⟨m₂, a₆⟩
  have a₇ : (P ++ Q).length > (FreeGroup.reduce P.dropLast ++ FreeGroup.reduce Q.tail).length := by calc
    (P ++ Q).length = P.length + Q.length := by simp!
    _ > P.length + Q.tail.length := by linarith [a₂]
    _ > P.dropLast.length + Q.tail.length := by linarith
    _ >= (FreeGroup.reduce (P.dropLast)).length + (FreeGroup.reduce (Q.tail)).length := by linarith
    _ = (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)).length := by exact Eq.symm List.length_append
  have a₈_1 : FreeGroup.Red (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)) (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))) := by exact FreeGroup.reduce.red
  have a₈_2 : ∃ n, List.length (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)) = List.length ((FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail)))) + 2 * n := by exact FreeGroup.Red.length a₈_1
  rcases a₈_2 with ⟨m₃, a₈⟩
  have a₉ : (P ++ Q).length > (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))).length := by linarith
  have a₀ : (P ++ Q).length = (FreeGroup.reduce (FreeGroup.reduce (P.dropLast) ++ FreeGroup.reduce (Q.tail))).length := by exact congrArg List.length this₂
  linarith

lemma IsRed.append_nonempty_iff (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) ↔ (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
  constructor
  exact fun a ↦ IsRed.append_nonempty P Q h₁ h₂ a
  exact fun a ↦ append_IsRed_IsRed_if P Q hP hQ h₁ h₂ a

lemma IsRed.app_red_still_red (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) (h₃ : Q ≠ []): (IsRed (P++Q++R)) := by
  have Pcases : (P = []) ∨ (P ≠ []) := by exact eq_or_ne P []
  have Rcases : (R = []) ∨ (R ≠ []) := by exact eq_or_ne R []
  cases Pcases with
  | inl h =>
    cases Rcases with
    | inl h =>
      expose_names
      aesop
    | inr h =>
      expose_names
      aesop
  | inr h =>
    cases Rcases with
    | inl h =>
      expose_names
      aesop
    | inr h =>
      expose_names
      have QRne : Q ++ R ≠ [] := by exact List.append_ne_nil_of_left_ne_nil h₃ R
      have main : (Q ++ R).head QRne= Q.head h₃ := by simp [h₃]
      have this : IsRed (P ++ (Q ++ R)) := by
        rw [IsRed.append_nonempty_iff]
        rw [main]
        rw [<-IsRed.append_nonempty_iff]
        exact h₁
        exact hp
        exact hq
        exact h_1
        exact hp
        exact h₂
      simp [this]

lemma isCycReduced_cycPerm_IsCycReduced : IsCycReduced (P ++ Q) → IsCycReduced (Q ++ P) := by
  intro ⟨hPQ1,hPQ2⟩
  rw [← isUncycled_iff] at hPQ2
  match P with
  | [] =>
    simp at *
    rw [isUncycled_iff] at hPQ2
    exact ⟨hPQ1,hPQ2⟩
  | [a] =>
    match Q with
    | [] =>
      simp at *
      rw [isUncycled_iff] at hPQ2
      exact ⟨hPQ1,hPQ2⟩
    | [c] =>
      simp at *
      constructor
      · rw [IsRed.two_iff_not_red_pair] at hPQ1 ⊢
        tauto
      · rw [isUncycled_iff] at hPQ2
        simp [Uncycle,-not_and] at *
        tauto
    | c::d::ds =>
    constructor
    · simp [IsUncycled] at hPQ2
      have h1 := List.concat_if_not_empty (d::ds) (by simp)
      have h2 : c :: ((d :: ds).dropLast ++ [(d :: ds).getLast (by simp)]) ++ [a] = (c :: (d :: ds).dropLast) ++ [(d :: ds).getLast (by simp)] ++ [a] := by simp
      rw [h1,h2,← IsRed.concat_iff_end_not_red_pair]
      have h3 : (c :: (d :: ds).dropLast ++ [(d :: ds).getLast (by simp)]) = c::((d :: ds).dropLast ++ [(d :: ds).getLast (by simp)]) := rfl
      rw [h3,← h1]
      exact ⟨IsRed.suffix_IsRed ([a]) _ hPQ1,by tauto⟩
    · rw [← isUncycled_iff]
      have h1 : c :: d :: ds ++ [a] = c::(d::ds++[a]) := rfl
      rw [h1]
      simp [IsUncycled]
      simp [IsRed.cons_cons_iff_not_red_pair] at hPQ1
      tauto
  | a::b::bs =>
    match Q with
    | [] =>
      simp at *
      rw [isUncycled_iff] at hPQ2
      exact ⟨hPQ1,hPQ2⟩
    | [c] =>
      rw [IsCycReduced]
      simp [IsUncycled] at hPQ2 ⊢
      constructor
      · exact (IsRed.cons_cons_iff_not_red_pair (b::bs)).mpr ⟨IsRed.prefix_IsRed (a :: b :: bs) [c] hPQ1,by tauto⟩
      · rw [← isUncycled_iff]
        simp [IsUncycled]
        have h1 := List.concat_if_not_empty (b::bs) (by simp)
        rw [h1] at hPQ1
        apply (IsRed.concat_iff_end_not_red_pair (a :: (b :: bs).dropLast)).mpr at hPQ1
        tauto
    | c::d::ds =>
      simp [IsUncycled] at hPQ2
      constructor
      · have h1 : (d::ds).getLast (List.cons_ne_nil d ds) = (c::d::ds).getLast (List.cons_ne_nil c (d::ds)) := rfl
        apply IsRed.append_IsRed_IsRed_if _ _ (IsRed.suffix_IsRed (a :: b :: bs) (c :: d :: ds) hPQ1) (IsRed.prefix_IsRed (a :: b :: bs) (c :: d :: ds) hPQ1) (List.cons_ne_nil c (d :: ds)) (List.cons_ne_nil a (b :: bs))
        rw [← h1]
        simp
        tauto
      · rw [← isUncycled_iff]
        simp [IsUncycled]
        rw [IsRed.append_nonempty_iff _ _ (IsRed.prefix_IsRed (a :: b :: bs) (c :: d :: ds) hPQ1) (IsRed.suffix_IsRed (a :: b :: bs) (c :: d :: ds) hPQ1) (List.cons_ne_nil a (b :: bs)) (List.cons_ne_nil c (d :: ds))] at hPQ1
        simp at hPQ1
        tauto

lemma List.append_nonempty (h : P ++ Q ≠ []) : (P ≠ []) ∨ (Q ≠ []) := by
  apply Decidable.not_and_iff_or_not.mp ?_
  by_contra
  expose_names
  have : P ++ Q = [] := by calc
    P ++ Q = [] ++ [] := by rw [h_1.1, h_1.2]
    _ = [] := by simp
  contradiction

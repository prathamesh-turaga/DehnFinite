import DehnFunction.Area1
import DehnFunction.Cyc_conj
import DehnFunction.IsRed



-- STUFF FROM AREA2



def CycReduce {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) := Uncycle (FreeGroup.reduce L)
-- Takes a list and returns cyclic reduction of that list's freely-reduced form.



lemma app_lists_eq_canc_r {k : Type*}: ∀ (P Q R : List k), P ++ Q = R ++ Q → P = R := by exact fun P Q R a ↦ List.append_cancel_right a
lemma app_lists_eq_canc_l {k : Type*}: ∀ (P Q R : List k), Q ++ P = Q ++ R → P = R := by exact fun P Q R a ↦ List.append_cancel_left a

lemma uncyc_of_red_is_red {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L → IsRed (Uncycle L) := by
  intro hypo
  unfold IsRed at hypo
  unfold IsRed
  by_contra
  expose_names; simp at h
  rcases h with ⟨L', h₁,h₂⟩;
  apply Uncycle_property at L; rcases L with ⟨U,V,p₁,p₂⟩
  rw [<- FreeGroup.Red.append_append_left_iff U] at h₁
  have tempp : FreeGroup.Red V V := by exact FreeGroup.Red.refl
  have this_one : FreeGroup.Red (U ++ Uncycle L ++ V) (U ++ L' ++ V) := by apply FreeGroup.Red.append_append h₁ tempp
  rw [<-p₁] at this_one
  specialize hypo (U ++ L' ++ V)
  have this₁ : (U ++ L' ++ V) = L := by exact hypo this_one
  have this₂ : (U ++ L' ++ V) = (U ++ (Uncycle L) ++ V) := by rw [p₁] at this₁; exact this₁
  have this₃ : L' = Uncycle L := by
    apply app_lists_eq_canc_r at this₂
    apply app_lists_eq_canc_l at this₂; exact this₂
  contradiction


lemma equiv_of_reds {α : Type*} [DecidableEq α] (L : List (α × Bool)) : IsRed L ↔ FreeGroup.reduce L = L := by
  constructor
  unfold IsRed; intro hypo
  have this₁ : FreeGroup.Red L (FreeGroup.reduce L) := by exact FreeGroup.reduce.red
  apply hypo at this₁; exact this₁
  intro hypo
  unfold IsRed;
  intro J
  intro are_rel_by_red
  have this₂ : FreeGroup.Red J (FreeGroup.reduce J) := by exact FreeGroup.reduce.red
  have RLJ : FreeGroup.Red L J := by exact are_rel_by_red
  apply FreeGroup.reduce.eq_of_red at are_rel_by_red
  rw [hypo] at are_rel_by_red
  rw [<-are_rel_by_red] at this₂
  apply FreeGroup.Red.sublist at RLJ
  apply FreeGroup.Red.sublist at this₂
  apply List.Sublist.antisymm RLJ this₂

-- reduced word a₁a₂...a_n is cycreduced iff it is reduced and ¬(a₁a_n = 1)

-- The last part can be said for the word as a list also. L represents a reduced word iff :
-- it is "reduced" (as a list, so would need to invoke standard free reduction somehow) and
-- (([L.head].mk) * ([L.getLast].mk) = 1)

-- Lemma : ∃! red and cycred reps for each equiv class that a FG constitutes.
-- pg 176 of pdf has an outline
-- Propn (w, w' cycreduced) : w.conj w' ↔ they are cyclically equivalent



--  have other₁ : True := sorry
--  simp [this₁, this₂, that₁, that₂, that₃]




lemma form_of_conj {α : Type*} [DecidableEq α] (g y : FreeGroup α): (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]



def cycreduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := (IsRed L) ∧ (Uncycle L = L)

lemma isredsubl {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : IsRed (P ++ Q)) : (IsRed P) ∧ (IsRed Q) := by exact ⟨IsRed.prefix_IsRed P Q h,IsRed.suffix_IsRed P Q h⟩

lemma red_join_at_nonempty_left {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P = []) (h₂ : Q ≠ []) : IsRed (P ++ Q) := by
  rw [h₁]; simp [List.nil_append]; exact hQ

lemma red_join_at_nonempty_right {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q = []) : IsRed (P ++ Q) := by
  rw [h₂]; simp [List.nil_append]; exact hP

lemma red_at_join_nonempty_both {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2  → IsRed (P ++ Q) := by
  induction P generalizing Q with
  | nil =>
    by_contra
    aesop
  | cons head tail ih =>
    specialize ih Q
    have this₁ : (head :: tail) = [head]++tail := by simp!
    rw [this₁] at hP

    have prelim : IsRed tail := by
      have hRed_and_tRed : IsRed [head] ∧ IsRed tail := by apply isredsubl [head] tail hP
      exact hRed_and_tRed.2
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

lemma FreeGroup.invRev_concat {α : Type*} [DecidableEq α] (L : List (α×Bool)) (a : α×Bool) : invRev (L++[a]) = (a.1,!a.2)::(invRev L) := by simp [invRev]

lemma FreeGroup.invRev_singleton {α : Type*} [DecidableEq α] (a : α×Bool) : invRev [a] = [(a.1,!a.2)] := rfl

lemma IsRed.invRev_IsRed {α : Type*} [DecidableEq α] (l : List (α×Bool)) (hl : IsRed l) : IsRed (FreeGroup.invRev l) := by
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

theorem IsRed.iff_invRev_IsRed {α : Type*} [DecidableEq α] (l : List (α×Bool)) : IsRed l ↔ IsRed (FreeGroup.invRev l) :=
  ⟨fun h => invRev_IsRed _ h,fun h => (Eq.symm (FreeGroup.invRev_invRev (L₁:=l))) ▸ invRev_IsRed _ h⟩

lemma uncyclicmid {α : Type*} [DecidableEq α] (L₁ L₂ : List (α × Bool)) (h₁ : cycreduced L₁) (h₂ : IsRed L₂):
  (IsRed (L₂ ++ L₁)) ∨ (IsRed (L₁ ++ FreeGroup.invRev L₂)) := by
  match L₁ with
  | [] => simp [h₂]
  | a::as =>
    by_cases h2 : L₂ = []
    · simp [h2,h₁.1]
    · by_cases hab : a.1 = (L₂.getLast h2).1 ∧ a.2 = !(L₂.getLast h2).2
      · right
        have h3 : uncycled (a::as) := by refine (uncycled_iff (a :: as)).mpr h₁.2
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
          simp [uncycled] at h3
          apply red_at_join_nonempty_both _ _ h₁.1 (IsRed.invRev_IsRed _ h₂) (by simp) (by simp [FreeGroup.invRev,h2])
          have h4 : ((a::b::bs).getLast (by simp)) = ((b::bs).getLast (by simp)) := by exact List.getLast_cons (by simp)
          simp_rw [h4]
          have h5 : (FreeGroup.invRev L₂).head (by simp [FreeGroup.invRev,h2]) = ((L₂.getLast h2).1,!(L₂.getLast h2).2) := by simp [FreeGroup.invRev]
          rw [h5]
          aesop
      · left
        apply red_at_join_nonempty_both _ _ h₂ h₁.1 h2 (by simp only [ne_eq, reduceCtorEq,not_false_eq_true])
        rw [not_and_or] at hab
        aesop

lemma largest_cancel {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ∃ (I J K : List (α × Bool)), (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by
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
      have h1 : a.head hae = h := by

lemma technique {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧ (J ≠ []) ∧ (IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by
  intro h


-- extremely important


lemma uncyc_on_conj {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : Uncycle (P ++ Q ++ FreeGroup.invRev P) = Uncycle Q := by sorry
-- is done by omar

lemma inv_of_app {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : FreeGroup.invRev (P++Q) = (FreeGroup.invRev Q) ++ (FreeGroup.invRev P) := by exact
  FreeGroup.invRev_append

lemma inv_of_inv {α : Type*} [DecidableEq α] (P : List (α × Bool)) : FreeGroup.invRev (FreeGroup.invRev P) = P := by exact
  FreeGroup.invRev_invRev

lemma cancel_inverses {α : Type*} [DecidableEq α] (P : List (α × Bool)) : FreeGroup.reduce (P ++ FreeGroup.invRev P) = [] := by
  induction P with
  | nil => simp
  | cons head tail ih =>
    have this₁ : head :: tail = [head] ++ tail := by rfl
    rw [this₁]
    rw [inv_of_app [head] tail]
    have this₂ : [head] ++ tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]) = [head] ++ (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head])) := by simp
    rw [this₂]
    have this₃ : FreeGroup.reduce ([head] ++ (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) = FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) := by simp [FreeGroup.reduce_append_reduce_reduce]
    rw [this₃]
    have this₄ : FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (tail ++ (FreeGroup.invRev tail ++ FreeGroup.invRev [head]))) = FreeGroup.reduce (FreeGroup.reduce [head] ++ FreeGroup.reduce (FreeGroup.reduce (tail ++ (FreeGroup.invRev tail)) ++ FreeGroup.reduce (FreeGroup.invRev [head]))) := by simp [FreeGroup.reduce_append_reduce_reduce]
    rw [this₄]
    rw [ih]
    simp only [List.nil_append, FreeGroup.reduce_append_reduce_reduce]
    simp only [FreeGroup.reduce_invRev]
    have : FreeGroup.reduce [head] = [head] := by exact rfl
    rw [this]
    cases head with
    | mk fst snd => simp [FreeGroup.invRev]



lemma distrib_reduce {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)): FreeGroup.reduce (P++ Q ++ FreeGroup.invRev Q ++ R) = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (R)) := by calc
  FreeGroup.reduce (P++ Q ++ FreeGroup.invRev Q ++ R) = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (Q ++ FreeGroup.invRev Q ++ R)) := by simp [FreeGroup.reduce_append_reduce_reduce]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (FreeGroup.reduce (Q ++ FreeGroup.invRev Q) ++ FreeGroup.reduce R)) := by simp [FreeGroup.reduce_append_reduce_reduce]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce ([] ++ FreeGroup.reduce R)) := by simp [cancel_inverses]
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce (FreeGroup.reduce R)) := by simp!
  _ = FreeGroup.reduce (FreeGroup.reduce P ++ FreeGroup.reduce R) := by simp [inv_of_inv]

lemma join_is_red_then_safe {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) → (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
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

lemma join_red_iff_safe {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : IsRed (P ++ Q) ↔ (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2 := by
  constructor
  exact fun a ↦ join_is_red_then_safe P Q hP hQ h₁ h₂ a
  exact fun a ↦ red_at_join_nonempty_both P Q hP hQ h₁ h₂ a

lemma app_red_still_red {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)) (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) (h₃ : Q ≠ []): (IsRed (P++Q++R)) := by
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
        rw [join_red_iff_safe]
        rw [main]
        rw [<-join_red_iff_safe]
        exact h₁
        exact hp
        exact hq
        exact h_1
        exact hp
        exact h₂
      simp [this]

-- extremely important

lemma uncyc_then_comm_lists₁ {α : Type*} [DecidableEq α] (P : List (α × Bool)) : ∀ K, K~r P → cycreduced (P) → cycreduced (K) := by
  induction P with
  | nil => sorry
  | cons head tail ih =>
    intro hd hypo
    specialize ih hd; specialize ih
    sorry
-- extremely important

lemma uncyc_then_comm_lists₂ {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : cycreduced (P ++ Q) → cycreduced (Q ++ P) := by sorry
-- need this exactly in proof, don't remove for now.


-- is done by vivek



lemma inv_of_red {α : Type*} [DecidableEq α] (P : List (α × Bool)) : IsRed P → IsRed (FreeGroup.invRev P) := by
  intro hypo
  rw [equiv_of_reds] at hypo ⊢
  rw [FreeGroup.reduce_invRev, hypo]

lemma appnonempty_then_some_nonempty {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : P ++ Q ≠ []) : (P ≠ []) ∨ (Q ≠ []) := by
  apply Decidable.not_and_iff_or_not.mp ?_
  by_contra
  expose_names
  have : P ++ Q = [] := by calc
    P ++ Q = [] ++ [] := by rw [h_1.1, h_1.2]
    _ = [] := by simp
  contradiction

lemma uncyc_red_isrotated_red_uncyc₁ {α : Type*} [DecidableEq α] : ∀ (g x  : FreeGroup α), (xhypo : cycreduced x.toWord) → (Uncycle ((g*x*g⁻¹).toWord)) ~r (FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord))) := by
  intro g x
  rw [form_of_conj]
  let Lg := g.toWord
  let Lx := x.toWord
  have : g⁻¹.toWord = FreeGroup.invRev g.toWord := by exact FreeGroup.toWord_inv g
  have gRed : IsRed g.toWord := by apply (equiv_of_reds g.toWord).mpr; exact FreeGroup.reduce_toWord g
  rw [this]
  rw [uncyc_on_conj]
  cases h_g: g.toWord with
  | nil => -- g empty
      simp
      have this₁ : IsRed x.toWord := by simp [(equiv_of_reds x.toWord)]
      have this₂ : IsRed (Uncycle x.toWord) := by
        simp [uncyc_of_red_is_red x.toWord this₁]
      simp [equiv_of_reds x.toWord] at this₂
      have this₃ : FreeGroup.reduce (Uncycle x.toWord) = (Uncycle x.toWord) := by exact (equiv_of_reds (Uncycle x.toWord)).mp this₂
      rw [this₃]
      intro dd
      aesop
  | cons head tail => --nontrivial conjugation of x with g≠ []
    intro CC'
    unfold cycreduced at CC'
    have CC : cycreduced x.toWord := by exact CC'
    rcases CC' with ⟨xisred, xisuncyclic⟩
    rw [xisuncyclic]
    apply (equiv_of_reds x.toWord).mp at xisred; simp only [xisred]
    have xisred' : IsRed x.toWord := by exact(equiv_of_reds x.toWord).mpr xisred
    have mylem : IsRed (head :: tail ++ x.toWord) ∨ IsRed (x.toWord ++ FreeGroup.invRev (head :: tail)) := by
      exact uncyclicmid x.toWord (head :: tail) CC
    have xcases : (x.toWord = []) ∨ (x.toWord ≠ []) := by exact eq_or_ne x.toWord []
    cases xcases with
      | inl xcontent => -- x is empty
        rw [xcontent, List.append_nil, cancel_inverses]
        aesop
      | inr xcontent =>  -- x ≠ []
        cases mylem with
        | inl h =>
          -- (h::t ++ x) is reduced, what about the other?
          by_cases hh : IsRed (x.toWord ++ FreeGroup.invRev (head :: tail))
          · -- both htx and xt⁻¹ h⁻¹ reduced.
            have htRed : IsRed (head :: tail) := by rw [h_g] at gRed; exact gRed
            have htinvRed : IsRed (FreeGroup.invRev (head :: tail)) := by exact inv_of_red (head :: tail) htRed
            have full_red: IsRed ((head :: tail) ++ x.toWord ++ FreeGroup.invRev (head :: tail)) := by apply app_red_still_red (head :: tail) (x.toWord) (FreeGroup.invRev (head :: tail)) htRed xisred' htinvRed h hh xcontent
            rw [equiv_of_reds] at full_red
            rw [full_red]
            rw [uncyc_on_conj]
            aesop
          · -- htx red but not xt⁻¹h⁻¹, so...? technique on?
            -- apply technique, then inside take cases on x content. Need : sublist of red is red. cases on x and J
            apply technique at hh
            rcases hh with ⟨I, J, K, hI, hJ, jNE, hK, hIK, hxLike, hHTinvLike⟩
            -- here's how to get the inv of an append :
            have hHTLike : (head :: tail) = (FreeGroup.invRev K) ++ J := by
              have temp : FreeGroup.invRev (FreeGroup.invRev (head :: tail)) = FreeGroup.invRev (FreeGroup.invRev J ++ K) := by exact congrArg FreeGroup.invRev hHTinvLike
              rw [inv_of_app, inv_of_inv, inv_of_inv] at temp
              exact temp
            nth_rewrite 1 [hxLike, hHTinvLike, hHTLike]
            have convenience₁ : (FreeGroup.invRev K ++ J ++ (I ++ J) ++ (FreeGroup.invRev J ++ K)) = (FreeGroup.invRev K ++ J ++ I) ++ J ++ (FreeGroup.invRev J) ++ K := by simp
            rw [convenience₁]
            rw [distrib_reduce, FreeGroup.reduce_append_reduce_reduce]
            -- now remember h : IsRed (head :: tail ++ x.toWord)
            rw [hHTLike, hxLike, <-List.append_assoc] at h
            -- Now to deal with K⁻¹JIK, (using IsRed KJIJ → IsRed JI), we need one of J and I to be nonempty. We will club things accordingly.
            have KinvRed : IsRed (FreeGroup.invRev K) := by exact inv_of_red K hK
            have KinvJRed : IsRed ((FreeGroup.invRev K)++J) := by
              rw [h_g] at gRed; rw [hHTLike] at gRed; exact gRed

            have convenience₂ : (FreeGroup.invRev K ++ J ++ I ++ J) = (FreeGroup.invRev K) ++ (J ++ I ++ J) := by simp
            rw [convenience₂] at h
            have KinvRed_JIJRed : IsRed (FreeGroup.invRev K) ∧ IsRed (J++I++J) := by
              apply isredsubl (FreeGroup.invRev K) (J ++ I ++ J) h
            -- have convenience₃ : J ++ I ++ J = (J ++ I) ++ J := by
            have JIRed_JRed : IsRed (J++I) ∧ IsRed J := by
               apply isredsubl (J++I) J KinvRed_JIJRed.2
              -- is a sublist of the reduced word at h
            rw [hxLike] at xcontent
            apply appnonempty_then_some_nonempty at xcontent
            cases xcontent with
            | inl NONEMPTY =>
              have Jcases : J = [] ∨ J ≠ [] := by exact eq_or_ne J []
              cases Jcases with
              | inl Jcontent =>
                simp only [Jcontent, List.append_nil, List.nil_append] at h ⊢ hxLike
                rw [hxLike] at xisuncyclic

                have full_red : IsRed (FreeGroup.invRev K ++ I ++ K) := by
                  apply app_red_still_red (FreeGroup.invRev K) I K KinvRed hI hK h hIK NONEMPTY
                rw [equiv_of_reds] at full_red
                rw [full_red]
                nth_rewrite 2 [<- inv_of_inv K]
                rw [uncyc_on_conj, hxLike, xisuncyclic]

              | inr Jcontent =>
                  have triplet_red : IsRed ((FreeGroup.invRev K) ++ J ++ I) := by
                    apply app_red_still_red (FreeGroup.invRev K) J I KinvRed hJ hI KinvJRed JIRed_JRed.1 Jcontent
                  have full_red : IsRed ((FreeGroup.invRev K ++ J) ++ I ++ K) := by
                    apply app_red_still_red (FreeGroup.invRev K ++ J) I K KinvJRed hI hK triplet_red hIK NONEMPTY
                  rw [equiv_of_reds] at full_red
                  rw [full_red]
                  nth_rewrite 2 [<-inv_of_inv K, List.append_assoc,]
                  rw [uncyc_on_conj]
                  rw [hxLike] at CC ⊢
                  have cycreducedJI : cycreduced (J++I) := by exact uncyc_then_comm_lists₂ I J CC
                  unfold cycreduced at cycreducedJI
                  rw [cycreducedJI.2]
                  exact List.isRotated_append
            | inr NONEMPTY => -- J ≠ []
              have Icases : I = [] ∨ I ≠ [] := by exact eq_or_ne I []
              cases Icases with
              | inl Icontent =>

                sorry
              | inr Icontent =>
                sorry

            exact xisred'
            have htRed : IsRed (head :: tail) := by rw [h_g] at gRed; exact gRed
            have htinvRed : IsRed (FreeGroup.invRev (head :: tail)) := by exact inv_of_red (head :: tail) htRed
            exact htinvRed
        | inr h =>
          -- (x ++ t⁻¹ ++ [h]⁻¹) is reduced, what about the other?
          by_cases hh : IsRed (head :: tail ++ x.toWord)
          · -- both red, copy code from previous and paste.
            have htRed : IsRed (head :: tail) := by rw [h_g] at gRed; exact gRed
            have htinvRed : IsRed (FreeGroup.invRev (head :: tail)) := by exact inv_of_red (head :: tail) htRed
            have full_red: IsRed ((head :: tail) ++ x.toWord ++ FreeGroup.invRev (head :: tail)) := by apply app_red_still_red (head :: tail) (x.toWord) (FreeGroup.invRev (head :: tail)) htRed xisred' htinvRed hh h xcontent
            rw [equiv_of_reds] at full_red
            rw [full_red]
            rw [uncyc_on_conj]
            aesop
          · -- xt⁻¹h⁻¹ red but not htx, so...? technique on?
            -- apply technique, then inside take cases on x content. Need : sublist of red is red. cases on x and J
            apply technique at hh
            rcases hh with ⟨I, J, K, hI, hJ, jNE, hK, hIK, hHTLike, hxLike⟩

            -- here's how to get the inv of an append :
            have hHTinvLike : FreeGroup.invRev (head :: tail) = (FreeGroup.invRev J) ++ (FreeGroup.invRev I) := by
              have temp : FreeGroup.invRev (head :: tail) = FreeGroup.invRev (I ++ J) := by exact congrArg FreeGroup.invRev hHTLike
              rw [inv_of_app] at temp
              exact temp
            nth_rewrite 1 [hxLike, hHTinvLike, hHTLike]
            have convenience₁ : I ++ J ++ (FreeGroup.invRev J ++ K) ++ (FreeGroup.invRev J ++ FreeGroup.invRev I) = I ++ J ++ (FreeGroup.invRev J) ++ (K ++ FreeGroup.invRev J ++ FreeGroup.invRev I) := by simp
            rw [convenience₁]
            rw [distrib_reduce, FreeGroup.reduce_append_reduce_reduce, <-List.append_assoc, <-List.append_assoc]
            -- now remember h : IsRed (x.toWord ++ FreeGroup.invRev (head :: tail))
            rw [hHTLike, hxLike, inv_of_app, <- List.append_assoc] at h
            -- Now to deal with IKJ⁻¹I⁻¹, (using IsRed J⁻¹KJ⁻¹I⁻¹ → IsRed JI), we need one of J⁻¹ and K to be nonempty. We will club things accordingly.
            sorry
            have htRed : IsRed (head :: tail) := by rw [h_g] at gRed; exact gRed
            exact htRed
            exact xisred'


lemma prathamesh_lemma {α : Type*} [DecidableEq α] (r y g: List (α × Bool)) (hr : cycreduced r) (hy : cycreduced y) (hg : IsRed g) (hypo : r = FreeGroup.reduce (g ++ y ++ (FreeGroup.invRev g))) : r ~r y := by
  have cases₁ : IsRed (g ++ y) ∨ IsRed (y ++ (FreeGroup.invRev g)) := by apply uncyclicmid y g hy
  have cases_y : y = [] ∨ y ≠ [] := by exact eq_or_ne y []
  have cases_g : g = [] ∨ g ≠ [] := by exact eq_or_ne g []
  cases cases_y with
  | inl y_nil =>
    rw [y_nil, List.append_nil, cancel_inverses] at hypo
    simp [hypo, y_nil]
  | inr y_content =>
      cases cases_g with
      | inl g_nil =>
        simp [g_nil, List.nil_append] at hypo
        unfold cycreduced at hy; rw [equiv_of_reds] at hy
        rw [hy.1] at hypo
        aesop
      | inr g_content =>
        cases cases₁ with
        | inl IsRed_gy =>
          have yginvIsRed : IsRed (y ++ FreeGroup.invRev g) ∨ ¬ IsRed (y ++ FreeGroup.invRev g) := by exact Classical.em (IsRed (y ++ FreeGroup.invRev g))
          cases yginvIsRed with
          | inl h =>
            -- both combos reduced
            unfold cycreduced at hy hr
            sorry
          | inr h =>
            -- yg⁻¹ not reduced, apply technique
            sorry
        | inr IsRed_yginv =>
          have gyIsRed : IsRed (g ++ y) ∨ ¬ IsRed (g ++ y) := by exact Classical.em (IsRed (g ++ y))
          cases gyIsRed with
          | inl h =>
            -- both combos reduced, copy from above
            sorry
          | inr h =>
            -- gy not reduced, apply technique
            sorry


lemma Uncycleconj_is_reduced_cperm {α : Type*} [DecidableEq α] : ∀ (g y : FreeGroup α), Uncycle (g*y*g⁻¹).toWord ∈ List.map FreeGroup.reduce (y.toWord).cyclicPermutations := by
  intros g y
  rw [form_of_conj]
  simp
  let conju := FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord)
  let r := conju.head (by sorry)

  sorry


-- cycperm is a conj
-- uncyc is a conj
-- cycred is a conj
-- use cyclically reduced things. formalize cycreduced, reduced.

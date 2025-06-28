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







lemma form_of_conj {α : Type*} [DecidableEq α] (g y : FreeGroup α): (g*y*g⁻¹).toWord = FreeGroup.reduce (g.toWord ++ y.toWord ++ FreeGroup.invRev g.toWord) := by
    simp! [FreeGroup.toWord_mul]
    rw [<-List.append_assoc]
    nth_rewrite 3 [<-FreeGroup.reduce_toWord]
    rw [<-FreeGroup.reduce_invRev]
    rw [FreeGroup.reduce_append_reduce_reduce]



def cycreduced {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := (IsRed L) ∧ (Uncycle L = L)

lemma uncyclicmid {α : Type*} [DecidableEq α] (L₁ L₂ : List (α × Bool)) (h : cycreduced L₁) (h₂: IsRed L₂): (IsRed (L₂ ++ L₁)) ∨ (IsRed (L₁ ++ FreeGroup.invRev L₂)) := by sorry
-- needed

lemma technique {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧ (J ≠ []) ∧ (IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by sorry
#check FreeGroup.reduce_toWord
-- done


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


lemma isredsubl {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : IsRed (P ++ Q)) : (IsRed P) ∧ (IsRed Q) := by sorry
-- vivek has done



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
      sorry --( done easily by porting to vivek's inductive definition )

    | inr h =>
      simp [h, h₂] at ih
      have tail_is_the_player : ((head :: tail).getLast h₁) = (tail.getLast h) := by exact List.getLast_cons h
      rw [tail_is_the_player]
      intro hypo_last
      simp [hypo_last] at ih
      sorry -- ( done easily by porting to vivek's inductive definition )


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

lemma uncyc_then_comm_lists₁ {α : Type*} [DecidableEq α] (P : List (α × Bool)) : ∀ K, K~r P → cycreduced (P) → cycreduced (K) := by sorry

-- extremely important

lemma uncyc_then_comm_lists₂ {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : cycreduced (P ++ Q) → cycreduced (Q ++ P) := by
  have Pnil : P = [] ∨ P ≠ [] := by exact eq_or_ne P []
  have Qnil : Q = [] ∨ Q ≠ [] := by exact eq_or_ne Q []
  cases Pnil with
  | inl Pnil =>
    cases Qnil with
    | inl Qnil =>
      simp [Pnil]
    | inr Qcontent =>
      simp [Pnil]
  | inr Pcontent =>
    cases Qnil with
    | inl Qnil => simp [Qnil]
    | inr Qcontent =>
      intro hypo
      unfold cycreduced at hypo
      rcases hypo with ⟨IsRedPQ, uncyclicPQ⟩
      rw [<-uncycled_iff] at uncyclicPQ; simp [uncycled] at uncyclicPQ
      have QPRed : IsRed P ∧ IsRed Q := by exact isredsubl P Q IsRedPQ
      rcases QPRed with ⟨Pred,Qred⟩
      rw [join_red_iff_safe] at IsRedPQ
      unfold cycreduced
      have cond4join : (P.getLast Pcontent).1 ≠ (Q.head Qcontent).1 ∨ (P.getLast Pcontent).2 = (Q.head Qcontent).2 := by
        simp [IsRedPQ]
      have UncyclicQP : Uncycle (Q++P) = (Q++P) := by
        rw [<-uncycled_iff]
        simp [uncycled]
        split
        · simp
        · simp
        · expose_names
          simp
          have QPhd_x : ((Q ++ P).head (by simp [Qcontent])) = (x :: y :: ys).head (by simp) := by
            simp [heq]
          have QPhd_Qhd : ((Q ++ P).head (by simp [Qcontent])) = (Q.head (by simp [Qcontent])) := by exact List.head_append_left (of_eq_true (Eq.trans (congrArg Not (eq_false Qcontent)) not_false_eq_true))
          rw [List.head, QPhd_Qhd] at QPhd_x
          rw [<-QPhd_x]
          have mm₁ : (x :: y :: ys).getLast (by simp) = (Q ++ P).getLast (by simp [Pcontent]) := by simp [heq]
          have mm₂ : (x :: y :: ys).getLast (by simp) = (y :: ys).getLast (by simp) := by simp
          have mm₃ : (Q ++ P).getLast (by simp [Pcontent]) = P.getLast (by simp [Pcontent]) := by
            exact List.getLast_append_of_ne_nil
              (of_eq_true
                (Eq.trans
                  (congrArg Not
                    (Eq.trans List.append_eq_nil_iff._proof_1
                      (Eq.trans (congrArg (And (Q = [])) (eq_false Pcontent))
                        (and_false (Q = [])))))
                  not_false_eq_true))
              (of_eq_true (Eq.trans (congrArg Not (eq_false Pcontent)) not_false_eq_true))
          rw [mm₂, mm₃] at mm₁
          rw [mm₁]
          by_cases jj : (P.getLast Pcontent).1 ≠ (Q.head Qcontent).1 ∨ (P.getLast Pcontent).2 = (Q.head Qcontent).2
          · aesop
          · aesop
      constructor
      ·
        have formofPQ : ∃ x y : (α × Bool), ∃ ys : List (α × Bool), (P ++ Q) = x :: y :: ys := by
          use P.head Pcontent
          cases hh : P.tail with
          | nil =>
            use Q.head Qcontent
            use Q.tail
            have this₁ : P = (P.head (Pcontent):: P.tail) := by simp
            rw [hh] at this₁
            have this₂ : Q = (Q.head (Qcontent):: Q.tail) := by simp

            have this₃ : P ++ Q = [P.head Pcontent] ++ (Q.head Qcontent :: Q.tail) := by
              simp
              rw [<-List.singleton_append, <-this₁]
            rw [<-List.singleton_append, <-this₁]
            simp
          | cons head tail =>
            use (P.tail).head (by simp [hh])
            use (P.tail).tail ++ Q
            simp [hh]
            have this₁ : P.head Pcontent :: head :: (tail ++ Q) = (P.head Pcontent :: (head :: tail)) ++ Q := by simp
            rw [this₁, <-hh]
            simp
        rcases formofPQ with ⟨x,y,xs,property⟩
        simp [property] at uncyclicPQ
        have xisPhead : (x :: y :: xs).head (by simp) = (P ++ Q).head (by simp [Pcontent]) := by simp [property]
        rw [List.head] at xisPhead
        have m₁ : (P ++ Q).head (by simp [Pcontent]) = P.head Pcontent := by
          exact List.head_append_left Pcontent
        rw [m₁] at xisPhead
        sorry
      ·
        exact UncyclicQP
      exact Pred
      exact Qred




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

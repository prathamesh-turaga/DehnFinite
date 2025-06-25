import DehnFunction.Area1
import DehnFunction.Cyc_conj



-- STUFF FROM AREA2



def CycReduce {α : Type*} [DecidableEq α] (L : List (α × Bool)) : List (α × Bool) := Uncycle (FreeGroup.reduce L)
-- Takes a list and returns cyclic reduction of that list's freely-reduced form.




def IsRed {α : Type*} [DecidableEq α] (L : List (α × Bool)) : Prop := ∀ J : List (α × Bool), FreeGroup.Red L J → J = L

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

lemma uncyclicmid {α : Type*} [DecidableEq α] (L₁ L₂ : List (α × Bool)) (h : cycreduced L₁): (IsRed (L₂ ++ L₁)) ∨ (IsRed (L₁ ++ FreeGroup.invRev L₂)) := by sorry
-- needed

lemma technique {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h₁ : IsRed P) (h₂ : IsRed Q) : ¬IsRed (P ++ Q) → ∃ (I J K : List (α × Bool)), (IsRed I) ∧ (IsRed J) ∧(IsRed K) ∧ (IsRed (I++K)) ∧ (P = I ++ J)∧(Q = (FreeGroup.invRev J)++K) := by sorry
#check FreeGroup.reduce_toWord
-- extremely important

lemma app_red_still_red {α : Type*} [DecidableEq α] (P Q R : List (α × Bool)) (hp : IsRed P) (hq : IsRed Q) (hr : IsRed R) (h₁ : IsRed (P++Q)) (h₂ : IsRed (Q++R)) : (IsRed (P++Q++R)) := by sorry
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

lemma sublistisred {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (h : IsRed P): List.Sublist Q P →  IsRed Q := by sorry
-- omar has done

lemma red_at_join_nonempty_both {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) (hP : IsRed P) (hQ : IsRed Q) (h₁ : P ≠ []) (h₂ : Q ≠ []) : (P.getLast h₁).1 ≠ (Q.head h₂).1 ∨ (P.getLast h₁).2 = (Q.head h₂).2  → IsRed (P ++ Q) := by
  induction P generalizing Q with
  | nil =>
    by_contra
    aesop
  | cons head tail ih =>
    specialize ih Q
    have this₁ : (head :: tail) = [head]++tail := by simp!
    rw [this₁] at hP
    have tail_is_sublist : List.Sublist tail ([head] ++ tail) := by simp!
    have prelim : IsRed tail := by exact sublistisred ([head] ++ tail) tail hP tail_is_sublist
    simp [prelim, hQ] at ih
    have case_maker : tail = [] ∨ tail ≠ [] := by exact eq_or_ne tail []
    cases case_maker with
    | inl h =>
      rw [h] at hP; simp at hP
      simp [h]
      rw [equiv_of_reds]
      intros hypo₁
      sorry --( done easily by porting to vivek's inductive definition )

    | inr h =>
      simp [h, h₂] at ih
      have tail_is_the_player : ((head :: tail).getLast h₁) = (tail.getLast h) := by exact List.getLast_cons h
      rw [tail_is_the_player]
      intro hypo_last
      simp [hypo_last] at ih
      sorry -- ( done easily by porting to vivek's inductive definition )




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


lemma isredsubl {α : Type*} [DecidableEq α] (P Q : List (α × Bool)) : IsRed (P ++ Q) → (IsRed P) ∧ (IsRed Q) := by sorry
-- is done by vivek

lemma uncyc_red_isrotated_red_uncyc {α : Type*} [DecidableEq α] : ∀ (g x  : FreeGroup α), (xhypo : cycreduced x.toWord) → (Uncycle ((g*x*g⁻¹).toWord)) ~r (FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord))) := by
  intro g x
  rw [form_of_conj]
  let Lg := g.toWord
  let Lx := x.toWord
  have : g⁻¹.toWord = FreeGroup.invRev g.toWord := by exact FreeGroup.toWord_inv g
  have gRed : IsRed g.toWord := by apply (equiv_of_reds g.toWord).mpr; exact FreeGroup.reduce_toWord g

  have key : FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (x.toWord)) := by calc
    FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ g⁻¹.toWord)) = FreeGroup.reduce (Uncycle (g.toWord ++ x.toWord ++ FreeGroup.invRev g.toWord)) := by exact congrArg FreeGroup.reduce (congrArg Uncycle (congrArg (HAppend.hAppend (g.toWord ++ x.toWord)) this))
    _ = FreeGroup.reduce (Uncycle x.toWord) := by rw [uncyc_on_conj g.toWord x.toWord]

  rw [this]
  rw [uncyc_on_conj]
  cases h_g: g.toWord with
  | nil =>
      simp
      have this₁ : IsRed x.toWord := by simp [(equiv_of_reds x.toWord)]
      have this₂ : IsRed (Uncycle x.toWord) := by
        simp [uncyc_of_red_is_red x.toWord this₁]
      simp [equiv_of_reds x.toWord] at this₂
      have this₃ : FreeGroup.reduce (Uncycle x.toWord) = (Uncycle x.toWord) := by exact (equiv_of_reds (Uncycle x.toWord)).mp this₂
      rw [this₃]
      intro dd
      aesop
  | cons head tail =>
    intro CC'
    unfold cycreduced at CC'
    have CC : cycreduced x.toWord := by exact CC'
    rcases CC' with ⟨xisred, xisuncyclic⟩
    rw [xisuncyclic]
    apply (equiv_of_reds x.toWord).mp at xisred; simp only [xisred]
    have xisred' : IsRed x.toWord := by exact(equiv_of_reds x.toWord).mpr xisred
    have mylem : IsRed (head :: tail ++ x.toWord) ∨ IsRed (x.toWord ++ FreeGroup.invRev (head :: tail)) := by
      exact uncyclicmid x.toWord (head :: tail) CC
    cases mylem with
    | inl h =>
      by_cases h : IsRed (x.toWord ++ FreeGroup.invRev g.toWord)
      rw [h_g] at h
      rw [h_g] at gRed
      have htinvred : IsRed (FreeGroup.invRev (head :: tail)) := by
        apply (equiv_of_reds (FreeGroup.invRev (head :: tail))).mpr
        rw [FreeGroup.reduce_invRev]
        rw [equiv_of_reds] at gRed
        rw [gRed]
      · expose_names
        have this₁ : IsRed (head :: tail ++ x.toWord ++ FreeGroup.invRev (head :: tail)) := by exact app_red_still_red (head :: tail) x.toWord (FreeGroup.invRev (head :: tail)) gRed xisred' htinvred h_1 h
        rw [equiv_of_reds] at this₁
        rw [this₁]
        rw [uncyc_on_conj (head :: tail) x.toWord]
        rw [xisuncyclic]
      ·
        have htinvred : IsRed (FreeGroup.invRev (head :: tail)) := by
          apply (equiv_of_reds (FreeGroup.invRev (head :: tail))).mpr
          rw [FreeGroup.reduce_invRev]
          rw [equiv_of_reds] at gRed
          rw [h_g] at gRed; rw [gRed]
        apply technique at h
        rcases h with ⟨I, J, K, hI, hJ, hK, hIK, hPrior, hPost⟩
        rw [h_g] at hPost
        have hPost' : (head :: tail) = (FreeGroup.invRev K) ++ J := by
          calc
            (head :: tail) = FreeGroup.invRev (FreeGroup.invRev (head :: tail)) := by exact Eq.symm (inv_of_inv (head :: tail))
            _ = (FreeGroup.invRev (FreeGroup.invRev J ++ K)) := by rw [hPost]
            _ = (FreeGroup.invRev K) ++ FreeGroup.invRev (FreeGroup.invRev J) := by exact inv_of_app (FreeGroup.invRev J) K
            _ = (FreeGroup.invRev K) ++ J := by simp
        rw [hPost, hPost', hPrior]
        have convenience₁ : (FreeGroup.invRev K ++ J ++ (I ++ J) ++ (FreeGroup.invRev J ++ K)) = (FreeGroup.invRev K ++ J ++ I ++ J ++ (FreeGroup.invRev J) ++ K) := by simp
        rw [convenience₁]
        have convenience₂ : FreeGroup.reduce (FreeGroup.invRev K ++ J ++ I ++ J ++ (FreeGroup.invRev J) ++ K) = FreeGroup.reduce ((FreeGroup.invRev K ++ J ++ I) ++ J ++ (FreeGroup.invRev J) ++ K) := by simp
        have convenience₃ : FreeGroup.reduce ((FreeGroup.invRev K ++ J ++ I) ++ J ++ (FreeGroup.invRev J) ++ K) = FreeGroup.reduce (FreeGroup.reduce (FreeGroup.invRev K ++ J ++ I) ++ FreeGroup.reduce K) := by rw [distrib_reduce]
        rw [convenience₃]
        simp [inv_of_inv]; rw [FreeGroup.reduce_append_reduce_reduce]
        have mini_r₁ : IsRed (I++J) := by
          simp [hPrior] at xisred'; exact xisred'
        have mini_r₂ : Uncycle (I++J) = (I++J) := by simp [hPrior] at xisuncyclic; exact xisuncyclic
        have r₁ : cycreduced (I ++ J) := by unfold cycreduced; exact And.symm ⟨mini_r₂, mini_r₁⟩
        have r₂ : cycreduced (J ++ I) := by exact uncyc_then_comm_lists₂ I J r₁
        have mini_r₂ : IsRed (J ++ I) := by unfold cycreduced at r₂; exact r₂.1

        rw [<-List.append_assoc]
        have r₃ : IsRed ((FreeGroup.invRev K) ++ J) := by
          rw [h_g] at gRed
          rw [hPost'] at gRed; exact gRed
        have this₉: IsRed (FreeGroup.invRev K) := by
          apply (equiv_of_reds (FreeGroup.invRev K)).mpr
          rw [FreeGroup.reduce_invRev]; simp [equiv_of_reds] at hK; simp [hK]
        have mini_split : IsRed (FreeGroup.invRev K ++ J ++ I) := by
          apply app_red_still_red (FreeGroup.invRev K) J I this₉ hJ hI r₃ mini_r₂
        have split_trio : IsRed (FreeGroup.invRev K ++ J ++ I ++ K) := by
          apply app_red_still_red ((FreeGroup.invRev K) ++ J) I K r₃ hI hK mini_split hIK
        rw [equiv_of_reds] at split_trio
        rw [split_trio]
        have k_is_k_inv_inv : K = FreeGroup.invRev (FreeGroup.invRev K) := by exact Eq.symm (inv_of_inv K)
        nth_rewrite 2 [k_is_k_inv_inv]
        have conditions_to_apply :  (FreeGroup.invRev K ++ J ++ I ++ FreeGroup.invRev (FreeGroup.invRev K)) =  (FreeGroup.invRev K ++ (J ++ I) ++ FreeGroup.invRev (FreeGroup.invRev K)) := by simp
        rw [conditions_to_apply]
        rw [uncyc_on_conj (FreeGroup.invRev K) (J ++ I)]
        unfold cycreduced at r₂
        rw [r₂.2]
        exact List.isRotated_append
        exact xisred'
        simp [h_g]; exact htinvred
    | inr h =>
      by_cases h : IsRed (g.toWord ++ x.toWord)
      rw [h_g] at h
      rw [h_g] at gRed
      have htinvred : IsRed (FreeGroup.invRev (head :: tail)) := by
        apply (equiv_of_reds (FreeGroup.invRev (head :: tail))).mpr
        rw [FreeGroup.reduce_invRev]
        rw [equiv_of_reds] at gRed
        rw [gRed]
      ·
        expose_names
        have this₁ : IsRed (head :: tail ++ x.toWord ++ FreeGroup.invRev (head :: tail)) := by exact app_red_still_red (head :: tail) x.toWord (FreeGroup.invRev (head :: tail)) gRed xisred' htinvred h h_1
        rw [equiv_of_reds] at this₁
        rw [this₁]
        rw [uncyc_on_conj (head :: tail) x.toWord]
        rw [xisuncyclic]
      ·
        have htinvred : IsRed (FreeGroup.invRev (head :: tail)) := by
          apply (equiv_of_reds (FreeGroup.invRev (head :: tail))).mpr
          rw [FreeGroup.reduce_invRev]
          rw [equiv_of_reds] at gRed
          rw [h_g] at gRed; rw [gRed]
        apply technique at h
        rcases h with ⟨I, J, K, hI, hJ, hK, hIK, hPrior, hPost⟩
        rw [h_g] at hPrior
        have hPrior' : FreeGroup.invRev (head :: tail) = (FreeGroup.invRev J) ++ FreeGroup.invRev (I) := by
          calc
            FreeGroup.invRev (head :: tail) = FreeGroup.invRev (I ++ J) := by exact congrArg FreeGroup.invRev hPrior
            _ = FreeGroup.invRev (J) ++ FreeGroup.invRev (I) := by exact inv_of_app I J

        nth_rewrite 1 [hPrior, hPrior', hPost]

        have convenience₁ : (I ++ J ++ (FreeGroup.invRev J ++ K) ++ (FreeGroup.invRev J ++ FreeGroup.invRev I)) = (I ++ J ++ (FreeGroup.invRev J) ++ (K ++ FreeGroup.invRev J ++ FreeGroup.invRev I)) := by simp
        rw [convenience₁]
        rw [distrib_reduce]
        simp [FreeGroup.reduce_append_reduce_reduce]
        rw [hPrior] at htinvred
        rw [inv_of_app] at htinvred
        rw [hPost] at xisred xisred' xisuncyclic CC ⊢
        apply uncyc_then_comm_lists₂ at CC
        unfold cycreduced at CC
        have JinvIsRed : IsRed (FreeGroup.invRev J) := by
          rw [equiv_of_reds] at hJ ⊢
          rw [FreeGroup.reduce_invRev]
          rw [hJ]
        have isred_first_three : IsRed (I ++ K ++ FreeGroup.invRev J) := by apply app_red_still_red I K (FreeGroup.invRev J) hI hK JinvIsRed hIK CC.1
        have convenience₂ : (I ++ (K ++ (FreeGroup.invRev J ++ FreeGroup.invRev I))) = ((I ++ K ++ FreeGroup.invRev J) ++ FreeGroup.invRev I) := by simp
        rw [convenience₂]
        have IinvIsRed : IsRed (FreeGroup.invRev I) := by
          rw [equiv_of_reds] at hI ⊢
          rw [FreeGroup.reduce_invRev]
          rw [hI]
        have mamma_mia : IsRed (I ++ K ++ (FreeGroup.invRev J) ++ (FreeGroup.invRev I)) := by apply app_red_still_red (I ++ K) (FreeGroup.invRev J) (FreeGroup.invRev I) hIK JinvIsRed IinvIsRed isred_first_three htinvred
        rw [equiv_of_reds] at mamma_mia
        rw [mamma_mia]

        have convenience₃ : (I ++ K ++ FreeGroup.invRev J ++ FreeGroup.invRev I) = (I ++ (K ++ FreeGroup.invRev J) ++ FreeGroup.invRev I) := by simp
        rw [convenience₃]
        rw [uncyc_on_conj I (K ++ FreeGroup.invRev J)]
        rw [CC.2]
        exact List.isRotated_append
        exact gRed
        exact xisred'

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

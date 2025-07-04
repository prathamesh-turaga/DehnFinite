import DehnFunction.IsRed

variable {α G : Type} [DecidableEq α] [Group G] [DecidableEq G]

/--
For every g in l, this checks for cancellations in `a*g` or `a*g⁻¹`, and accordingly adds them when there are no such cancellations
-/
def letter_mul_after_check_cancel (a : α) (l : List (FreeGroup α)) : List (FreeGroup α) :=
  match l with
  | [] => []
  | g::gs =>
    if hg : g=1 then [(.of a),(.of a)⁻¹]++(letter_mul_after_check_cancel a gs)
    else if g.toWord.head (by contrapose! hg; exact FreeGroup.toWord_eq_nil_iff.mp hg) = (a,true) then (.of a)*g::(letter_mul_after_check_cancel a gs)
    else if g.toWord.head (by contrapose! hg; exact FreeGroup.toWord_eq_nil_iff.mp hg) = (a,false) then (.of a)⁻¹*g::(letter_mul_after_check_cancel a gs)
    else [(.of a)*g,(.of a)⁻¹*g]++(letter_mul_after_check_cancel a gs)

lemma IsRed.toWord (g : FreeGroup α) : IsRed g.toWord := by
  rw [IsRed.iff_reduce_self]
  exact FreeGroup.reduce_toWord g

lemma mul_toWord_noCancel1 (a : α) {g : FreeGroup α} (hg1 : g≠1) (hg2 : g.toWord.head (by contrapose! hg1; exact FreeGroup.toWord_eq_nil_iff.mp hg1) ≠ (a,false)) :
  ((.of a)*g).toWord = (a,true)::g.toWord := by
  simp [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.cons_append,-FreeGroup.reduce.cons]
  rw [← IsRed.iff_reduce_self,IsRed.cons_iff_not_red_pair]
  constructor
  · exact IsRed.toWord g
  · simp at hg2
    rw [Prod.ext_iff,not_and_or] at hg2
    simp at hg2 ⊢
    tauto

lemma mul_toWord_noCancel2 (a : α) {g : FreeGroup α} (hg1 : g≠1) (hg2 : g.toWord.head (by contrapose! hg1; exact FreeGroup.toWord_eq_nil_iff.mp hg1) ≠ (a,true)) :
  ((.of a)⁻¹*g).toWord = (a,false)::g.toWord := by
  simp [FreeGroup.toWord_mul,FreeGroup.invRev,FreeGroup.toWord_of,List.cons_append,-FreeGroup.reduce.cons]
  rw [← IsRed.iff_reduce_self,IsRed.cons_iff_not_red_pair]
  constructor
  · exact IsRed.toWord g
  · simp at hg2
    rw [Prod.ext_iff,not_and_or] at hg2
    simp at hg2 ⊢
    tauto

/--
If every element of `l` has norm `k`, every element of `letter_mul_after_check_cancel a l` will have norm `k+1`
-/
theorem letter_mul_after_check_cancel_elt_norm (a : α) {l : List (FreeGroup α)} (k : ℕ) (hl : ∀ g ∈ l, g.norm = k) : ∀ g ∈ letter_mul_after_check_cancel a l, g.norm = k+1 := by
  intro g hg
  induction l with
  | nil => simp [letter_mul_after_check_cancel] at hg
  | cons h hs ih =>
    simp [letter_mul_after_check_cancel] at hl hg
    split_ifs at hg with h1 h2 h3
    · simp at hg
      simp [h1] at hl
      rcases hg with hg|hg|hg
      · rw [← hl.1]
        simp [hg]
      · rw [← hl.1]
        simp [hg]
      · exact ih hl.2 hg
    · simp at hg
      rcases hg with hg|hg
      · rw [hg] at *
        have h3 := mul_toWord_noCancel1 a h1 (by simp [h2])
        simp [FreeGroup.norm,h3,← hl.1]
      · exact ih hl.2 hg
    · simp at hg
      rcases hg with hg|hg
      · rw [hg] at *
        have h4 := mul_toWord_noCancel2 a h1 h2
        simp [FreeGroup.norm,h4,← hl.1]
      · exact ih hl.2 hg
    · simp at hg
      rcases hg with hg|hg|hg
      · rw [hg] at *
        have h4 := mul_toWord_noCancel1 a h1 h3
        simp [FreeGroup.norm,h4,← hl.1]
      · rw [hg] at *
        have h4 := mul_toWord_noCancel2 a h1 h2
        simp [FreeGroup.norm,h4,← hl.1]
      · exact ih hl.2 hg

/--
List of all the elements of `FreeGroup α` of norm k.

(A = alphabet written as a list)
-/
def FreeGroup.elts_norm_k (A : List α) (hA : A ≠ []) (k : ℕ) : List (FreeGroup α) :=
  match k with
  | 0 => [1]
  | p+1 => (List.map (fun a => letter_mul_after_check_cancel a (elts_norm_k A hA p)) A).flatten

/--
List of all the elements of `FreeGroup α` of norm 0 to k.

(A = alphabet written as a list)
-/
def FreeGroup.elts_upto_norm_k (A : List α) (hA : A ≠ []) (k : ℕ) : List (FreeGroup α) :=
  match k with
  | 0 => [1]
  | p+1 => (elts_upto_norm_k A hA p)++(elts_norm_k A hA (p+1))

-- Should I define elts_norm_k and append from 1 to k?
--which defn better?

theorem FreeGroup.elts_norm_k_correct1 (A : List α) (hA : A ≠ []) (k : ℕ) (g : FreeGroup α) (hg : g ∈ elts_norm_k A hA k) : g.norm = k := by
  induction k generalizing g with
  | zero =>
    simp [elts_norm_k] at hg
    exact norm_eq_zero.mpr hg
  | succ p ih =>
    cases A with
    | nil => contradiction
    | cons a as =>
      simp [elts_norm_k] at hg
      rcases hg with hg|hg
      · exact letter_mul_after_check_cancel_elt_norm a p ih g hg
      · rcases hg with ⟨b,hbas,hgb⟩
        exact letter_mul_after_check_cancel_elt_norm b p ih g hgb

lemma FreeGroup.norm_eq_one (g : FreeGroup α) (hg : g.norm = 1) : ∃ a : α, g.toWord = [(a,true)] ∨ g.toWord = [(a,false)] := by
  rw [norm] at hg
  generalize g.toWord = l at *
  match l with
  | [x] =>
    use x.1
    aesop

lemma FreeGroup.norm_succ (g : FreeGroup α) (n : ℕ) (hg : g.norm = n+1) :
  ∃ (a : α) (h : FreeGroup α), h.norm = n ∧ (g.toWord = (a,true)::h.toWord ∨ g.toWord = (a,false)::h.toWord) := by
  rw [norm] at hg
  generalize hl : g.toWord = l at *
  induction l generalizing g n with
  | nil => contradiction
  | cons x xs ih =>
    cases n with
    | zero =>
      simp at hg
      simp [hg] at hl ⊢
      have h1 : g.norm = 1 := by simp [norm,hl]
      apply norm_eq_one at h1
      rcases h1 with ⟨a,ha⟩
      use a
      rw [hl] at ha
      simp at ha
      tauto
    | succ n =>
      use x.1
      use (mk xs)
      have h1 := IsRed.toWord g
      rw [hl] at h1
      have h2 := IsRed.tail _ h1
      rw [IsRed.iff_reduce_self] at h2
      specialize ih (mk xs) n
      rw [toWord_mk] at ih
      simp at hg
      rw [norm,toWord_mk,h2]
      simp [hg]
      aesop

lemma letter_mul_after_check_cancel_mem (a : α) (g h : FreeGroup α) (l : List (FreeGroup α)) (hh : h ∈ l) (hg : g.toWord = (a,true)::h.toWord) :
  g ∈ letter_mul_after_check_cancel a l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp at hh
    rcases hh with hh|hh
    · simp [← hh,letter_mul_after_check_cancel]
      split_ifs with h1 h2 h3
      · simp [h1] at hg
        simp
        left
        exact FreeGroup.toWord_inj.mp hg
      · simp
        left
        rw [← FreeGroup.toWord_inj]
        rwa [mul_toWord_noCancel1 a h1 (by simp [h2])]
      · simp
        have h4 := IsRed.toWord g
        rw [hg] at h4
        rw [IsRed.cons_iff_not_red_pair] at h4
        simp [h3] at h4
        clear h2 h3
        contrapose! h1
        exact FreeGroup.toWord_eq_nil_iff.mp h1
      · simp
        left
        rw [← FreeGroup.toWord_inj]
        rwa [mul_toWord_noCancel1 a h1 h3]
    · simp [letter_mul_after_check_cancel]
      split_ifs with h1 h2 h3 <;> simp [ih hh]

lemma letter_mul_after_check_cancel_mem' (a : α) (g h : FreeGroup α) (l : List (FreeGroup α)) (hh : h ∈ l) (hg : g.toWord = (a,false)::h.toWord) :
  g ∈ letter_mul_after_check_cancel a l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp at hh
    rcases hh with hh|hh
    · simp [← hh,letter_mul_after_check_cancel]
      split_ifs with h1 h2 h3
      · simp [h1] at hg
        simp
        right
        left
        exact FreeGroup.toWord_inj.mp hg
      · simp
        have h4 := IsRed.toWord g
        rw [hg] at h4
        rw [IsRed.cons_iff_not_red_pair] at h4
        simp [h2] at h4
        clear h2
        contrapose! h1
        exact FreeGroup.toWord_eq_nil_iff.mp h1
      · simp
        left
        rw [← FreeGroup.toWord_inj]
        rwa [mul_toWord_noCancel2 a h1 h2]
      · simp
        right
        left
        rw [← FreeGroup.toWord_inj]
        rwa [mul_toWord_noCancel2 a h1 h2]
    · simp [letter_mul_after_check_cancel]
      split_ifs with h1 h2 h3 <;> simp [ih hh]

-- assume there exists a computable choice function
theorem FreeGroup.elts_norm_k_correct2 (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (k : ℕ) (g : FreeGroup α) (hg : g.norm = k) : g ∈ elts_norm_k A hAe k := by
  induction k generalizing g with
  | zero =>
    simp [elts_norm_k]
    exact norm_eq_zero.mp hg
  | succ p ih =>
    apply norm_succ at hg
    rcases hg with ⟨a,h,hh,ha⟩
    have h1 := ih h hh
    simp [elts_norm_k]
    specialize hA a
    use a
    use hA
    simp [elts_norm_k] at h1
    rcases ha with ha|ha
    · exact letter_mul_after_check_cancel_mem a g h (elts_norm_k A hAe p) (ih h hh) ha
    · exact letter_mul_after_check_cancel_mem' a g h (elts_norm_k A hAe p) (ih h hh) ha

/--
Proof that `elts_norm_k` contains exactly the elements of `FreeGroup α` of norm k.

(A = alphabet written as a list, hA = proof of that)
-/
theorem FreeGroup.elts_norm_k_correct (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (g : FreeGroup α) (k : ℕ) : g ∈ elts_norm_k A hAe k ↔ g.norm = k :=
  ⟨fun h ↦ elts_norm_k_correct1 A hAe k g h,fun h ↦ elts_norm_k_correct2 A hA hAe k g h⟩

theorem FreeGroup.elts_upto_norm_k_correct (A : List α) (hAe : A ≠ []) (k : ℕ) : elts_upto_norm_k A hAe k = (List.ofFn (fun (i:Fin (k+1)) => elts_norm_k A hAe i)).flatten := by
  induction k with
  | zero =>
    simp [elts_upto_norm_k,elts_norm_k]
  | succ n ih =>
    simp only [elts_upto_norm_k,ih]
    have h1 : elts_norm_k A hAe (n + 1) = (List.ofFn (fun (i : Fin 1) => elts_norm_k A hAe (n+1+i))).flatten := by simp
    rw [h1,← List.flatten_append,← List.ofFn_fin_append]
    congr
    simp
    rw [Fin.append_right_eq_snoc]
    ext i : 1
    cases i using Fin.lastCases with
    | last => simp
    | cast i => simp

/--
Proof that `elts_upto_norm_k` contains exactly the elements of `FreeGroup α` upto norm k.

(A = alphabet written as a list, hA = proof of that)
-/
theorem FreeGroup.set_of_words_norm_le_k_eq (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (k : ℕ) : {g : FreeGroup α | FreeGroup.norm g ≤ k} = {x | x ∈ elts_upto_norm_k A hAe k} := by
  induction k with
  | zero =>
    simp [elts_upto_norm_k]
  | succ n ih =>
    ext g
    constructor
    · simp
      intro hg
      rw [Nat.le_succ_iff] at hg
      rcases hg with hg|hg
      · rw [Set.ext_iff] at ih
        simp at ih
        specialize ih g
        rw [ih] at hg
        simp [elts_upto_norm_k,hg]
      · simp [elts_upto_norm_k]
        right
        exact elts_norm_k_correct2 A hA hAe (n + 1) g hg
    · simp
      intro hg
      rw [Set.ext_iff] at ih
      simp at ih
      specialize ih g
      simp [elts_upto_norm_k] at hg
      rcases hg with hg|hg
      · rw [← ih] at hg
        exact Nat.le_add_right_of_le hg
      · rw [elts_norm_k_correct] at hg
        exact Nat.le_of_eq hg
        exact hA

/--
Given [r₁,...,rₙ] and [u₁,...,uₙ], it produces [u₁*r₁*u₁⁻¹,...,uₙ*rₙ*uₙ⁻¹]
-/
def lists_conjugate (rlist ulist : List G) : List G :=
  match rlist,ulist with
  | [],[] => []
  | r::rs,[] => r::rs
  | [],_::_ => []
  | r::rs,u::us => u*r*u⁻¹::(lists_conjugate rs us)

inductive typ |a |b |c deriving DecidableEq, Repr

-- def alph := [typ.a,.b]
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5))
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5)).length
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5)).Nodup

-- def alph1 := [typ.a,.b,.c]
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k alph1 (by decide) 6)).length

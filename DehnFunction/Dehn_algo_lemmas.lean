import DehnFunction.IsRed

variable {α G : Type} [DecidableEq α] [Group G] [DecidableEq G]

namespace FreeGroup

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
  rw [IsRed.equiv_of_reds]
  exact FreeGroup.reduce_toWord g

lemma mul_toWord_noCancel1 (a : α) {g : FreeGroup α} (hg1 : g≠1) (hg2 : g.toWord.head (by contrapose! hg1; exact FreeGroup.toWord_eq_nil_iff.mp hg1) ≠ (a,false)) :
  ((.of a)*g).toWord = (a,true)::g.toWord := by
  simp [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.cons_append,-FreeGroup.reduce.cons]
  rw [← IsRed.equiv_of_reds,IsRed.cons_iff_not_red_pair]
  constructor
  · exact IsRed.toWord g
  · simp at hg2
    rw [Prod.ext_iff,not_and_or] at hg2
    simp at hg2 ⊢
    tauto

lemma mul_toWord_noCancel2 (a : α) {g : FreeGroup α} (hg1 : g≠1) (hg2 : g.toWord.head (by contrapose! hg1; exact FreeGroup.toWord_eq_nil_iff.mp hg1) ≠ (a,true)) :
  ((.of a)⁻¹*g).toWord = (a,false)::g.toWord := by
  simp [FreeGroup.toWord_mul,FreeGroup.invRev,FreeGroup.toWord_of,List.cons_append,-FreeGroup.reduce.cons]
  rw [← IsRed.equiv_of_reds,IsRed.cons_iff_not_red_pair]
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
def elts_norm_k (A : List α) (hA : A ≠ []) (k : ℕ) : List (FreeGroup α) :=
  match k with
  | 0 => [1]
  | p+1 => (List.map (fun a => letter_mul_after_check_cancel a (elts_norm_k A hA p)) A).flatten

/--
List of all the elements of `FreeGroup α` of norm 0 to k.

(A = alphabet written as a list)
-/
def elts_upto_norm_k (A : List α) (hA : A ≠ []) (k : ℕ) : List (FreeGroup α) :=
  match k with
  | 0 => [1]
  | p+1 => (elts_upto_norm_k A hA p)++(elts_norm_k A hA (p+1))

theorem elts_norm_k_correct1 (A : List α) (hA : A ≠ []) (k : ℕ) (g : FreeGroup α) (hg : g ∈ elts_norm_k A hA k) : g.norm = k := by
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

lemma norm_eq_one (g : FreeGroup α) (hg : g.norm = 1) : ∃ a : α, g.toWord = [(a,true)] ∨ g.toWord = [(a,false)] := by
  rw [norm] at hg
  generalize g.toWord = l at *
  match l with
  | [x] =>
    use x.1
    aesop

lemma norm_succ (g : FreeGroup α) (n : ℕ) (hg : g.norm = n+1) :
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
      rw [IsRed.equiv_of_reds] at h2
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

-- assume alphabet can be written as a list
theorem elts_norm_k_correct2 (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (k : ℕ) (g : FreeGroup α) (hg : g.norm = k) : g ∈ elts_norm_k A hAe k := by
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
theorem elts_norm_k_correct (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (g : FreeGroup α) (k : ℕ) : g ∈ elts_norm_k A hAe k ↔ g.norm = k :=
  ⟨fun h ↦ elts_norm_k_correct1 A hAe k g h,fun h ↦ elts_norm_k_correct2 A hA hAe k g h⟩

theorem elts_upto_norm_k_correct (A : List α) (hAe : A ≠ []) (k : ℕ) : elts_upto_norm_k A hAe k = (List.ofFn (fun (i:Fin (k+1)) => elts_norm_k A hAe i)).flatten := by
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
theorem set_of_words_norm_le_k_eq (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (k : ℕ) : {g : FreeGroup α | FreeGroup.norm g ≤ k} = {x | x ∈ elts_upto_norm_k A hAe k} := by
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

theorem elts_upto_norm_k_correct' (A : List α) (hA : ∀ a : α, a ∈ A) (hAe : A ≠ []) (k : ℕ) (x : FreeGroup α) : x ∈ elts_upto_norm_k A hAe k ↔ x.norm ≤ k := by
  change x ∈ {x | x ∈ elts_upto_norm_k A hAe k} ↔ x.norm ≤ k
  rw [← set_of_words_norm_le_k_eq]
  simp
  exact hA

end FreeGroup

/--
Given a list A, generates lists of size n out of the elements of A
-/
def lists_of_size_n (A : List α) (n : ℕ) : List (List α) :=
  match n with
  | 0 => [[]]
  | k+1 => (List.map (fun a => (List.map (fun l => a::l)) (lists_of_size_n A k)) A).flatten

-- #eval lists_of_size_n [1,2] 3

#eval lists_of_size_n [1,2,3] 2
omit [DecidableEq α] in
/--
The lists in `lists_of_size_n` are of size n
-/
lemma lists_of_size_n_size_eq_n (A : List α) (n : ℕ) : ∀ l ∈ lists_of_size_n A n, l.length = n := by
  induction n with
  | zero => simp [lists_of_size_n]
  | succ k ih =>
    intro l hl
    simp [lists_of_size_n] at hl
    rcases hl with ⟨a,ha,as,has1,has2⟩
    specialize ih as has1
    simpa [← has2]
#check List.map

omit [DecidableEq α] in
/--
The elements of the lists in `lists_of_size_n` lie in the original list
-/
lemma lists_of_size_n_elt_original (A : List α) (n : ℕ) (l : List α) (hl : l ∈ lists_of_size_n A n) : ∀ e ∈ l, e ∈ A := by
  induction n generalizing l with
  | zero => simp [lists_of_size_n] at hl; simp [hl]
  | succ k ih =>
    simp [lists_of_size_n] at hl
    rcases hl with ⟨b,hb,bs,hb1,hb2⟩
    specialize ih bs hb1
    simp [← hb2]
    exact ⟨hb,ih⟩

omit [DecidableEq α] in
/--
If l is a list of size n containing only elements from A, it lies in `lists_of_size_n A n`
-/
lemma lists_of_size_n_elt_if (A : List α) (n : ℕ) (l : List α) (hl1 : l.length = n) (hl2 : ∀ e ∈ l, e ∈ A) : l ∈ lists_of_size_n A n := by
  induction l generalizing n with
  | nil =>
    simp at hl1
    simp [← hl1,lists_of_size_n]
  | cons x xs ih =>
    simp at hl1 hl2
    simp [← hl1,lists_of_size_n]
    specialize ih (n-1) (by rw [← hl1]; norm_num) hl2.2
    constructor
    · exact hl2.1
    · convert ih
      rw [← hl1]
      norm_num

-- /--
-- Given [r₁,...,rₙ] and [u₁,...,uₙ], it produces [u₁*r₁*u₁⁻¹,...,u₁*rₙ*u₁⁻¹,...,uₙ*r₁*uₙ⁻¹,...,uₙ*rₙ*uₙ⁻¹]
-- -/
-- def lists_conjugate (rlist ulist : List G) : List G :=
--   (List.map (fun r => (List.map (fun u => u*r*u⁻¹) ulist)) rlist).flatten

inductive typ |a |b |c deriving DecidableEq, Repr

def alph := [typ.a,.b]
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5))
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5)).length
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k ([typ.a,.b]) (by decide) 5)).Nodup

-- def alph1 := [typ.a,.b,.c]
-- #eval (List.map FreeGroup.toWord (FreeGroup.elts_upto_norm_k alph1 (by decide) 6)).length
-- #eval List.map FreeGroup.toWord (lists_conjugate [(FreeGroup.of typ.a)*(.of .b)*(.of .a)⁻¹*(.of .b)⁻¹,(.of .b)] [(FreeGroup.of typ.a),(.of .a)⁻¹])

/--
Given [r₁,...,rₙ] and [u₁,...,uₙ], it produces [u₁*r₁*u₁⁻¹,u₂*r₂*u₂⁻¹,...,uₙ*rₙ*uₙ⁻¹]
-/
def produce_conjugated_term (rlist ulist : List G) : G :=
  List.prod (aux rlist ulist) where
  aux (rlist ulist : List G) :=
    match rlist,ulist with
    | l,[] => l
    | [],_::_ => []
    | r::rs,u::us => (u*r*u⁻¹)::(aux rs us)
#eval (List.foldr max 5 [])

namespace FreeGroup

#check List.sublistsLen
-- #eval List.sublistsLen 3 [1,2]
def output_list_aux (rlist ulist : List (FreeGroup α)) (n : ℕ) : List (FreeGroup α) :=
  let l1 := lists_of_size_n rlist n
  let l2 := lists_of_size_n ulist n
  (List.map (fun rs => (List.map (fun us => produce_conjugated_term rs us)) l2) l1).flatten

/--Gives the maximum norm of all the elements in the list-/
def list_max_norm (l : List (FreeGroup α)) : ℕ := List.foldr max 0 (List.map FreeGroup.norm l)

/--The output list for the Dehn algorithm-/
def output_list (rlist : List (FreeGroup α)) (dehn_bound : ℕ → ℕ) (n : ℕ) (A : List α) (hAe : A ≠ []) : List (FreeGroup α) :=
  output_list_aux (rlist++(List.map (fun x => x⁻¹) rlist)) (elts_upto_norm_k A hAe (n + (list_max_norm rlist)*(dehn_bound n))) (dehn_bound n)

def rels := [(FreeGroup.of typ.a)*(.of .b)]
-- #eval list_max_norm [(FreeGroup.of typ.a)*(.of .b)]
-- #eval FreeGroup.toWord ((lists_conjugate rels (elts_upto_norm_k alph (by decide) 3))).prod
-- #eval List.map (fun l => List.map FreeGroup.toWord l) (lists_of_size_n rels 2)
-- #eval (List.map FreeGroup.toWord (output_list [(FreeGroup.of typ.a)*(.of .b)] id 2 alph (by decide))).length

-- rlist need not be relators here
/--The output list of the Dehn algorithm is a list of the relators and their inverses conjugated by elements upto a certain norm-/
lemma output_list_correct (rlist : List (FreeGroup α)) (dehn_bound : ℕ → ℕ) (n : ℕ) (A : List α) (hAe : A ≠ []) (hA : ∀ a : α, a ∈ A) (g : FreeGroup α) :
  g ∈ output_list rlist dehn_bound n A hAe
  ↔ ∃ rs us,
  g = (produce_conjugated_term rs us)
  ∧ rs.length = (dehn_bound n)
  ∧ (∀ r ∈ rs, r ∈ rlist ++ (List.map (fun x => x⁻¹) rlist))
  ∧ us.length = (dehn_bound n)
  ∧ (∀ u ∈ us, u.norm ≤ (n + (list_max_norm rlist)*(dehn_bound n))) := by
  constructor
  · intro h
    simp [output_list,output_list_aux] at h
    rcases h with ⟨rs,hrs,us,hus,hg⟩
    use rs
    use us
    simp [hg,lists_of_size_n_size_eq_n _ _ _ hrs,lists_of_size_n_size_eq_n _ _ _ hus,-List.mem_append]
    constructor
    · exact fun r a ↦ lists_of_size_n_elt_original _ (dehn_bound n) rs hrs r a
    · apply lists_of_size_n_elt_original at hus
      intro u hu
      specialize hus u hu
      rwa [elts_upto_norm_k_correct'] at hus
      exact hA
  · intro ⟨rs,us,hg,hrs1,hrs2,hus1,hus2⟩
    simp [output_list,output_list_aux]
    use rs
    use lists_of_size_n_elt_if _ (dehn_bound n) rs hrs1 hrs2
    use us
    constructor
    · apply lists_of_size_n_elt_if _ _ _ hus1
      intro u hu
      rw [elts_upto_norm_k_correct']
      exact hus2 u hu
      exact hA
    · exact (Eq.symm hg)

-- rlist needs to be list of relators here
theorem word_in_reqd_list_aux (rlist : List (FreeGroup α)) (n : ℕ) (dehn_bound : ℕ → ℕ) (w : FreeGroup α) (hw : IsProductOfNConjugates {R | R ∈ rlist} (dehn_bound n) w) :
  ∃ rs us,
    w = (produce_conjugated_term rs us)
    ∧ rs.length = (dehn_bound n)
    ∧ (∀ r ∈ rs, r ∈ (rlist) ++ (List.map (fun x => x⁻¹) rlist))
    ∧ us.length = (dehn_bound n)
    ∧ (∀ u ∈ us, u.norm ≤ (n + (list_max_norm rlist)*(dehn_bound n))) := by sorry

-- w is identity in place of prod n conj
theorem word_in_reqd_list (rlist : List (FreeGroup α)) (n : ℕ) (dehn_bound : ℕ → ℕ) (w : FreeGroup α) (hw : IsProductOfNConjugates {R | R ∈ rlist} (dehn_bound n) w) (A : List α) (hAe : A ≠ []) (hA : ∀ a : α, a ∈ A) :
  w ∈ output_list rlist dehn_bound n A hAe :=
  (output_list_correct rlist dehn_bound n A hAe hA w).mpr (word_in_reqd_list_aux rlist n dehn_bound w hw)

--if w=1 it is in output list (decidable dehn bound)

end FreeGroup

module

public import PaperVerification.AlternatingFormsWeightAlgebraic

/-!
# The dimension of the actual interval Plücker quotient

The lower bound uses the right-to-left saturated interval chain. Its normalized
diagonal exponents form a triangular integral matrix: each nonpivot coordinate
has coefficient one on its own chain member and can occur additionally only
in members with an earlier row. This proves algebraic independence over the
original field. Together with the normalized-band embedding it gives the exact
Krull dimension in Lemma 2.2.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

def intervalPathColumn (α β : Fin s → Fin n) :
    NormalizedBandVariable α β → Fin s → Fin n
  | none => α
  | some a => fun i => if i<a.1 then α i else if i=a.1 then a.2.val else β i

theorem intervalPathColumn_mem (α β : Fin s → Fin n) (hab : ∀ i, α i ≤ β i)
    (x : NormalizedBandVariable α β) (i : Fin s) :
    α i ≤ intervalPathColumn α β x i ∧ intervalPathColumn α β x i ≤ β i := by
  cases x with
  | none => exact ⟨le_rfl,hab i⟩
  | some a =>
    simp only [intervalPathColumn]
    split_ifs with hia hie
    · exact ⟨le_rfl,hab i⟩
    · subst i
      exact ⟨a.2.property.1.le,a.2.property.2⟩
    · exact ⟨hab i,le_rfl⟩

theorem intervalPathColumn_strictMono (α β : Fin s → Fin n)
    (hα : StrictMono α) (hβ : StrictMono β) (hab : ∀ i, α i ≤ β i)
    (x : NormalizedBandVariable α β) : StrictMono (intervalPathColumn α β x) := by
  cases x with
  | none => exact hα
  | some a =>
    intro i j hij
    change (if i<a.1 then α i else if i=a.1 then a.2.val else β i) <
      (if j<a.1 then α j else if j=a.1 then a.2.val else β j)
    by_cases hi : i<a.1
    · rw [if_pos hi]
      by_cases hj : j<a.1
      · rw [if_pos hj]
        exact hα hij
      · rw [if_neg hj]
        by_cases he : j=a.1
        · rw [if_pos he]
          exact lt_of_lt_of_le (hα (he ▸ hij)) a.2.property.1.le
        · rw [if_neg he]
          exact lt_of_lt_of_le (hα hij) (hab j)
    · have hj : ¬ j<a.1 := not_lt_of_ge (le_trans (le_of_not_gt hi) hij.le)
      have hja : j≠a.1 := ne_of_gt (lt_of_le_of_lt (le_of_not_gt hi) hij)
      rw [if_neg hi,if_neg hj,if_neg hja]
      by_cases he : i=a.1
      · rw [if_pos he]
        exact lt_of_le_of_lt a.2.property.2 (hβ (he ▸ hij))
      · rw [if_neg he]
        exact hβ hij

def intervalPathExponent (α β : Fin s → Fin n) (x : NormalizedBandVariable α β) :
    NormalizedBandVariable α β →₀ ℕ :=
  normalizedMinorTermExponent α β (intervalPathColumn α β x) 1

theorem intervalPathExponent_none (α β : Fin s → Fin n) (hs : 0 < s)
    (x : NormalizedBandVariable α β) : intervalPathExponent α β x none = 1 := by
  simpa only [normalizedDiagonalExponent,normalizedChainTermExponent,Fin.sum_univ_one,
    intervalPathExponent] using
    normalizedDiagonalExponent_none α β (fun _ : Fin 1 => intervalPathColumn α β x) hs

theorem normalizedMinorTermExponent_diagonal_some (α β I : Fin s → Fin n)
    (b : BandNonpivot α β) :
    normalizedMinorTermExponent α β I 1 (some b) = if I b.1=b.2.val then 1 else 0 := by
  classical
  simp only [normalizedMinorTermExponent,Finset.sum_apply',Equiv.Perm.one_apply,
    normalizedEntryExponent_some]
  rw [Finset.sum_eq_single b.1]
  · simp only [Prod.mk.injEq,true_and]
  · intro i hi hib
    simp only [Prod.mk.injEq,hib,false_and,ite_false]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

theorem intervalPathExponent_some (α β : Fin s → Fin n)
    (x : NormalizedBandVariable α β) (b : BandNonpivot α β) :
    intervalPathExponent α β x (some b) = (if x=some b then 1 else 0) +
      match x with
      | none => 0
      | some a => if a.1<b.1 ∧ b.2.val=β b.1 then 1 else 0 := by
  classical
  rw [intervalPathExponent,normalizedMinorTermExponent_diagonal_some]
  cases x with
  | none => simp only [intervalPathColumn,b.2.property.1.ne,ite_false,reduceCtorEq,zero_add]
  | some a =>
    by_cases hrow : a.1=b.1
    · rcases a with ⟨i,j,hj⟩
      rcases b with ⟨i',j',hj'⟩
      dsimp at hrow
      subst i'
      simp [intervalPathColumn,lt_irrefl,Subtype.ext_iff]
    · by_cases hlt : a.1<b.1
      · simp [intervalPathColumn,not_lt_of_ge hlt.le,Ne.symm hrow,hrow,hlt,
          eq_comm,show a ≠ b from fun h => hrow (congrArg Sigma.fst h),
          show b ≠ a from fun h => hrow (congrArg Sigma.fst h.symm)]
      · have hgt : b.1<a.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hrow)
        simp [intervalPathColumn,hgt,hlt,b.2.property.1.ne,
          show a ≠ b from fun h => hrow (congrArg Sigma.fst h)]

def earlierPathCount (α β : Fin s → Fin n)
    (c : NormalizedBandVariable α β →₀ ℕ) (i : Fin s) : ℕ :=
  ∑ a : BandNonpivot α β, if a.1 < i then c (some a) else 0

theorem intervalPathCombination_none (α β : Fin s → Fin n) (hs : 0 < s)
    (c : NormalizedBandVariable α β →₀ ℕ) :
    Finsupp.linearCombination ℕ (intervalPathExponent α β) c none =
      ∑ x, c x := by
  classical
  rw [Finsupp.linearCombination_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,
    intervalPathExponent_none α β hs,mul_one]

theorem intervalPathCombination_some (α β : Fin s → Fin n)
    (c : NormalizedBandVariable α β →₀ ℕ) (b : BandNonpivot α β) :
    Finsupp.linearCombination ℕ (intervalPathExponent α β) c (some b) =
      c (some b) + if b.2.val=β b.1 then earlierPathCount α β c b.1 else 0 := by
  classical
  rw [Finsupp.linearCombination_apply,Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,
    intervalPathExponent_some,mul_add,Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (some b)]
  · simp only [ite_true,mul_one]
    congr 1
    rw [Fintype.sum_option]
    by_cases hb : b.2.val=β b.1
    · simp [hb,earlierPathCount,mul_ite]
    · simp [hb]
  · intro x hx hxb
    rw [if_neg hxb,mul_zero]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

theorem intervalPathCombination_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective (Finsupp.linearCombination ℕ (intervalPathExponent α β)) := by
  classical
  intro c d h
  have hrow (k : ℕ) : ∀ i : Fin s, i.val=k →
      ∀ j : {j : Fin n // α i<j ∧ j≤β i}, c (some ⟨i,j⟩)=d (some ⟨i,j⟩) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi j
      have hearlier : earlierPathCount α β c i = earlierPathCount α β d i := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hai : a.1 < i
        · rw [if_pos hai,if_pos hai]
          exact ih a.1.val (by simpa only [← hi,Fin.lt_def] using hai) a.1 rfl a.2
        · rw [if_neg hai,if_neg hai]
      have he := congrArg (fun a => a (some ⟨i,j⟩)) h
      rw [intervalPathCombination_some,intervalPathCombination_some,hearlier] at he
      exact Nat.add_right_cancel he
  have hsome (a : BandNonpivot α β) : c (some a)=d (some a) :=
    hrow a.1.val a.1 rfl a.2
  apply Finsupp.ext
  intro x
  cases x with
  | some a => exact hsome a
  | none =>
    have he := congrArg (fun a => a none) h
    rw [intervalPathCombination_none α β hs,intervalPathCombination_none α β hs,
      Fintype.sum_option,Fintype.sum_option] at he
    have hsum : ∑ a : BandNonpivot α β, c (some a) = ∑ a, d (some a) :=
      Finset.sum_congr rfl (fun a ha => hsome a)
    rw [hsum] at he
    exact Nat.add_right_cancel he

theorem normalizedPathMinors_algebraicIndependent
    (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    AlgebraicIndependent K (fun x : NormalizedBandVariable α β =>
      normalizeBand (K := K) α β (bandMinor α β (intervalPathColumn α β x))) := by
  apply algebraicIndependent_of_weightMonic (normalizedEntryWeight α β) _
    (intervalPathExponent α β)
  · intro x
    let C : BandChain α β 1 := ⟨fun _ => intervalPathColumn α β x,
      fun _ => intervalPathColumn_strictMono α β hα hβ hab x,
      fun _ => intervalPathColumn_mem α β hab x,
      fun a b hab => le_rfl⟩
    simpa only [bandStandardProduct,Fin.prod_univ_one,normalizedDiagonalExponent,
      normalizedChainTermExponent,Fin.sum_univ_one,intervalPathExponent,C] using
      normalizeBand_standard_weightMonic (K := K) α β C
  · exact intervalPathCombination_injective α β hs

def intervalPathCoordinate (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (x : NormalizedBandVariable α β) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β :=
  Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
    (X ⟨intervalPathColumn α β x,intervalPathColumn_strictMono α β hα hβ hab x⟩)

theorem intervalPathCoordinates_algebraicIndependent
    (α β : Fin s → Fin n) (hα : StrictMono α) (hβ : StrictMono β)
    (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    AlgebraicIndependent K (intervalPathCoordinate (K := K) α β hα hβ hab) := by
  apply AlgebraicIndependent.of_comp (normalizedIntervalMap α β hα.monotone hβ.monotone)
  convert normalizedPathMinors_algebraicIndependent (K := K) α β hα hβ hab hs using 1
  funext x
  change normalizeBand α β (bandPluckerMap α β
    (X ⟨intervalPathColumn α β x,intervalPathColumn_strictMono α β hα hβ hab x⟩)) = _
  apply congrArg (normalizeBand (K := K) α β)
  exact MvPolynomial.aeval_X
    (f := fun I : PluckerIndex s n => bandMinor (K := K) α β I.val) _

/-- The full Krull-dimension clause of Lemma 2.2, for all nonempty intervals
of positive-size subsets and the actual generic-minor Plücker presentation. -/
theorem intervalPlucker_krullDim (α β : Fin s → Fin n)
    (hα : StrictMono α) (hβ : StrictMono β) (hab : ∀ i, α i ≤ β i) (hs : 0 < s) :
    ringKrullDim (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) =
      (1 + ∑ i, ((β i).val - (α i).val) : ℕ) := by
  apply le_antisymm (intervalPlucker_krullDim_le α β hα.monotone hβ.monotone hs)
  letI := intervalPluckerIdeal_isPrime (K := K) α β hα.monotone hβ.monotone hs
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg K]
  have h := (intervalPathCoordinates_algebraicIndependent (K := K) α β hα hβ hab hs).lift_cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0_of_finiteType (R := K)
    (S := MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)
  have hn := Cardinal.toNat_le_toNat h (by simpa using hfinite)
  have hn' : 1 + ∑ i, ((β i).val - (α i).val) ≤
      (Algebra.trdeg K
        (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β)).toNat := by
    simpa only [Cardinal.toNat_lift,Cardinal.mk_toNat_eq_card,normalizedBandVariable_card]
      using hn
  exact_mod_cast hn'

end PaperVerification.AlternatingForms

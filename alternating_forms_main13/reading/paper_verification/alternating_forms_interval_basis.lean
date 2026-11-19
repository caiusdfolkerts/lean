module

public import PaperVerification.AlternatingFormsIntegralStraightening
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The actual interval Plücker quotient has its standard-monomial basis

Integral generic-minor straightening gives spanning over every field in
the quotient by the actual generic-minor kernel. Forbidden coordinates then delete precisely
the chains outside the interval. Distinct diagonal monomials in the literal
band matrix prove independence and identify the full kernel of its minor map.
The row count is positive, as in the Grassmannians of the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n r : ℕ}

def pluckerWord (I : Fin r → PluckerIndex s n) : MvPolynomial (PluckerIndex s n) K :=
  ∏ j, X (I j)

def standardPluckerWord (C : StandardMinorChain s n r) :
    MvPolynomial (PluckerIndex s n) K :=
  pluckerWord (fun j => ⟨C.val j,C.property.1 j⟩)

theorem genericPluckerMap_word (I : Fin r → PluckerIndex s n) :
    genericPluckerMap (K := K) (pluckerWord I) =
      genericMinorProduct (fun j => (I j).val) := by
  simp only [pluckerWord,genericPluckerMap,map_prod,aeval_X,genericPluckerMinor,
    genericMinorProduct]

theorem genericPluckerMap_standardWord (C : StandardMinorChain s n r) :
    genericPluckerMap (K := K) (standardPluckerWord C) = genericStandardMinorProduct C :=
  genericPluckerMap_word _

def intervalAllStandardProduct (α β : Fin s → Fin n)
    (C : Σ r, BandChain α β r) :
    MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β :=
  intervalStandardProduct α β C.2

def intervalStandardSpan (α β : Fin s → Fin n) :
    Submodule K (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  Submodule.span K (Set.range (intervalAllStandardProduct (K := K) α β))

theorem standardWord_quotient_mem_intervalSpan (α β : Fin s → Fin n)
    (C : StandardMinorChain s n r) :
    Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (standardPluckerWord (K := K) C) ∈
      intervalStandardSpan α β := by
  classical
  by_cases hC : ∀ j i, α i ≤ C.val j i ∧ C.val j i ≤ β i
  · exact Submodule.subset_span
      ⟨⟨r,⟨C.val,C.property.1,hC,C.property.2⟩⟩,rfl⟩
  · obtain ⟨j,hj⟩ := not_forall.mp hC
    have hz : Ideal.Quotient.mk (intervalPluckerIdeal (K := K) α β)
        (X (⟨C.val j,C.property.1 j⟩ : PluckerIndex s n)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Submodule.mem_sup_right (Ideal.subset_span ⟨_,hj,rfl⟩)
    have hprod : Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
        (standardPluckerWord (K := K) C) = 0 := by
      simp only [standardPluckerWord,pluckerWord,map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    rw [hprod]
    exact (intervalStandardSpan α β).zero_mem

/-- Every word of any length straightens in the actual interval quotient. -/
theorem pluckerWord_quotient_mem_intervalSpan (α β : Fin s → Fin n)
    (I : Fin r → PluckerIndex s n) :
    Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (pluckerWord (K := K) I) ∈
      intervalStandardSpan α β := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (genericMinorProduct_mem_span_standard_all (R := K) (fun j => (I j).val))
  let p : MvPolynomial (PluckerIndex s n) K :=
    ∑ C : StandardMinorChain s n r, c C • standardPluckerWord C
  have hdiff : pluckerWord I-p ∈ matrixPluckerIdeal (K := K) (s := s) (n := n) := by
    change genericPluckerMap (pluckerWord I-p) = 0
    simp only [p,map_sub,map_sum,map_smul,genericPluckerMap_word,
      genericPluckerMap_standardWord]
    rw [hc,sub_self]
  have heq : Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (pluckerWord I) =
      Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (pluckerWord I) p).mpr (Submodule.mem_sup_left hdiff)
  rw [heq]
  simp only [p,map_sum,map_smul]
  exact (intervalStandardSpan α β).sum_mem fun C hC =>
    (intervalStandardSpan α β).smul_mem (c C)
      (standardWord_quotient_mem_intervalSpan α β C)

theorem intervalStandardSpan_mul_variable (α β : Fin s → Fin n)
    {z : MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β}
    (hz : z ∈ intervalStandardSpan α β) (I : PluckerIndex s n) :
    z * Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) (X I) ∈ intervalStandardSpan α β := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨r,C⟩,rfl⟩ := hz
    have h := pluckerWord_quotient_mem_intervalSpan (K := K) α β
      ((Fin.cons I (fun j => (⟨C.val j,C.property.1 j⟩ : PluckerIndex s n))) :
        Fin (r+1) → PluckerIndex s n)
    rw [pluckerWord,Fin.prod_univ_succ] at h
    change Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)
      (X I * chainPluckerProduct (K := K) α β C) ∈
        intervalStandardSpan α β at h
    rw [map_mul] at h
    change (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β))
        (chainPluckerProduct (K := K) α β C) *
      (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)) (X I) ∈ intervalStandardSpan α β
    rw [mul_comm]
    exact h
  | zero => simpa only [zero_mul] using (intervalStandardSpan α β).zero_mem
  | add x y hx hy hmx hmy =>
    simpa only [add_mul] using (intervalStandardSpan α β).add_mem hmx hmy
  | smul a x hx hmx =>
    simpa only [smul_mul_assoc] using (intervalStandardSpan α β).smul_mem a hmx

theorem intervalStandardSpan_eq_top (α β : Fin s → Fin n) :
    intervalStandardSpan (K := K) α β = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K (intervalPluckerIdeal α β) z
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 := pluckerWord_quotient_mem_intervalSpan (K := K) α β
      (Fin.elim0 : Fin 0 → PluckerIndex s n)
    simp only [pluckerWord,Fin.prod_univ_zero,map_one] at h1
    have ha := (intervalStandardSpan α β).smul_mem a h1
    simpa only [C_eq_smul_one,map_smul,map_one] using ha
  | add p q hp hq =>
    simpa only [map_add] using (intervalStandardSpan α β).add_mem hp hq
  | mul_X p I hp =>
    simpa only [map_mul] using intervalStandardSpan_mul_variable α β hp I

theorem chainDiagonalExponent_degree (I : Fin r → Fin s → Fin n) :
    Finsupp.weight (fun _ : Fin s × Fin n => (1 : ℕ)) (chainDiagonalExponent I) = r*s := by
  simp only [chainDiagonalExponent,chainTermExponent,minorTermExponent,map_sum,
    Finsupp.weight_single,one_smul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id]

theorem allChainDiagonalExponent_injective (α β : Fin s → Fin n) (hs : 0 < s) :
    Function.Injective (fun C : Σ r, BandChain α β r => chainDiagonalExponent C.2.val) := by
  rintro ⟨r,C⟩ ⟨r',C'⟩ h
  have hr := congrArg (Finsupp.weight (fun _ : Fin s × Fin n => (1 : ℕ))) h
  simp only [chainDiagonalExponent_degree] at hr
  have he : r=r' := Nat.eq_of_mul_eq_mul_right hs hr
  subst r'
  have hC : C = C' := chainDiagonalExponent_injective α β h
  cases hC
  rfl

theorem intervalBandProducts_all_linearIndependent (α β : Fin s → Fin n) (hs : 0 < s) :
    LinearIndependent K (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  apply linearIndependent_of_weightMonic (bandEntryWeight s n) _
    (fun C : S => chainDiagonalExponent C.val.2.val)
  · exact (allChainDiagonalExponent_injective α β hs).comp Subtype.val_injective
  · intro C
    exact bandStandardProduct_weightMonic α β C.val.2

/-- The band-minor map is injective on the literal interval quotient. -/
theorem intervalBandMap_injective (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Function.Injective (intervalBandMap (K := K) α β hα hβ) := by
  apply LinearMap.injective_of_linearIndependent
    (f := (intervalBandMap (K := K) α β hα hβ).toLinearMap)
    (show Submodule.span K (Set.range (intervalAllStandardProduct α β)) = ⊤ from
      intervalStandardSpan_eq_top α β)
  have he : (intervalBandMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
    funext C
    exact intervalBandMap_standardProduct α β hα hβ C.2
  rw [he]
  exact intervalBandProducts_all_linearIndependent α β hs

theorem intervalAllStandardProducts_linearIndependent (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    LinearIndependent K (intervalAllStandardProduct (K := K) α β) := by
  apply LinearIndependent.of_comp (intervalBandMap α β hα hβ).toLinearMap
  have he : (intervalBandMap (K := K) α β hα hβ).toLinearMap ∘
      intervalAllStandardProduct α β =
      (fun C : Σ r, BandChain α β r => bandStandardProduct (K := K) α β C.2) := by
    funext C
    exact intervalBandMap_standardProduct α β hα hβ C.2
  rw [he]
  exact intervalBandProducts_all_linearIndependent α β hs

theorem intervalPluckerIdeal_eq_bandKernel (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    intervalPluckerIdeal (K := K) α β = RingHom.ker (bandPluckerMap α β).toRingHom := by
  apply le_antisymm (intervalPluckerIdeal_le_kernel α β hα hβ)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply intervalBandMap_injective α β hα hβ hs
  change bandPluckerMap α β p = intervalBandMap α β hα hβ 0
  rw [map_zero]
  exact hp

/-- The primeness clause of Lemma 2.2 for the actual generic-minor presentation. -/
theorem intervalPluckerIdeal_isPrime (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    (intervalPluckerIdeal (K := K) α β).IsPrime := by
  rw [intervalPluckerIdeal_eq_bandKernel α β hα hβ hs]
  exact RingHom.ker_isPrime _

/-- The complete standard-monomial basis, indexed by all interval multichains. -/
def intervalStandardBasis (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) :
    Module.Basis (Σ r, BandChain α β r) K
      (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  Module.Basis.mk
    (intervalAllStandardProducts_linearIndependent α β hα hβ hs)
    (by rw [← intervalStandardSpan_eq_top (K := K) α β]; exact le_rfl)

end PaperVerification.AlternatingForms

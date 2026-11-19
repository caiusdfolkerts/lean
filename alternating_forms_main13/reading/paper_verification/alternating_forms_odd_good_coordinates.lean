module

public import PaperVerification.AlternatingFormsOddNormalForm
public import PaperVerification.AlternatingFormsHibiGroebner



@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped BigOperators
open Hibi

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "B" => oddPluckerStandardBasis (K := K) k t hs
local notation "P" => MvPolynomial (IntervalIndex α β) K

def oddGoodMap : P →ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  (Ideal.Quotient.mkₐ K Q).comp (rename Subtype.val)

def oddGoodIdeal : Ideal P := RingHom.ker (oddGoodMap (K := K) k t hs).toRingHom

@[simp] theorem oddGoodMap_X (I : IntervalIndex α β) :
    oddGoodMap (K := K) k t hs (X I)=Ideal.Quotient.mk Q (X I.val) := by
  change Ideal.Quotient.mkₐ K Q (rename Subtype.val (X I)) = _
  exact congrArg (Ideal.Quotient.mkₐ K Q) (MvPolynomial.rename_X Subtype.val I)

theorem oddGoodMap_standardPolynomial (C : OddStandardIndex k t hs) :
    oddGoodMap (K := K) k t hs (standardPolynomial α β C.2)=B C := by
  rw [oddPluckerStandardBasis_apply]
  simp only [standardPolynomial,map_prod,oddStandardRepresentative,chainPluckerProduct]
  apply Finset.prod_congr rfl
  intro j hj
  exact oddGoodMap_X (K := K) k t hs (intervalIndexOfChain α β C.2 j)

def oddGoodRepresentative
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) : P :=
  ((B).repr q).sum (fun C c => c • standardPolynomial α β C.2)

theorem oddGoodMap_representative
    (q : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :
    oddGoodMap k t hs (oddGoodRepresentative k t hs q)=q := by
  simp only [oddGoodRepresentative,Finsupp.sum,map_sum,map_smul,
    oddGoodMap_standardPolynomial]
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using (B).linearCombination_repr q

theorem oddGoodMap_surjective : Function.Surjective (oddGoodMap (K := K) k t hs) :=
  fun q => ⟨oddGoodRepresentative k t hs q,oddGoodMap_representative k t hs q⟩

def oddGoodQuotientEquiv : (P⧸oddGoodIdeal k t hs) ≃ₐ[K]
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  Ideal.quotientKerAlgEquivOfSurjective (oddGoodMap_surjective k t hs)

def oddGoodNormalForm (p : P) : P :=
  oddGoodRepresentative k t hs (oddGoodMap k t hs p)

@[simp] theorem oddGoodMap_normalForm (p : P) :
    oddGoodMap k t hs (oddGoodNormalForm k t hs p)=oddGoodMap k t hs p :=
  oddGoodMap_representative k t hs _

theorem oddGoodNormalForm_pair (I J : IntervalIndex α β) :
    oddGoodNormalForm (K := K) k t hs (X I*X J)=
      (oddCoefficients (K := K) k t hs (X I.val*X J.val)).sum
        (fun C c => c • standardPolynomial α β C.2) := by
  simp only [oddGoodNormalForm,oddGoodRepresentative,oddCoefficients,map_mul,oddGoodMap_X]
  all_goals rfl


def oddQuadraticRelation (I J : IntervalIndex α β) : P :=
  X I*X J-oddGoodNormalForm k t hs (X I*X J)

def oddQuadraticSet : Set P :=
  {p | ∃ I J,incomparable α β I J ∧ p=oddQuadraticRelation k t hs I J}

theorem oddQuadraticRelation_mem (I J : IntervalIndex α β) :
    oddQuadraticRelation (K := K) k t hs I J∈oddGoodIdeal k t hs := by
  change oddGoodMap k t hs (X I*X J-oddGoodNormalForm k t hs (X I*X J))=0
  rw [map_sub,oddGoodMap_normalForm,sub_self]

theorem standardPolynomial_isHomogeneous (C : OddStandardIndex k t hs) :
    (standardPolynomial (K := K) α β C.2).IsHomogeneous C.1 := by
  simpa only [standardPolynomial,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ
      (fun j => (X (intervalIndexOfChain α β C.2 j) : P)) (fun _ => 1)
      (fun j hj => isHomogeneous_X K _)

theorem oddQuadraticRelation_homogeneous (I J : IntervalIndex α β) :
    (oddQuadraticRelation (K := K) k t hs I J).IsHomogeneous 2 := by
  apply ((isHomogeneous_X K I).mul (isHomogeneous_X K J)).sub
  rw [oddGoodNormalForm_pair]
  apply IsHomogeneous.sum
  intro C hC
  have hd := odd_pair_coefficients_degree k t hs I J C (Finsupp.mem_support_iff.mp hC)
  intro a ha
  refine (standardPolynomial_isHomogeneous (K := K) k t hs C ?_).trans hd
  intro hz
  apply ha
  simp only [coeff_smul,hz,smul_zero]

def goodChainExponent (C : OddStandardIndex k t hs) : IntervalIndex α β →₀ ℕ :=
  ∑ j,Finsupp.single (intervalIndexOfChain α β C.2 j) 1

theorem standardPolynomial_eq_monomial (C : OddStandardIndex k t hs) :
    standardPolynomial (K := K) α β C.2=monomial (goodChainExponent k t hs C) 1 := by
  simp only [standardPolynomial,X,prod_monomial_eq_monomial_sum,
    Finset.prod_const_one,goodChainExponent]

theorem goodChainExponent_weight (u : IntervalIndex α β → ℕ)
    (C : OddStandardIndex k t hs) :
    Finsupp.weight u (goodChainExponent k t hs C)=
      ∑ j,u (intervalIndexOfChain α β C.2 j) := by
  simp only [goodChainExponent,map_sum,Finsupp.weight_single,one_smul]

theorem goodChainExponent_vertexWeight (C : OddStandardIndex k t hs) :
    Finsupp.weight (oddGoodWeight k t hs) (goodChainExponent k t hs C)=
      oddStandardWeight k t hs C := by
  rw [goodChainExponent_weight]
  rfl

theorem goodChainExponent_diagonalWeight (C : OddStandardIndex k t hs) :
    Finsupp.weight (diagonalWeight α β) (goodChainExponent k t hs C)=
      standardDiagonalWeight α β C := goodChainExponent_weight k t hs _ C

theorem normalChain_injective_on_normal :
    Function.Injective (fun a : {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a} =>
      normalChain α β a.val) := by
  intro a b h
  apply Subtype.ext
  apply MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℚ)≠0)
  change (monomial a.val 1 : MvPolynomial (IntervalIndex α β) ℚ) = monomial b.val 1
  rw [←normalChain_polynomial α β a.val a.property,
    ←normalChain_polynomial α β b.val b.property]
  exact congrArg (fun C : Σ r, BandChain α β r =>
    standardPolynomial (K := ℚ) α β C.2) h


theorem oddGood_normal_polynomial_eq_zero (p : P)
    (hp : ∀ a∈p.support,NormalMonomial α β a) (hz : oddGoodMap k t hs p=0) : p=0 := by
  classical
  have hli : LinearIndependent K (fun a : p.support =>
      oddGoodMap k t hs (monomial a.val 1 : P)) := by
    have h := (B).linearIndependent.comp
      (fun a : p.support => normalChain α β a.val) (by
        intro a b hab
        have hne := normalChain_injective_on_normal k t hs
          (show normalChain α β (⟨a.val,hp a.val a.property⟩ :
            {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a}).val=
            normalChain α β (⟨b.val,hp b.val b.property⟩ :
            {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a}).val from hab)
        exact Subtype.ext (congrArg
          (fun z : {a : IntervalIndex α β →₀ ℕ // NormalMonomial α β a} => z.val) hne))
    convert h using 1
    funext a
    rw [←normalChain_polynomial α β a.val (hp a.val a.property)]
    exact oddGoodMap_standardPolynomial (K := K) k t hs (normalChain α β a.val)
  have hsum : (∑ a : p.support,p.coeff a.val •
      oddGoodMap k t hs (monomial a.val 1 : P))=0 := by
    rw [Finset.sum_coe_sort p.support (fun a => p.coeff a •
      oddGoodMap k t hs (monomial a 1 : P))]
    have he : oddGoodMap k t hs p = ∑ a ∈ p.support,
        p.coeff a • oddGoodMap k t hs (monomial a 1 : P) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show monomial a (p.coeff a) = p.coeff a • (monomial a 1 : P) from by
        simp only [smul_monomial,smul_eq_mul,mul_one],map_smul]
    exact he.symm.trans hz
  have hc := Fintype.linearIndependent_iff.mp hli (fun a => p.coeff a.val) hsum
  ext a
  change p.coeff a = 0
  by_cases ha : a∈p.support
  · exact hc ⟨a,ha⟩
  · exact notMem_support_iff.mp ha

end PaperVerification.AlternatingForms

module

public import PaperVerification.AlternatingFormsIntervalBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Every actual graded piece of the interval Plücker quotient

The component is the image of the ordinary homogeneous polynomial submodule
under the literal quotient map. The standard basis in this component is
indexed by multichains of exactly that length. The proof uses homogeneous
projection in the band-matrix polynomial ring and the proved injectivity of
the band map, rather than assigning a grading by definition to a free model.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Module

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n r : ℕ}

theorem bandMinor_isHomogeneous (α β I : Fin s → Fin n) :
    (bandMinor (K := K) α β I).IsHomogeneous s := by
  classical
  rw [bandMinor_expansion]
  apply IsHomogeneous.sum
  intro σ hσ
  apply isHomogeneous_monomial
  simp only [Finsupp.degree_eq_weight_one,minorTermExponent,map_sum,
    Finsupp.weight_single,Pi.one_apply,one_smul,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_id]

theorem bandStandardProduct_isHomogeneous (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    (bandStandardProduct (K := K) α β C).IsHomogeneous (s*r) := by
  simpa only [bandStandardProduct,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.mul_comm,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ (fun j => bandMinor (K := K) α β (C.val j))
      (fun _ => s) (fun j hj => bandMinor_isHomogeneous α β (C.val j))

theorem bandPluckerMap_isHomogeneous (α β : Fin s → Fin n)
    (p : MvPolynomial (PluckerIndex s n) K) (hp : p.IsHomogeneous r) :
    (bandPluckerMap α β p).IsHomogeneous (s*r) :=
  hp.aeval _ (fun I => bandMinor_isHomogeneous α β I.val)

theorem chainPluckerProduct_isHomogeneous (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    (chainPluckerProduct (K := K) α β C).IsHomogeneous r := by
  simpa only [chainPluckerProduct,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_id] using
    IsHomogeneous.prod Finset.univ
      (fun j => (X ⟨C.val j,C.property.1 j⟩ : MvPolynomial (PluckerIndex s n) K))
      (fun _ => 1) (fun j hj => isHomogeneous_X K _)

def intervalPluckerDegree (α β : Fin s → Fin n) (r : ℕ) :
    Submodule K (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :=
  (homogeneousSubmodule (PluckerIndex s n) K r).map
    (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)).toLinearMap

theorem intervalStandardProduct_mem_degree (α β : Fin s → Fin n)
    (C : BandChain α β r) :
    intervalStandardProduct (K := K) α β C ∈ intervalPluckerDegree α β r :=
  ⟨chainPluckerProduct α β C,chainPluckerProduct_isHomogeneous α β C,rfl⟩

theorem intervalBandMap_projection_lift (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ)
    (q : MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) :
    ∃ y ∈ Submodule.span K (Set.range (intervalStandardProduct (K := K) (r := r) α β)),
      intervalBandMap α β hα hβ y =
        homogeneousComponent (s*r) (intervalBandMap α β hα hβ q) := by
  have hq : q ∈ intervalStandardSpan α β := by
    rw [intervalStandardSpan_eq_top]
    trivial
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨⟨l,C⟩,rfl⟩ := hq
    by_cases hl : l=r
    · subst l
      refine ⟨intervalStandardProduct α β C,Submodule.subset_span ⟨C,rfl⟩,?_⟩
      simpa only [intervalAllStandardProduct,intervalBandMap_standardProduct] using
        (homogeneousComponent_eq_self (bandStandardProduct_isHomogeneous (K := K) α β C)).symm
    · refine ⟨0,(Submodule.span K _).zero_mem,?_⟩
      change intervalBandMap α β hα hβ 0 =
        homogeneousComponent (s*r) (intervalBandMap α β hα hβ
          (intervalStandardProduct α β C))
      rw [map_zero,intervalBandMap_standardProduct,
        homogeneousComponent_of_mem (bandStandardProduct_isHomogeneous (K := K) α β C)]
      have hsr : s*r ≠ s*l := fun he => hl (Nat.eq_of_mul_eq_mul_left hs he.symm)
      rw [if_neg hsr]
  | zero =>
    exact ⟨0,(Submodule.span K _).zero_mem,by simp only [map_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x',hx',heqx⟩ := ihx
    obtain ⟨y',hy',heqy⟩ := ihy
    exact ⟨x'+y',(Submodule.span K _).add_mem hx' hy',by
      simp only [map_add,heqx,heqy]⟩
  | smul a x hx ih =>
    obtain ⟨x',hx',heq⟩ := ih
    exact ⟨a • x',(Submodule.span K _).smul_mem a hx',by simp only [map_smul,heq]⟩

theorem intervalPluckerDegree_eq_standardSpan (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    intervalPluckerDegree (K := K) α β r =
      Submodule.span K (Set.range (intervalStandardProduct (K := K) (r := r) α β)) := by
  apply le_antisymm
  · rintro q ⟨p,hp,rfl⟩
    obtain ⟨y,hy,heq⟩ := intervalBandMap_projection_lift α β hα hβ hs r
      (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p)
    change intervalBandMap α β hα hβ y =
      homogeneousComponent (s*r) (bandPluckerMap α β p) at heq
    rw [homogeneousComponent_eq_self (bandPluckerMap_isHomogeneous α β p hp)] at heq
    have hyq : y = Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β) p :=
      intervalBandMap_injective α β hα hβ hs heq
    rwa [hyq] at hy
  · apply Submodule.span_le.mpr
    rintro q ⟨C,rfl⟩
    exact intervalStandardProduct_mem_degree α β C

def intervalPluckerDegreeBasis (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    Basis (BandChain α β r) K (intervalPluckerDegree (K := K) α β r) :=
  (Basis.span (intervalStandardProducts_linearIndependent (K := K) α β hα hβ r)).map
    (LinearEquiv.ofEq _ _ (intervalPluckerDegree_eq_standardSpan α β hα hβ hs r).symm)

@[simp] theorem intervalPluckerDegreeBasis_apply (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) (C : BandChain α β r) :
    (intervalPluckerDegreeBasis (K := K) α β hα hβ hs r C :
      MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) =
      intervalStandardProduct α β C := by
  simp only [intervalPluckerDegreeBasis,Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Basis.coe_span_apply]

/-- The Hilbert function in Lemma 2.2, expressed by the exact multichain count
of its actual degree-r quotient component. -/
theorem intervalPluckerDegree_finrank (α β : Fin s → Fin n)
    (hα : Monotone α) (hβ : Monotone β) (hs : 0 < s) (r : ℕ) :
    Module.finrank K (intervalPluckerDegree (K := K) α β r) = Fintype.card (BandChain α β r) :=
  Module.finrank_eq_card_basis (intervalPluckerDegreeBasis α β hα hβ hs r)

end PaperVerification.AlternatingForms

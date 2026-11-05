module

public import PaperVerification.GenericVectorSectionSmoothness
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Generic emptiness when there are too many equations

The same parameter polynomial used for generic smoothness makes the gradients
of the original equations independent at every field-valued common zero.
Their number therefore cannot exceed the number of ambient differential
coordinates. If it does, the literal ideal of equations is the unit ideal.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- Nonvanishing of a parameter polynomial persists in every extension field. -/
lemma parameter_aeval_map_ne_zero {L : Type*} [Field L] [Algebra K L]
    (a : ι → K) (p : MvPolynomial ι K) (ha : MvPolynomial.aeval a p ≠ 0) :
    MvPolynomial.aeval (fun i => algebraMap K L (a i)) p ≠ 0 := by
  have he : algebraMap K L (MvPolynomial.aeval a p) =
      MvPolynomial.aeval (fun i => algebraMap K L (a i)) p := by
    simpa only [Algebra.ofId_apply] using
      (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L) p)
  rw [← he]
  intro h
  exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))

/-- The number of equations is bounded by the ambient differential rank at
every field-valued common zero in the good parameter locus. -/
theorem linearSection_card_le_of_point [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (χ : R →ₐ[K] L)
    (hz : ∀ j, χ (linearSection v a j)=0) :
    Fintype.card κ ≤ Fintype.card τ := by
  have hz' : ∀ j, ∑ i, algebraMap K L (a i)*χ (v j i)=0 := by
    intro j
    simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes]
      using hz j
  have h := specialized_gradient_linearIndependent b v u hvu χ
    (fun i => algebraMap K L (a i)) (parameter_aeval_map_ne_zero a _ ha) hz'
  simpa only [Module.finrank_fintype_fun_eq_card] using h.fintype_card_le_finrank

/-- Above the dimension threshold, the equations generate the unit ideal on
the same nonempty principal open of the full parameter space. -/
theorem linearSection_ideal_eq_top_of_more_equations [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    (hcard : Fintype.card τ < Fintype.card κ) :
    Ideal.span (Set.range (linearSection v a)) = ⊤ := by
  classical
  by_contra hI
  obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal _ hI
  letI : J.IsMaximal := hJ
  letI : Field (R ⧸ J) := Ideal.Quotient.field J
  have hz : ∀ j, (Ideal.Quotient.mkₐ K J) (linearSection v a j)=0 := by
    intro j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hIJ (Ideal.subset_span (Set.mem_range_self j)))
  exact (not_le_of_gt hcard)
    (linearSection_card_le_of_point b v u hvu a ha (Ideal.Quotient.mkₐ K J) hz)

end PaperVerification.GenericSectionDifferentials

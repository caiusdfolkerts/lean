module

public import PaperVerification.GenericVectorSectionSmoothness
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Residue-field Jacobian rows on the same generic parameter open

This exposes the residue calculation used inside generic smoothness. The
avoidance polynomial and the literal defining equations are unchanged.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The defining Jacobian has independent rows in every residue field on the
already constructed principal open; no smoothness of the quotient is assumed. -/
theorem linearSection_residue_gradient_rows [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    (J : Ideal (R ⧸ Ideal.span (Set.range (linearSection v a)))) [J.IsMaximal] :
    LinearIndependent ((R ⧸ Ideal.span (Set.range (linearSection v a))) ⧸ J)
      (Matrix.map (fun j t => Ideal.Quotient.mk (Ideal.span (Set.range (linearSection v a)))
        (b.repr (D K R (linearSection v a j)) t) :
          Matrix κ τ (R ⧸ Ideal.span (Set.range (linearSection v a))))
            (Ideal.Quotient.mk J)) := by
  classical
  let I := Ideal.span (Set.range (linearSection v a))
  let S := R ⧸ I
  let L := S ⧸ J
  letI : Field L := Ideal.Quotient.field J
  let χ : R →ₐ[K] L := (Ideal.Quotient.mkₐ K J).comp (Ideal.Quotient.mkₐ K I)
  let a' : ι → L := fun i => algebraMap K L (a i)
  have ha' : MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
    have he : algebraMap K L (MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu)) =
        MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) := by
      simpa only [Algebra.ofId_apply,a'] using
        (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L)
          (criticalAvoidancePolynomial b v u hvu))
    rw [← he]
    intro h
    exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hz : ∀ j, ∑ i, a' i * χ (v j i) = 0 := by
    intro j
    have hz' : algebraMap R S (linearSection v a j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
    have h : χ (linearSection v a j) = 0 := by
      change Ideal.Quotient.mk J (algebraMap R S (linearSection v a j)) = 0
      rw [hz',map_zero]
    simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes,a'] using h
  have hind := specialized_gradient_linearIndependent b v u hvu χ a' ha' hz
  convert hind using 1
  funext j t
  change χ (b.repr (D K R (linearSection v a j)) t) = _
  rw [linearSection_gradient]
  simp only [map_sum,a',Algebra.smul_def,map_mul,AlgHom.commutes]

/-- For a polynomial chart, these are exactly the rows of the matrix of
formal partial derivatives of the original equations. -/
theorem linearSection_residue_pderiv_rows
    (v : Matrix κ ι (MvPolynomial τ K))
    (u : Matrix ι κ (MvPolynomial τ K)) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu) ≠ 0)
    (J : Ideal (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))))
    [J.IsMaximal] :
    LinearIndependent ((MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))) ⧸ J)
      (Matrix.map (fun j t => Ideal.Quotient.mk (Ideal.span (Set.range (linearSection v a)))
        (MvPolynomial.pderiv t (linearSection v a j)) :
          Matrix κ τ (MvPolynomial τ K ⧸ Ideal.span (Set.range (linearSection v a))))
            (Ideal.Quotient.mk J)) := by
  simpa only [KaehlerDifferential.mvPolynomialBasis_repr_apply] using
    linearSection_residue_gradient_rows
      (KaehlerDifferential.mvPolynomialBasis K τ) v u hvu a ha J

end PaperVerification.GenericSectionDifferentials

module

public import PaperVerification.RegularHomogeneousHilbertSeries
public import PaperVerification.FiniteGradedDimension
public import PaperVerification.WeightedMonomialSeries
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The dimension formula for a finite weighted complete intersection

This module combines the actual monomial basis of a polynomial ring, the
regular-sequence exactness argument, and polynomial evaluation at one.
Both the grading and the quotient are the ordinary Mathlib constructions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.WeightedRegularQuotientDimension

open MvPolynomial GradedInjectiveQuotient RegularHomogeneousHilbertSeries

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The usual weighted grading of the actual multivariable polynomial ring. -/
def polynomialGrading (weights : σ → ℕ) :
    TauCeti.InternalGrading K (MvPolynomial σ K) ℕ := by
  letI := MvPolynomial.weightedDecomposition K weights
  exact TauCeti.InternalGrading.ofDecomposition
    (MvPolynomial.weightedHomogeneousSubmodule K weights)

@[simp] theorem polynomialGrading_piece (weights : σ → ℕ) (d : ℕ) :
    (polynomialGrading (K:=K) weights).piece d =
      MvPolynomial.weightedHomogeneousSubmodule K weights d := by
  simp only [polynomialGrading, TauCeti.InternalGrading.ofDecomposition_piece]

/-- The exact dimension of each weighted monomial piece. -/
theorem finrank_polynomial_piece (weights : σ → ℕ) (d : ℕ) :
    Module.finrank K ((polynomialGrading (K:=K) weights).piece d) =
      Nat.card (WeightedMonomialSeries.Exponents weights d) := by
  rw [polynomialGrading_piece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {a : σ →₀ ℕ | Finsupp.weight weights a=d})

/-- Positive weights make every graded piece finite, without making the
whole polynomial ring finite-dimensional. -/
theorem polynomial_piece_finite (weights : σ → ℕ) (hw : ∀ i, weights i≠0) (d : ℕ) :
    FiniteDimensional K ((polynomialGrading (K:=K) weights).piece d) := by
  rw [polynomialGrading_piece]
  exact Module.Finite.iff_fg.mpr (MvPolynomial.weightedHomogeneousSubmodule_fg K weights hw d)

theorem polynomial_hilbertSeries_denominator (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) :
    hilbertSeries (polynomialGrading (K:=K) weights) *
      (∏ i, (1-PowerSeries.X^(weights i))) = 1 := by
  have hs : hilbertSeries (polynomialGrading (K:=K) weights) =
      PowerSeries.mk (fun d => (Nat.card (WeightedMonomialSeries.Exponents weights d) : ℤ)) := by
    apply PowerSeries.ext
    intro d
    simp only [hilbertSeries, PowerSeries.coeff_mk, finrank_polynomial_piece]
  rw [hs]
  exact WeightedMonomialSeries.series_mul_denominator_eq_one weights hw

/-- The literal quotient has the image grading and the complete-intersection
Hilbert-series identity. The number of equations is unrestricted, and the
quotient need not be finite-dimensional. -/
theorem exists_graded_quotient_hilbertSeries (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) (s : ℕ)
    (relations : Fin s → MvPolynomial σ K) (degrees : Fin s → ℕ)
    (hhom : ∀ i, (relations i).IsWeightedHomogeneous weights (degrees i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) (List.ofFn relations)) :
    ∃ H : TauCeti.InternalGrading K
        (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations)) ℕ,
      (∀ d, H.piece d = ((polynomialGrading (K:=K) weights).piece d).map
        ((Ideal.ofList (List.ofFn relations)).mkQ.restrictScalars K)) ∧
      hilbertSeries H * (∏ i, (1-PowerSeries.X^(weights i))) =
        ∏ i : Fin s, (1-PowerSeries.X^(degrees i)) := by
  classical
  let G := polynomialGrading (K:=K) weights
  let rs : List (MvPolynomial σ K × ℕ) := List.ofFn (fun i => (relations i,degrees i))
  have hrmap : rs.map Prod.fst=List.ofFn relations := by simp [rs,Function.comp_def]
  have hh : ∀ re ∈ rs,
      TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G.piece G.piece re.2 := by
    intro re hre
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hre
    apply TauCeti.LinearMap.isHomogeneous_def.mpr
    intro d x hx
    simp only [G, polynomialGrading_piece, scalarMap_apply, smul_eq_mul] at hx ⊢
    change (relations i*x).IsWeightedHomogeneous weights (d+degrees i)
    change x.IsWeightedHomogeneous weights d at hx
    simpa only [Nat.add_comm] using (hhom i).mul hx
  obtain ⟨H,hpieces,hseries⟩ := exists_quotient_grading_hilbertSeries G rs hh
    (by simpa only [hrmap] using hreg) (polynomial_piece_finite weights hw)
  have hI : (Ideal.ofList (rs.map Prod.fst) •
      (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K))) =
      Ideal.ofList (List.ofFn relations) := by
    rw [hrmap, Ideal.smul_eq_mul, Ideal.mul_top]
  let E := (Submodule.quotEquivOfEq _ _ hI).restrictScalars K
  let HQ := H.map E
  have hseriesQ : hilbertSeries HQ = hilbertSeries G *
      (∏ i : Fin s, (1-PowerSeries.X^(degrees i))) := by
    rw [hilbertSeries_map, hseries]
    simp [rs, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  refine ⟨HQ, ?_, ?_⟩
  · intro d
    rw [TauCeti.InternalGrading.map_piece, hpieces, ← Submodule.map_comp]
    rfl
  · rw [hseriesQ]
    calc
      _ = (hilbertSeries G * (∏ i, (1-PowerSeries.X^(weights i)))) *
          (∏ i : Fin s, (1-PowerSeries.X^(degrees i))) := by ring
      _ = _ := by rw [polynomial_hilbertSeries_denominator weights hw, one_mul]

/-- A finite quotient by exactly as many homogeneous regular equations as
variables has dimension determined by the product of their degrees. -/
theorem finrank_quotient_mul_weights (weights : σ → ℕ)
    (hw : ∀ i, weights i≠0) (s : ℕ)
    (relations : Fin s → MvPolynomial σ K) (degrees : Fin s → ℕ)
    (hhom : ∀ i, (relations i).IsWeightedHomogeneous weights (degrees i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) (List.ofFn relations))
    [FiniteDimensional K (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations))]
    (hs : s=Fintype.card σ) :
    (Module.finrank K (MvPolynomial σ K ⧸ Ideal.ofList (List.ofFn relations)) : ℤ) *
      (∏ i, (weights i : ℤ)) = ∏ i, (degrees i : ℤ) := by
  classical
  obtain ⟨HQ, _, hseriesQ⟩ := exists_graded_quotient_hilbertSeries
    weights hw s relations degrees hhom hreg
  let e : Fin s ≃ σ := Fintype.equivOfCardEq (by simpa using hs)
  have hp : hilbertSeries HQ * (∏ i : Fin s, (1-PowerSeries.X^(weights (e i)))) =
      ∏ i : Fin s, (1-PowerSeries.X^(degrees i)) := by
    rw [e.prod_comp (fun i => (1-PowerSeries.X^(weights i) : ℤ⟦X⟧))]
    exact hseriesQ
  have hd := FiniteGradedDimension.finrank_mul_product_degrees HQ
    (fun i => weights (e i)) degrees hp
  simpa only [e.prod_comp (fun i => (weights i : ℤ))] using hd

end PaperVerification.WeightedRegularQuotientDimension

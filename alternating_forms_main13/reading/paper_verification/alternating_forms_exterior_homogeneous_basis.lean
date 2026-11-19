module

public import PaperVerification.HomogeneousAugmentedBasis
public import PaperVerification.HomogeneousBasisProfile
public import PaperVerification.AlternatingFormsActualQuadraticKernel
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Actual homogeneous augmented bases for every exterior quadratic quotient

This construction supplies the finite bar-basis data, original degrees,
and exact degree-one coordinate generators for arbitrary f and g. The
full exterior quotient and its grading are already defined independently.
No genericity, rank formula, cutoff, or Koszul hypothesis is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.AlternatingForms.ExteriorHomogeneousBasis

open ExteriorAugmented QuadraticDual

universe u
variable {K ν : Type u} [Field K] [CharZero K] [Fintype ν] [DecidableEq ν]
  (f g : ⋀[K]^2 (ν → K))

instance quotientFinite : Module.Finite K (ExteriorAugmented.Quotient f g) := by
  letI : LinearOrder ν := linearOrderOfSTO WellOrderingRel
  haveI : Module.Finite K (ExteriorAlgebra K (ν → K)) :=
    Module.Finite.of_basis (Pi.basisFun K ν).ExteriorAlgebra
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K (exteriorRelationIdeal f g))

/-- This is exactly the original coordinate generator basis in degree one. -/
def degreeOneBasis : Module.Basis ν K ((grading f g).piece 1) :=
  (Pi.basisFun K ν).map (actualDegreeOneEquiv f g)

abbrev PositiveIndex := HomogeneousAugmentedBasis.PositiveIndex (ν := ν) (grading f g)

abbrev positiveDegree : PositiveIndex f g → ℕ :=
  HomogeneousAugmentedBasis.positiveDegree (grading f g)

def basis : Module.Basis (Option (PositiveIndex f g)) K (ExteriorAugmented.Quotient f g) :=
  HomogeneousAugmentedBasis.basis (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

def positiveFintype : Fintype (PositiveIndex f g) :=
  HomogeneousAugmentedBasis.positiveFintype (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

theorem basis_none : basis f g none=1 :=
  HomogeneousAugmentedBasis.basis_none (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g)

theorem basis_one (i : ν) :
    basis f g (some (.inl i))=actualGenerator f g (Pi.basisFun K ν i) := by
  rw [basis,HomogeneousAugmentedBasis.basis_one,degreeOneBasis,Module.Basis.map_apply]
  exact actualDegreeOneEquiv_apply f g _

theorem basis_positive_mem (i : PositiveIndex f g) :
    basis f g (some i)∈(grading f g).piece (positiveDegree f g i) :=
  HomogeneousAugmentedBasis.basis_positive_mem (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) i

theorem positiveDegree_pos (i : PositiveIndex f g) : 0<positiveDegree f g i :=
  HomogeneousAugmentedBasis.positiveDegree_pos (grading f g) i

theorem basis_positive_augmentation (i : PositiveIndex f g) :
    augmentation f g (basis f g (some i))=0 :=
  HomogeneousAugmentedBasis.basis_positive_augmentation (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) (augmentation_piece_zero f g) i

theorem product_homogeneous (a b c : PositiveIndex f g)
    (h : AugmentedAlgebraBasis.productCoefficients (basis f g) a b c≠0) :
    positiveDegree f g c=positiveDegree f g a+positiveDegree f g b :=
  HomogeneousAugmentedBasis.product_homogeneous (grading f g) (augmentation f g)
    (grading_zero f g) (degreeOneBasis f g) (grading_mul f g) a b c h

def degreeOneIndexEquiv : ν ≃ {i : PositiveIndex f g // positiveDegree f g i=1} :=
  HomogeneousAugmentedBasis.degreeOneIndexEquiv (grading f g)

@[simp] theorem degreeOneIndexEquiv_val (i : ν) : (degreeOneIndexEquiv f g i).val=Sum.inl i := rfl

/-- The positive basis counts in each degree are the intrinsic quotient dimensions. -/
theorem card_degree (d : ℕ) (hd : 0<d) :
    letI := positiveFintype f g
    Fintype.card {i : PositiveIndex f g // positiveDegree f g i=d}=
      Module.finrank K (ExteriorQuotientDegree f g d) := by
  letI := positiveFintype f g
  exact (HomogeneousBasisProfile.card_degree (grading f g) (basis f g) (positiveDegree f g)
    (grading_zero f g) (basis_none f g) (basis_positive_mem f g) d hd).trans
      (grading_piece_finrank f g d)

/-- The actual complete exterior Hilbert series, with every natural degree. -/
def actualHilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (ExteriorQuotientDegree f g d) : ℤ))

theorem degree_zero_finrank : Module.finrank K (ExteriorQuotientDegree f g 0)=1 := by
  rw [←grading_piece_finrank f g 0]
  have he := (DimensionFiveGradedBasis.scalarPieceEquiv
    (grading f g) (augmentation f g) (grading_zero f g)).finrank_eq
  simpa only [Module.finrank_self] using he.symm

/-- The bar-basis Hilbert series is rigorously the actual exterior quotient series. -/
theorem one_add_positiveSeries_eq :
    letI := positiveFintype f g
    1+WeightedBar.positiveSeries (positiveDegree f g)=actualHilbertSeries f g := by
  letI := positiveFintype f g
  apply PowerSeries.ext
  intro d
  rw [map_add,PowerSeries.coeff_one,HomogeneousBasisProfile.coeff_positiveSeries,
    actualHilbertSeries,PowerSeries.coeff_mk]
  by_cases hd : d=0
  · subst d
    have hn : ∀ i : PositiveIndex f g,positiveDegree f g i≠0 :=
      fun i => Nat.ne_of_gt (positiveDegree_pos f g i)
    simp [hn,degree_zero_finrank]
  · rw [card_degree f g d (Nat.pos_of_ne_zero hd)]
    simp [hd]

end PaperVerification.AlternatingForms.ExteriorHomogeneousBasis

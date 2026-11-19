module

public import Recovery.Unimodular.FlagKoszul.FlagExactness
public import Recovery.Unimodular.FlagKoszul.TorCriterion
public import Recovery.Unimodular.FlagKoszul.BarReindex

/-!
# A genuine commutative flag algebra is Koszul

The proof constructs homogeneous reduced-bar boundaries in every degree r<N.
Its final endpoint is diagonal vanishing in ordinary derived augmentation Tor.
The variables are finite, compatibility is reflexive and symmetric, and no
transitivity or word-PBW hypothesis occurs.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.FlagKoszul.FlagBar

variable {E K : Type*} [Field K]

/-- The actual residue-field equivalence, applied coefficientwise. -/
def residueMap (R : E → E → Prop) : Chain R Set.univ K →ₗ[K] (List (Positive R) →₀ K) :=
  Finsupp.mapRange.linearMap (quotientAllEquiv R (K := K)).toLinearMap

@[simp] theorem residueMap_apply (R : E → E → Prop) (z : Chain R Set.univ K) (L : List (Positive R)) :
    residueMap R z L = quotientAllEquiv R (K := K) (z L) := rfl

theorem residueMap_injective (R : E → E → Prop) : Function.Injective (residueMap R (K := K)) :=
  CoefficientModuleBar.map_injective (quotientAllEquiv R (K := K)).toLinearMap (quotientAllEquiv R (K := K)).injective

theorem residueMap_surjective (R : E → E → Prop) : Function.Surjective (residueMap R (K := K)) :=
  CoefficientModuleBar.map_surjective (quotientAllEquiv R (K := K)).toLinearMap (quotientAllEquiv R (K := K)).surjective

@[simp] theorem residueMap_single (R : E → E → Prop) (L : List (Positive R))
    (q : QuotientModule R Set.univ K) :
    residueMap R (Finsupp.single L q) = Finsupp.single L (quotientAllEquiv R q) := by
  simp [residueMap]

theorem residueMap_positive_action (R : E → E → Prop) (i : Positive R)
    (q : QuotientModule R Set.univ K) :
    quotientAllEquiv R (augmentedBasis R (K := K) (some i) • q) = 0 := by
  change quotientAllEquiv R (K := K)
    (Ideal.Quotient.mk (variableIdeal R Set.univ (K := K))
      (augmentedBasis R (K := K) (some i)) * q) = 0
  rw [map_mul, quotientAllEquiv_mk, augmentation_basis_some, zero_mul]

theorem residueMap_scalarLift (R : E → E → Prop) (q : QuotientModule R Set.univ K)
    (z : List (Positive R) →₀ K) :
    residueMap R (CoefficientDegree.scalarLift q z) = quotientAllEquiv R q • z := by
  ext L
  change quotientAllEquiv R (K := K) (CoefficientDegree.scalarLift q z L) = _
  rw [CoefficientDegree.scalarLift_apply, map_smul]
  exact mul_comm _ _

/-- The actual quotient-module differential becomes the negative reduced bar
operator. The coefficient formula is proved directly and retains independent
field and monomial-index universes. -/
theorem residueMap_boundary (R : E → E → Prop) (z : Chain R Set.univ K) :
    residueMap R (boundary R Set.univ z) =
      -PaperVerification.ReducedBarBasis.differential (augmentedBasis R (K := K)) (residueMap R z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, neg_zero]
  | add z w hz hw => simp only [map_add, hz, hw, neg_add]
  | single L q =>
    change residueMap R (CoefficientModuleBar.differential (augmentedBasis R (K := K))
      (Finsupp.single L q)) = _
    cases L with
    | nil =>
      rw [CoefficientDegree.differential_nil, map_zero, residueMap_single,
        PaperVerification.ReducedBarBasis.differential_single]
      simp only [PaperVerification.ReducedBarBasis.differentialBasis, smul_zero, neg_zero]
    | cons i L =>
      rw [CoefficientDegree.differential_cons, map_sub, residueMap_single,
        residueMap_positive_action, Finsupp.single_zero, zero_sub, residueMap_scalarLift,
        residueMap_single, PaperVerification.ReducedBarBasis.differential_single]

/-- The coefficient grading on A/J_all agrees exactly with the original
internal grading of the reduced bar complex. -/
theorem piece_iff_residueMap (R : E → E → Prop) (r N : ℕ) (z : Chain R Set.univ K) :
    z ∈ piece R Set.univ r N ↔
      residueMap R z ∈ BarReindex.homogeneousPiece (positiveDegree R) r N := by
  constructor
  · intro hz L hL
    have hn : quotientAllEquiv R (K := K) (z L) ≠ 0 := Finsupp.mem_support_iff.mp hL
    rw [quotientAllEquiv_eq_zero_coordinate] at hn
    have hh := hz L (zeroPoint R Set.univ) hn
    refine ⟨hh.1, ?_⟩
    simpa only [coefficientDegree, zeroPoint, map_zero, zero_add,
      HomogeneousWords.wordDegree, PaperVerification.WeightedBar.totalDegree] using hh.2
  · intro hz L u hu
    have he : u = zeroPoint R Set.univ := Subtype.ext ((allowed_univ_iff R u.1).mp u.2)
    subst u
    have hn : quotientAllEquiv R (K := K) (z L) ≠ 0 := by
      rwa [quotientAllEquiv_eq_zero_coordinate]
    have hh := hz (Finsupp.mem_support_iff.mpr hn)
    refine ⟨hh.1, ?_⟩
    simpa only [coefficientDegree, zeroPoint, map_zero, zero_add,
      HomogeneousWords.wordDegree, PaperVerification.WeightedBar.totalDegree] using hh.2

/-- Every homogeneous reduced-bar cycle above the diagonal is an actual
homogeneous boundary. This endpoint is also the leading-complex input
for filtered deformations. The field and monomial-index universes are independent. -/
theorem reduced_cycle_is_boundary [Fintype E] {R : E → E → Prop}
    (hrefl : ∀ i, R i i) (hsymm : ∀ {i j}, R i j → R j i)
    (r N : ℕ) (hrN : r < N) (z : List (Positive R) →₀ K)
    (hz : z ∈ BarReindex.homogeneousPiece (positiveDegree R) r N)
    (hdz : PaperVerification.ReducedBarBasis.differential (augmentedBasis R (K := K)) z = 0) :
    ∃ y ∈ BarReindex.homogeneousPiece (positiveDegree R) (r + 1) N,
      -PaperVerification.ReducedBarBasis.differential (augmentedBasis R (K := K)) y = z := by
  obtain ⟨b, hb⟩ := residueMap_surjective R z
  have hbp : b ∈ piece R Set.univ r N := (piece_iff_residueMap R r N b).mpr (by rw [hb]; exact hz)
  have hdb : boundary R Set.univ b = 0 := by
    apply residueMap_injective R
    rw [map_zero, residueMap_boundary, hb, hdz, neg_zero]
  obtain ⟨v, hv, hdv⟩ := exact_all_variable_quotients hrefl hsymm Set.univ r N hrN b hbp hdb
  refine ⟨residueMap R v, (piece_iff_residueMap R (r + 1) N v).mp hv, ?_⟩
  rw [← residueMap_boundary, hdv, hb]

#print axioms residueMap_boundary
#print axioms piece_iff_residueMap
#print axioms reduced_cycle_is_boundary

end Unimodular.FlagKoszul.FlagBar

namespace Unimodular.FlagKoszul

universe u
variable {E K : Type u} [Fintype E] [Field K]

/-- The ordinary semigroup-style definition of Koszulness: every internal
piece of ordinary derived Tor vanishes away from the diagonal. The algebra
is the literal quotient by the incompatible squarefree quadratic monomials. -/
theorem flagAlgebra_hasDiagonalTor {R : E → E → Prop}
    (hrefl : ∀ i, R i i) (hsymm : ∀ {i j}, R i j → R j i) :
    PaperVerification.WeightedBar.HasDiagonalTor
      (augmentation R (K := K)) (augmentedBasis R (K := K)) (augmentedBasis_none R)
      (augmentation_basis_some R) (positiveDegree R) (product_degree R) :=
  TorCriterion.hasDiagonalTor_of_boundaries
    (augmentation R) (augmentedBasis R (K := K)) (augmentedBasis_none R)
    (augmentation_basis_some R) (positiveDegree R) (product_degree R)
    (positiveDegree_pos R) (FlagBar.reduced_cycle_is_boundary hrefl hsymm)

#print axioms flagAlgebra_hasDiagonalTor

end Unimodular.FlagKoszul

#check Unimodular.FlagKoszul.flagAlgebra_hasDiagonalTor

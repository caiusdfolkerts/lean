module
public import PalomarMain13Literal
public import paper_verification.graded_degenerations3
import all paper_verification.graded_degenerations3
import all paper_verification.literal004
import all paper_verification.literal005

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace PalomarAlternatingDegeneration
open PaperVerification.WeightedInitialFiber
attribute [local instance] MvPolynomial.gradedAlgebra

section GradedFamilyBridge
variable {K σ τ υ : Type*} [Field K]

/-- Literal quotient images are the original ordinary coordinate pieces. -/
private theorem quotientPiece_eq_source (Q : Ideal (MvPolynomial σ K)) (d : ℕ) :
    Model.quotientPiece Q d = _root_.PaperVerification.HomogeneousIdealPieces.piece Q d := rfl

/-- The literal coefficient condition is exactly the actual ordinary Rees grading. -/
private theorem reesPiece_eq_source (Q : Ideal (MvPolynomial σ K))
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    Model.reesPiece Q w d = (_root_.PaperVerification.WeightedInitialFiber.reesCoordinateGrading Q hQ w).piece d := by
  ext a
  rw [_root_.PaperVerification.WeightedInitialFiber.mem_reesCoordinateGrading_iff]
  simp only [Model.reesPiece, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

/-- Transport the already constructed actual graded family, with all original
fiber pieces, to the literal coefficientwise specification. No family is assumed
in any principal theorem: the three original constructors are applied below. -/
private theorem gradedFamily_of_source (Q : Ideal (MvPolynomial σ K))
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (w : σ → ℕ)
    (sourceIdeal : Ideal (MvPolynomial τ K)) (specialIdeal : Ideal (MvPolynomial υ K))
    (G : _root_.PaperVerification.AlternatingForms.CoordinateGradedReesDegeneration Q hQ w sourceIdeal specialIdeal) :
    Model.GradedWeightFamily Q w sourceIdeal specialIdeal := by
  refine ⟨hQ, G.flat, ?_, ?_, ?_, ?_⟩
  · have hpieces := funext (reesPiece_eq_source Q hQ w)
    simpa only [hpieces] using
      (_root_.PaperVerification.WeightedInitialFiber.reesCoordinateGrading Q hQ w).isInternal
  · intro f d a ha
    rw [reesPiece_eq_source Q hQ w d] at ha ⊢
    exact _root_.PaperVerification.WeightedInitialFiber.reesPolynomial_smul_coordinate_mem Q hQ w f ha
  · refine ⟨G.specialFiberEquiv, ?_⟩
    intro d
    have h := G.specialFiber_piece d
    rw [_root_.PaperVerification.WeightedInitialFiber.zeroFiberCoordinateGrading_piece] at h
    rw [← reesPiece_eq_source Q hQ w d] at h
    exact h
  · intro c hc
    refine ⟨G.nonzeroFiberEquiv c hc, ?_⟩
    intro d
    have h := G.nonzeroFiber_piece c hc d
    rw [_root_.PaperVerification.WeightedInitialFiber.parameterFiberCoordinateGrading_piece] at h
    rw [← reesPiece_eq_source Q hQ w d] at h
    exact h
end GradedFamilyBridge

section ActualBarBridge
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]

private theorem literalPositiveCoordinates_eq (B : Module.Basis (Option I) K A) : Model.positiveCoordinates B = _root_.PaperVerification.AugmentedAlgebraBasis.positiveCoordinates B := by
  ext x i
  rfl
private theorem literalProductCoordinates_eq (B : Module.Basis (Option I) K A) (i j : I) : Model.productCoordinates B i j = _root_.PaperVerification.AugmentedAlgebraBasis.productCoefficients B i j := by
  change Model.positiveCoordinates B (B (some i) * B (some j)) = _root_.PaperVerification.AugmentedAlgebraBasis.positiveCoordinates B (B (some i) * B (some j))
  rw [literalPositiveCoordinates_eq]
private theorem literalPrepend_eq (i : I) : Model.prepend (K := K) i = _root_.PaperVerification.ReducedBarBasis.prepend (K := K) i := rfl
private theorem literalAppendTail_eq (L : List I) : Model.appendTail (K := K) L = _root_.PaperVerification.ReducedBarBasis.appendTail (K := K) L := rfl
private theorem literalMergeBasis_eq (B : Module.Basis (Option I) K A) (i : I) (L : List I) : Model.mergeBasis B i L = _root_.PaperVerification.ReducedBarBasis.mergeBasis B i L := by
  cases L with
  | nil => rfl
  | cons j T =>
    change Model.appendTail T (Model.productCoordinates B i j) = _root_.PaperVerification.ReducedBarBasis.appendTail T (_root_.PaperVerification.AugmentedAlgebraBasis.productCoefficients B i j)
    rw [literalAppendTail_eq, literalProductCoordinates_eq]
private theorem literalMerge_eq (B : Module.Basis (Option I) K A) (i : I) : Model.merge B i = _root_.PaperVerification.ReducedBarBasis.merge B i := by
  change Finsupp.linearCombination K (Model.mergeBasis B i) = Finsupp.linearCombination K (_root_.PaperVerification.ReducedBarBasis.mergeBasis B i)
  congr 1
  funext L
  exact literalMergeBasis_eq B i L

/-- The unchanged adjacent-product recursion agrees in every tensor length. -/
private theorem differentialBasis_eq_source (B : Module.Basis (Option I) K A) (L : List I) :
    Model.differentialBasis B L = _root_.PaperVerification.ReducedBarBasis.differentialBasis B L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change Model.merge B i (Finsupp.single L 1) - Model.prepend i (Model.differentialBasis B L) =
      _root_.PaperVerification.ReducedBarBasis.merge B i (Finsupp.single L 1) -
        _root_.PaperVerification.ReducedBarBasis.prepend i
          (_root_.PaperVerification.ReducedBarBasis.differentialBasis B L)
    rw [ih, literalMerge_eq, literalPrepend_eq]

/-- Genuine identity with the differential of the original normalized bar
resolution. Together with oddNormalizedBarTorIso below this identifies the
literal cycle/boundary criterion with ordinary Mathlib Tor. -/
private theorem differential_eq_source (B : Module.Basis (Option I) K A) :
    Model.differential B = _root_.PaperVerification.ReducedBarBasis.differential B := by
  change Finsupp.linearCombination K (Model.differentialBasis B) =
    Finsupp.linearCombination K (_root_.PaperVerification.ReducedBarBasis.differentialBasis B)
  congr 1
  funext L
  exact differentialBasis_eq_source B L
end ActualBarBridge

namespace PaperVerification.AlternatingForms
private theorem literalEdgeCost_eq (k : ℕ) : oddPathEdgeCost k = _root_.PaperVerification.AlternatingForms.oddPathEdgeCost k := by
  funext j
  by_cases h : Even j
  · simp only [oddPathEdgeCost, _root_.PaperVerification.AlternatingForms.oddPathEdgeCost, if_pos h]
  · simp only [oddPathEdgeCost, _root_.PaperVerification.AlternatingForms.oddPathEdgeCost, if_neg h]
private theorem literalPathCost_eq (e : ℕ → ℤ) (j : ℕ) : pathVertexCost e j = _root_.PaperVerification.AlternatingForms.pathVertexCost e j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [pathVertexCost, _root_.PaperVerification.AlternatingForms.pathVertexCost, ih]
private theorem literalVertexCost_eq (k : ℕ) : oddPathVertexCost k = _root_.PaperVerification.AlternatingForms.oddPathVertexCost k := by
  funext i
  change pathVertexCost (oddPathEdgeCost k) i.val = _root_.PaperVerification.AlternatingForms.pathVertexCost (_root_.PaperVerification.AlternatingForms.oddPathEdgeCost k) i.val
  rw [literalEdgeCost_eq, literalPathCost_eq]
private theorem literalShift_eq {ι : Type*} [Fintype ι] (u : ι → ℤ) : positiveWeightShift u = _root_.PaperVerification.AlternatingForms.positiveWeightShift u := rfl
private theorem literalVertexWeight_eq (k : ℕ) : oddPathVertexWeight k = _root_.PaperVerification.AlternatingForms.oddPathVertexWeight k := by
  funext i
  change positiveWeightShift (oddPathVertexCost k) - oddPathVertexCost k i = _root_.PaperVerification.AlternatingForms.positiveWeightShift (_root_.PaperVerification.AlternatingForms.oddPathVertexCost k) - _root_.PaperVerification.AlternatingForms.oddPathVertexCost k i
  rw [literalVertexCost_eq, literalShift_eq]
private theorem literalNatWeight_eq (k : ℕ) : oddNatVertexWeight k = _root_.PaperVerification.AlternatingForms.oddNatVertexWeight k := by
  funext i
  change (oddPathVertexWeight k i).toNat = (_root_.PaperVerification.AlternatingForms.oddPathVertexWeight k i).toNat
  rw [literalVertexWeight_eq]
private theorem literalPluckerWeight_eq (k s : ℕ) : pluckerVertexWeight (s := s) (oddNatVertexWeight k) = _root_.PaperVerification.AlternatingForms.pluckerVertexWeight (s := s) (_root_.PaperVerification.AlternatingForms.oddNatVertexWeight k) := by
  funext I
  change (∑ j, oddNatVertexWeight k (I.val j)) = ∑ j, _root_.PaperVerification.AlternatingForms.oddNatVertexWeight k (I.val j)
  rw [literalNatWeight_eq]
end PaperVerification.AlternatingForms

namespace PaperVerification.AlternatingForms
open MvPolynomial PaperVerification.WeightedInitialFiber
universe uMain
variable {K : Type uMain} [Field K] [CharZero K]

/-- Actual standard categorical Tor is computed by this precise normalized
bar complex. Its terms are the actual augmentation residue, not a rank model. -/
private def ordinaryTorComparison (k t : ℕ) (hs : t+2≤k+1) (r : ℕ) :=
  _root_.PaperVerification.AlternatingForms.oddNormalizedBarTorIso (K := K) k t hs r

theorem paper13_weight_families (k : ℕ) :
  Model.GradedWeightFamily (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) (pluckerVertexWeight (oddNatVertexWeight k)) (matrixPluckerIdeal (s := 1) (n := 2*k+1)) (intervalPluckerIdeal (oddIntervalLower k 1 (by omega)) (oddIntervalUpper k 1 (by omega))) ∧
  (∀ (t : ℕ) (hs : t+2≤k+1), Model.GradedWeightFamily (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)) (pluckerVertexWeight (oddNatVertexWeight k)) (isotropicPluckerIdeal (t := t) (oddPluckerForms k)) (intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))) ∧
  (∀ (s : ℕ) (hpos : 0<s) (hs : s≤k+1), Model.GradedWeightFamily (Hibi.goodBandIdeal (K := K) (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (Hibi.diagonalWeight (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (intervalPluckerIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs)) (Hibi.relationIdeal (oddIntervalLower k s hs) (oddIntervalUpper k s hs))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [literalPluckerWeight_eq]
    exact gradedFamily_of_source _
      (_root_.PaperVerification.AlternatingForms.matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1)) _ _ _
      (_root_.PaperVerification.AlternatingForms.onePlaneOddRichardsonGradedFlatDegeneration (K := K) k)
  · intro t hs
    rw [literalPluckerWeight_eq]
    exact gradedFamily_of_source _
      (_root_.PaperVerification.AlternatingForms.isotropicPluckerIdeal_isHomogeneous _) _ _ _
      (_root_.PaperVerification.AlternatingForms.oddRichardsonGradedFlatDegeneration (K := K) k t hs)
  · intro s hpos hs
    exact gradedFamily_of_source _
      (_root_.PaperVerification.AlternatingForms.Hibi.goodBandIdeal_coordinate_homogeneous _ _
        (_root_.PaperVerification.AlternatingForms.oddIntervalLower_strictMono k s hs).monotone
        (_root_.PaperVerification.AlternatingForms.oddIntervalUpper_strictMono k s hs).monotone hpos) _ _ _
      (_root_.PaperVerification.AlternatingForms.Hibi.hibiGradedFlatDegeneration (K := K)
        (_root_.PaperVerification.AlternatingForms.oddIntervalLower k s hs)
        (_root_.PaperVerification.AlternatingForms.oddIntervalUpper k s hs)
        (_root_.PaperVerification.AlternatingForms.oddIntervalLower_strictMono k s hs).monotone
        (_root_.PaperVerification.AlternatingForms.oddIntervalUpper_strictMono k s hs).monotone hpos)

theorem paper13_oneplane_quadratic (k : ℕ) : HasQuadraticGroebnerBasis (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) := by
  change _root_.PaperVerification.AlternatingForms.HasQuadraticGroebnerBasis (_root_.PaperVerification.AlternatingForms.matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
  exact (_root_.PaperVerification.AlternatingForms.odd_onePlane_conclusions (K := K) k).quadratic

theorem paper13_quadratic (k t : ℕ) (hs : t+2≤k+1) :
  Nonempty ((MvPolynomial (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) K ⧸ oddGoodIdeal k t hs) ≃ₐ[K] (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k))) ∧ HasQuadraticGroebnerBasis (oddGoodIdeal (K := K) k t hs) := by
  refine ⟨⟨_root_.PaperVerification.AlternatingForms.oddGoodQuotientEquiv (K := K) k t hs⟩, ?_⟩
  change _root_.PaperVerification.AlternatingForms.HasQuadraticGroebnerBasis (_root_.PaperVerification.AlternatingForms.oddGoodIdeal (K := K) k t hs)
  exact (_root_.PaperVerification.AlternatingForms.odd_higherPlane_conclusions (K := K) k t hs).quadratic

theorem paper13_higher_koszul (k t : ℕ) (hs : t+2≤k+1) :
  ∃ (I : Type uMain) (B : Module.Basis (Option I) K (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
    (ε : (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸ isotropicPluckerIdeal (t := t) (oddPluckerForms k)) →ₐ[K] K) (δ : I → ℕ),
    B none=1 ∧ (∀ i, ε (B (some i))=0) ∧
    (∀ i, 0<δ i ∧ B (some i) ∈ Model.quotientPiece (isotropicPluckerIdeal (t := t) (oddPluckerForms k)) (δ i)) ∧
    (∀ j, ε (Ideal.Quotient.mk _ (X j))=0) ∧
    (∀ r N, r≠N → ∀ z ∈ Model.barPiece (K := K) δ r N, Model.differential B z=0 → ∃ y ∈ Model.barPiece (K := K) δ (r+1) N, -Model.differential B y=z) := by
  let C := _root_.PaperVerification.AlternatingForms.OddPositiveStandardIndex (K := K) k t hs
  let B := _root_.PaperVerification.AlternatingForms.oddAugmentedBasis (K := K) k t hs
  let ε := _root_.PaperVerification.AlternatingForms.oddAugmentation (K := K) k t
  let δ := _root_.PaperVerification.AlternatingForms.oddPositiveDegree (K := K) k t hs
  have hp (r N : ℕ) : Model.barPiece (K := K) δ r N =
      _root_.PaperVerification.AlternatingForms.BarCompositions.internalDegreePiece
        (K := K) (_root_.PaperVerification.AlternatingForms.oddPositiveWordEquiv (K := K) k t hs) r N := by
    ext z
    change ((z.support : Set (List C)) ⊆ {L | L.length=r ∧ (L.map δ).sum=N}) ↔
      ((z.support : Set (List C)) ⊆ {L | L.length=r ∧
        (_root_.PaperVerification.AlternatingForms.BarCompositions.flattenBarWord
          (_root_.PaperVerification.AlternatingForms.oddPositiveWordEquiv (K := K) k t hs) L).length=N})
    simp only [_root_.PaperVerification.AlternatingForms.oddBarWord_length_eq_degree,
      _root_.PaperVerification.AlternatingForms.BarDegrees.totalDegree, δ]
  refine ⟨C, B, ε, δ,
    _root_.PaperVerification.AlternatingForms.oddAugmentedBasis_none k t hs,
    _root_.PaperVerification.AlternatingForms.oddAugmentation_positive k t hs, ?_, ?_, ?_⟩
  · intro i
    refine ⟨_root_.PaperVerification.AlternatingForms.oddPositiveDegree_pos k t hs i, ?_⟩
    change _root_.PaperVerification.AlternatingForms.oddAugmentedBasis (K := K) k t hs (some i) ∈ _root_.PaperVerification.AlternatingForms.oddPluckerDegree k t (_root_.PaperVerification.AlternatingForms.oddPositiveDegree (K := K) k t hs i)
    exact _root_.PaperVerification.AlternatingForms.oddAugmentedBasis_homogeneous k t hs i
  · intro j
    exact _root_.PaperVerification.AlternatingForms.isotropicAugmentation_X t (2*k+1)
      (_root_.PaperVerification.AlternatingForms.oddPluckerForms (K := K) k) j
  · intro r N hr z hz hd
    have hz0 := hz
    rw [hp r N] at hz0
    cases r with
    | zero =>
      have hzero := _root_.PaperVerification.AlternatingForms.oddInternalDegree_zero_eq_zero
        (K := K) k t hs N (Ne.symm hr) ⟨z, hz0⟩
      have heq : z=0 := congrArg Subtype.val hzero
      subst z
      exact ⟨0, (Model.barPiece (K := K) δ 1 N).zero_mem, by simp only [map_zero, neg_zero]⟩
    | succ r =>
      have hd0 : _root_.PaperVerification.ReducedBarBasis.differential B z=0 := by
        rw [← differential_eq_source B]
        exact hd
      obtain ⟨y, hy, he⟩ := _root_.PaperVerification.AlternatingForms.odd_normalized_bar_off_diagonal
        (K := K) k t hs (_root_.PaperVerification.WeightedMonomialOrder.finiteBaseOrder _)
        r N hr z hz0 hd0
      refine ⟨y, ?_, ?_⟩
      · rw [hp (r+2) N]
        exact hy
      · rw [differential_eq_source B]
        exact he

end PaperVerification.AlternatingForms
end PalomarAlternatingDegeneration

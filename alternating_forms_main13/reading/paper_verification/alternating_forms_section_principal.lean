module

public import PaperVerification.AlternatingFormsOddPrincipal
public import PaperVerification.AlternatingFormsIsotropicAtlas
public import PaperVerification.AlternatingFormsSectionTor
public import PaperVerification.AlternatingFormsOnePlaneSectionTor

/-!
# Theorem 1.3 with the actual complete Plucker section rings

The older coordinate-ring statement is retained in full. The additional
clauses identify its literal original Proj with the actual common-isotropic
normalized atlas, identify the original graded coordinate ring with the
direct sum of its actual global twisting-sheaf sections, and state the
degeneration and Koszul clauses for that actual section algebra.

The section-ring multiplication was defined independently by multiplying
actual local sections. The displayed polynomial maps use the corresponding
actual coordinate sections. Their kernels are proved to be exactly the
previous original coordinate ideals. Ordinary Tor here is genuinely Tor
over these complete section algebras, computed by their actual bar or
projective resolutions with the original homogeneous degrees.

This is a full-scope assembly candidate, not a verification certificate.
Its complete canonical module closure and actual proof bodies remain to be
checked. Every positive plane dimension, the one-plane boundary, and the
maximal singleton interval are included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry CategoryTheory
open PaperVerification.ProjectiveSectionRing
open PaperVerification.WeightedInitialFiber

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Flatness and both fibers, with the original nonzero fiber identified
with the separately defined actual complete section algebra. -/
def WeightedFlatDegenerationTo {σ τ : Type*}
    (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ)
    (J : Ideal (MvPolynomial τ K))
    (S : Type*) [CommRing S] [Algebra K S] : Prop :=
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧
  Nonempty (ZeroFiber Q w ≃ₐ[K] (MvPolynomial τ K⧸J)) ∧
  ∀ c : K,c≠0 → Nonempty (ParameterFiber Q w c ≃ₐ[K] S)

/-- The original good coordinates, as actual degree-one global sections. -/
def oddSectionGoodMap (k t : ℕ) (hs : t+2≤k+1) :
    MvPolynomial (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) K →ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).toAlgHom.comp (oddGoodMap (K := K) k t hs)

theorem oddSectionGoodMap_surjective (k t : ℕ) (hs : t+2≤k+1) :
    Function.Surjective (oddSectionGoodMap (K := K) k t hs) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).surjective.comp (oddGoodMap_surjective k t hs)

theorem oddSectionGoodMap_kernel (k t : ℕ) (hs : t+2≤k+1) :
    RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
      oddGoodIdeal (K := K) k t hs := by
  ext p
  change oddCompleteSectionRingEquiv (K := K) k t hs (oddGoodMap (K := K) k t hs p)=0 ↔
    oddGoodMap (K := K) k t hs p=0
  exact (oddCompleteSectionRingEquiv (K := K) k t hs).map_eq_zero_iff

theorem oddSectionGoodMap_coordinate (k t : ℕ) (hs : t+2≤k+1)
    (I : Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) :
    oddSectionGoodMap (K := K) k t hs (X I)=
      DirectSum.of (fun d ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) d)) 1
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (1 : ℤ)=1) ⊤
          ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩) :=
  oddCompleteSectionRingEquiv_homogeneous k t hs 1
    ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩

theorem oddSectionGoodMap_quadratic (k t : ℕ) (hs : t+2≤k+1) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom) := by
  rw [oddSectionGoodMap_kernel]
  exact (odd_higherPlane_conclusions k t hs).quadratic

theorem odd_section_richardson_flat (k t : ℕ) (hs : t+2≤k+1) :
    WeightedFlatDegenerationTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
        (oddIntervalUpper k (t+2) hs))
      (SectionRing (oddProjectiveGrading (K := K) k t)) :=
  ⟨(odd_richardson_flat_family k t hs).1,
    (odd_richardson_flat_family k t hs).2.1,
    fun c hc ↦ ⟨(oddRichardsonNonzeroFiberEquiv k t c hc).trans
      (oddCompleteSectionRingEquiv (K := K) k t hs)⟩⟩

/-- The actual one-plane coordinate sections. -/
def onePlaneSectionCoordinateMap (k : ℕ) :
    MvPolynomial (PluckerIndex 1 (2*k+1)) K →ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).toAlgHom.comp
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal)

theorem onePlaneSectionCoordinateMap_surjective (k : ℕ) :
    Function.Surjective (onePlaneSectionCoordinateMap (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).surjective.comp Ideal.Quotient.mk_surjective

set_option maxHeartbeats 800000 in
theorem onePlaneSectionCoordinateMap_kernel (k : ℕ) :
    RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
      matrixPluckerIdeal := by
  change RingHom.ker
    ((onePlaneCompleteSectionRingEquiv (K := K) k).toRingHom.comp
      (Ideal.Quotient.mk matrixPluckerIdeal))=matrixPluckerIdeal
  exact (RingHom.ker_comp_of_injective (Ideal.Quotient.mk matrixPluckerIdeal)
    (onePlaneCompleteSectionRingEquiv (K := K) k).injective).trans Ideal.mk_ker

theorem onePlaneSectionCoordinateMap_quadratic (k : ℕ) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom) := by
  rw [onePlaneSectionCoordinateMap_kernel]
  exact (odd_onePlane_conclusions k).quadratic

theorem onePlane_section_richardson_flat (k : ℕ) :
    WeightedFlatDegenerationTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))
      (SectionRing (onePlaneProjectiveGrading (K := K) k)) :=
  ⟨(odd_onePlane_conclusions k).richardson.1,
    (odd_onePlane_conclusions k).richardson.2.1,
    fun c hc ↦ ⟨(nonzeroFiberEquiv _ _ c hc).trans
      (onePlaneCompleteSectionRingEquiv (K := K) k)⟩⟩

/-- The one-plane boundary, now including the actual complete section
algebra and its actual ordinary Tor in every internal degree. -/
structure OddOnePlaneSectionConclusions (k : ℕ) : Prop where
  original : OddOnePlaneConclusions (K := K) k
  complete : Nonempty
    (OnePlaneKoszul.Ring K (2*k+1) ≃ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k))
  degree_comparison : ∀ d (r : onePlaneProjectiveGrading (K := K) k d),
    onePlaneCompleteSectionRingEquiv (K := K) k r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (onePlaneProjectiveGrading (K := K) k) j)) d
        (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
          (rfl : (d : ℤ)=d) ⊤ r)
  charts : ∀ p : PluckerIndex 1 (2*k+1),Nonempty
    ((Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)))
  cover : (⨆ p : PluckerIndex 1 (2*k+1),
    Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p)))=⊤
  coordinates : Function.Surjective (onePlaneSectionCoordinateMap (K := K) k)
  coordinate_kernel : RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
    matrixPluckerIdeal
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (SectionRing (onePlaneProjectiveGrading (K := K) k))
  tor_exhaustive : ∀ r,(⨆ N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N)=⊤
  koszul : ∀ r N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N=
    if N=r then ⊤ else ⊥

theorem odd_onePlane_section_conclusions (k : ℕ) :
    OddOnePlaneSectionConclusions (K := K) k :=
  ⟨odd_onePlane_conclusions k,⟨onePlaneCompleteSectionRingEquiv (K := K) k⟩,
    onePlaneCompleteSectionRingEquiv_homogeneous k,
    fun p ↦ ⟨onePlaneProjBasicOpenIso k p⟩,onePlaneProjBasicOpen_cover k,
    onePlaneSectionCoordinateMap_surjective k,onePlaneSectionCoordinateMap_kernel k,
    onePlaneSectionCoordinateMap_quadratic k,onePlane_section_richardson_flat k,
    OnePlaneSectionKoszul.torInternalPieces_iSup k,
    OnePlaneSectionKoszul.actual_section_Tor_internal_degree k⟩

/-- Every higher positive plane dimension, including the maximal singleton
interval, with the actual original scheme and actual complete section algebra. -/
structure OddHigherPlaneSectionConclusions (k t : ℕ) (hs : t+2≤k+1) : Prop where
  original : OddHigherPlaneConclusions (K := K) k t hs
  exact_equations : NormalizedHomogeneousProjOverlap.equationIdeal
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k))=
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
  same_scheme : Proj (NormalizedHomogeneousProjOverlap.grading
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)))=
      Proj (oddProjectiveGrading (K := K) k t)
  charts : ∀ p : PluckerIndex (t+2) (2*k+1),Nonempty
    ((Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p (oddPluckerForms (K := K) k))))
  cover : (⨆ p : PluckerIndex (t+2) (2*k+1),
    Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p)))=⊤
  genuine_transitions : ∀ p q : PluckerIndex (t+2) (2*k+1),
    NormalizedHomogeneousProjOverlap.actualTransition
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q=
      (NormalizedHomogeneousChart.transitionHom
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q).toRingHom
  complete : Nonempty
    ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) ≃ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t))
  degree_comparison : ∀ d (r : oddProjectiveGrading (K := K) k t d),
    oddCompleteSectionRingEquiv (K := K) k t hs r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) j)) d
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (d : ℤ)=d) ⊤ r)
  coordinates : Function.Surjective (oddSectionGoodMap (K := K) k t hs)
  coordinate_kernel : RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
    oddGoodIdeal (K := K) k t hs
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs))
    (SectionRing (oddProjectiveGrading (K := K) k t))
  residue_field : Nonempty
    (BarFree.Residue (oddSectionAugmentation (K := K) k t hs) ≃ₐ[K] K)
  tor_exhaustive : ∀ r,(⨆ N,oddSectionTorInternalPiece (K := K) k t hs r N)=⊤
  koszul : ∀ r N,oddSectionTorInternalPiece (K := K) k t hs r N=
    if N=r then ⊤ else ⊥

theorem odd_higherPlane_section_conclusions (k t : ℕ) (hs : t+2≤k+1) :
    OddHigherPlaneSectionConclusions (K := K) k t hs :=
  ⟨odd_higherPlane_conclusions k t hs,
    isotropicHomogeneousSystem_ideal_eq (oddPluckerForms (K := K) k),
    isotropicHomogeneousSystem_projectiveScheme_eq (oddPluckerForms (K := K) k),
    fun p ↦ ⟨isotropicProjBasicOpenIso p (oddPluckerForms (K := K) k)⟩,
    isotropicProjBasicOpen_cover (oddPluckerForms (K := K) k),
    NormalizedHomogeneousProjOverlap.actualTransition_eq_transitionHom _,
    ⟨oddCompleteSectionRingEquiv (K := K) k t hs⟩,
    oddCompleteSectionRingEquiv_homogeneous k t hs,
    oddSectionGoodMap_surjective k t hs,oddSectionGoodMap_kernel k t hs,
    oddSectionGoodMap_quadratic k t hs,odd_section_richardson_flat k t hs,
    ⟨oddSectionResidueEquivField k t hs⟩,
    oddSectionTorInternalPieces_iSup k t hs,oddSection_actual_Tor_internal_degree k t hs⟩

/-- The literal full positive plane range. The excluded zero-plane case
is false and is never used by the positive-range theorem. -/
def OddCompleteSectionConclusions (k s : ℕ) (hs : s≤k+1) : Prop :=
  match s,hs with
  | 0,_ => False
  | 1,_ => OddOnePlaneSectionConclusions (K := K) k
  | t+2,h => OddHigherPlaneSectionConclusions (K := K) k t h

theorem odd_all_positive_section_conclusions (k s : ℕ)
    (hpos : 0<s) (hs : s≤k+1) : OddCompleteSectionConclusions (K := K) k s hs := by
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ s =>
    cases s with
    | zero => exact odd_onePlane_section_conclusions k
    | succ t => exact odd_higherPlane_section_conclusions k t hs

/-- The complete all-degree exterior-basis and all-positive-plane theorem,
with the literal complete section-ring form of every algebraic clause. -/
theorem paper_theorem_1_3_complete_section_ring (k : ℕ) :
    (∀ s,∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2*k+1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0<s) (hs : s≤k+1),OddCompleteSectionConclusions (K := K) k s hs) :=
  ⟨paper_theorem_1_3_exterior_basis k,odd_all_positive_section_conclusions k⟩

end PaperVerification.AlternatingForms

module

public import PaperVerification.AlternatingFormsOddExteriorBasis
public import PaperVerification.AlternatingFormsOddFlatFamily
public import PaperVerification.AlternatingFormsHibiDegeneration
public import PaperVerification.AlternatingFormsOddGroebner
public import PaperVerification.AlternatingFormsOddTorPure
public import PaperVerification.AlternatingFormsOnePlaneDegreeFaithfulness
public import PaperVerification.AlternatingFormsChartConverse
public import PaperVerification.AlternatingFormsConnectedGrading
public import PaperVerification.AlternatingFormsOddPrime
public import PaperVerification.AlternatingFormsOddIndexCorrespondence

/-!
# The full all-degree and all-plane statement of Theorem 1.3

The exterior-basis clause includes every degree, including degrees zero and
one and the vanishing range.  The geometric and algebraic clauses include
every `1 ≤ s ≤ k+1`.  The one-plane case is the actual polynomial Plücker
ring; the remaining cases use `s=t+2`, with no restriction on `t`.

The word Koszul has its standard homological meaning here: the actual
ordinary Tor of the augmentation residue is concentrated in internal degree
equal to homological degree.  The residue is proved isomorphic to the
coefficient field, and the internal pieces come from the original polynomial
grading.  Connectedness, degree compatibility, and exhaustion are included
explicitly below.  No separately constructed minimal linear resolution is
claimed.  The coordinate-chart equivalence retains the actual isotropy ideal
and its scheme structure.  Primality and irrelevant-ideal saturation exclude
any hidden homogeneous torsion.  The two flat families are the actual weighted Rees
images, with all nonzero fibers identified.

This assembly is a proof candidate until its complete source closure and
actual theorem bodies have passed the compiler and independent audit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber

universe u v
variable {K : Type u} [Field K] [CharZero K]

/-- Flatness and the exact special and nonzero fibers of the literal weighted
Rees image.  Both endpoint rings retain their displayed polynomial ideals. -/
def WeightedFlatDegeneration {σ τ : Type*}
    (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ)
    (J : Ideal (MvPolynomial τ K)) : Prop :=
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧
  Nonempty (ZeroFiber Q w ≃ₐ[K] (MvPolynomial τ K⧸J)) ∧
  ∀ c : K,c≠0 → Nonempty (ParameterFiber Q w c ≃ₐ[K] (MvPolynomial σ K⧸Q))

/-- The usual finite homogeneous-quadratic Gröbner property of the literal
kernel in the displayed coordinate variables. -/
def HasQuadraticGroebnerBasis {σ : Type v} (Q : Ideal (MvPolynomial σ K)) : Prop :=
  ∃ (m : MonomialOrder.{v,v} σ) (S : Set (MvPolynomial σ K)),
    S.Finite ∧ (∀ p∈S,p.IsHomogeneous 2) ∧ m.IsGroebnerBasis S Q

/-- For one-planes every coordinate lies in the printed interval `[0,2k]`.
Thus the Richardson ideal is exactly the original one-plane Plücker ideal. -/
theorem onePlane_odd_intervalIdeal (k : ℕ) (hs : 1≤k+1) :
    intervalPluckerIdeal (K := K) (oddIntervalLower k 1 hs)
      (oddIntervalUpper k 1 hs)=matrixPluckerIdeal := by
  have hspan : Ideal.span
      {p | ∃ I : PluckerIndex 1 (2*k+1),
        (¬∀ i,oddIntervalLower k 1 hs i≤I.val i ∧
          I.val i≤oddIntervalUpper k 1 hs i) ∧ p=X I}=
      (⊥ : Ideal (MvPolynomial (PluckerIndex 1 (2*k+1)) K)) := by
    apply le_antisymm ?_ bot_le
    apply Ideal.span_le.mpr
    rintro p ⟨I,hI,hp⟩
    exact False.elim (hI (by
      intro i
      have hi : i.val=0 := by omega
      constructor
      · change 2*i.val≤(I.val i).val
        omega
      · change (I.val i).val≤2*(k+1-1+i.val)
        have hlt := (I.val i).isLt
        omega))
  rw [intervalPluckerIdeal,hspan,sup_bot_eq]

theorem onePlane_odd_richardson_flat (k : ℕ) (hs : 1≤k+1) :
    WeightedFlatDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k 1 hs) (oddIntervalUpper k 1 hs)) := by
  rw [onePlane_odd_intervalIdeal]
  exact onePlane_flat_family _

def onePlaneCoefficientAugmentation (n : ℕ) :
    OnePlaneKoszul.Ring K n →ₐ[K] K :=
  (aeval (fun _ : Fin n ↦ (0 : K))).comp
    (OnePlaneKoszul.polynomialEquiv K n).toAlgHom

set_option synthInstance.maxHeartbeats 80000 in
/-- All clauses for the one-plane boundary.  In particular, the empty
quadratic Gröbner basis is a basis of a proved zero kernel, and the Tor
grading is linked to the original homogeneous coordinates and differential. -/
structure OddOnePlaneConclusions (k : ℕ) : Prop where
  prime : (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)).IsPrime
  saturated : IsSaturatedWithRespectTo
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerIrrelevantIdeal 1 (2*k+1))
  richardson : WeightedFlatDegeneration
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
  hibi : WeightedFlatDegeneration
    (Hibi.goodBandIdeal (K := K) (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (Hibi.diagonalWeight (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (Hibi.relationIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
  hibi_original_fibers : ∀ c : K,c≠0 → Nonempty
    (ParameterFiber
      (Hibi.goodBandIdeal (K := K) (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))
      (Hibi.diagonalWeight (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex 1 (2*k+1)) K⧸
        intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
          (oddIntervalUpper k 1 (by omega))))
  quadratic : HasQuadraticGroebnerBasis
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
  connected : HomogeneousIdealPieces.piece
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) 0=
      (1 : Submodule K (OnePlaneKoszul.Ring K (2*k+1)))
  scalars : Function.Injective (algebraMap K (OnePlaneKoszul.Ring K (2*k+1)))
  grading : Nonempty {G : TauCeti.InternalGrading K (OnePlaneKoszul.Ring K (2*k+1)) ℕ //
    ∀ N,G.piece N=OnePlaneKoszul.originalDegree K (2*k+1) N}
  degree_mul : ∀ i j (x y : OnePlaneKoszul.Ring K (2*k+1)),
    x∈OnePlaneKoszul.originalDegree K (2*k+1) i →
    y∈OnePlaneKoszul.originalDegree K (2*k+1) j →
    x*y∈OnePlaneKoszul.originalDegree K (2*k+1) (i+j)
  residue_field : Nonempty (OnePlaneKoszul.Residue K (2*k+1) ≃ₐ[K] K)
  original_degree : ∀ N,
    BasisDegree.piece (OnePlaneKoszul.coordinateBasis K (2*k+1)) Finsupp.degree N=
      OnePlaneKoszul.originalDegree K (2*k+1) N
  differential_degree : ∀ r N (z : OnePlaneKoszul.freeTermOverK K (2*k+1) (r+1)),
    z∈(OnePlaneKoszul.freeGrading K (2*k+1) (r+1)).piece N →
      OnePlaneKoszul.differentialOverK K (2*k+1) r z∈
        (OnePlaneKoszul.freeGrading K (2*k+1) r).piece N
  koszul : ∀ r N,
    (OnePlaneKoszul.torGrading K (2*k+1) r).piece N=if N=r then ⊤ else ⊥

theorem odd_onePlane_conclusions (k : ℕ) : OddOnePlaneConclusions (K := K) k := by
  let hs : 1≤k+1 := by omega
  let α := oddIntervalLower k 1 hs
  let β := oddIntervalUpper k 1 hs
  refine ⟨onePlane_ideal_isPrime (2*k+1),onePlane_PluckerIdeal_saturated k,
    onePlane_odd_richardson_flat k hs,?_,?_,?_,
    homogeneousQuotient_degree_zero _,
    augmentedQuotient_scalar_injective _ (onePlaneCoefficientAugmentation (2*k+1)),
    ⟨⟨HomogeneousIdealPieces.grading _
      (OnePlaneKoszul.onePlaneIdeal_isHomogeneous K (2*k+1)),
      HomogeneousIdealPieces.grading_piece _ _⟩⟩,
    homogeneousQuotient_mul_mem _,⟨OnePlaneKoszul.residueEquivField K (2*k+1)⟩,
    OnePlaneKoszul.coefficientDegree_eq_originalDegree K (2*k+1),
    OnePlaneKoszul.differentialOverK_homogeneous K (2*k+1),
    OnePlaneKoszul.actual_onePlane_Tor_degree K (2*k+1)⟩
  · exact ⟨inferInstance,
      ⟨Hibi.hibiSpecialFiberEquiv α β
        (oddIntervalLower_strictMono k 1 hs).monotone
        (oddIntervalUpper_strictMono k 1 hs).monotone (by decide)⟩,
      fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  · intro c hc
    exact ⟨Hibi.hibiNonzeroFiberEquiv α β
      (oddIntervalLower_strictMono k 1 hs).monotone
      (oddIntervalUpper_strictMono k 1 hs).monotone (by decide) c hc⟩
  · exact ⟨WeightedMonomialOrder.finiteBaseOrder (PluckerIndex 1 (2*k+1)),∅,
      onePlane_quadratic_groebner _⟩

/-- The remaining cases use the original common-isotropic ring and its
original good-coordinate presentation.  The chart clause identifies its
literal equations with row isotropy, rather than postulating a geometric
interpretation.  The Tor pieces are the images of the original homogeneous
bar subcomplexes inside ordinary Mathlib Tor. -/
structure OddHigherPlaneConclusions (k t : ℕ) (hs : t+2≤k+1) : Prop where
  prime : (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime
  saturated : IsSaturatedWithRespectTo
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (pluckerIrrelevantIdeal (t+2) (2*k+1))
  charts : ∀ p : PluckerIndex (t+2) (2*k+1),Nonempty
    ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      (isotropicPluckerIdeal (t := t) (oddPluckerForms k) ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K⧸
        isotropicChartIdeal p (oddPluckerForms k)))
  richardson : WeightedFlatDegeneration
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
  hibi : WeightedFlatDegeneration
    (Hibi.goodBandIdeal (K := K) (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs))
    (Hibi.diagonalWeight (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
    (Hibi.relationIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
  hibi_original_fibers : ∀ c : K,c≠0 → Nonempty
    (ParameterFiber
      (Hibi.goodBandIdeal (K := K) (oddIntervalLower k (t+2) hs)
        (oddIntervalUpper k (t+2) hs))
      (Hibi.diagonalWeight (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)))
  good_coordinates : Nonempty
    ((MvPolynomial
      (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) K⧸
      oddGoodIdeal k t hs) ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  quadratic : HasQuadraticGroebnerBasis (oddGoodIdeal (K := K) k t hs)
  connected : oddPluckerDegree (K := K) k t 0=
    (1 : Submodule K (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  scalars : Function.Injective (algebraMap K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  grading : Nonempty {G : TauCeti.InternalGrading K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms k)) ℕ //
    ∀ N,G.piece N=oddPluckerDegree (K := K) k t N}
  degree_mul : ∀ i j (x y : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)),
    x∈oddPluckerDegree k t i → y∈oddPluckerDegree k t j →
      x*y∈oddPluckerDegree k t (i+j)
  residue_field : Nonempty (BarFree.Residue (oddAugmentation (K := K) k t) ≃ₐ[K] K)
  tor_exhaustive : ∀ r,(⨆ N,oddTorInternalPiece (K := K) k t hs r N)=⊤
  koszul : ∀ r N,oddTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥

theorem odd_higherPlane_conclusions (k t : ℕ) (hs : t+2≤k+1) :
    OddHigherPlaneConclusions (K := K) k t hs := by
  let α := oddIntervalLower k (t+2) hs
  let β := oddIntervalUpper k (t+2) hs
  refine ⟨odd_isotropicPluckerIdeal_isPrime k t hs,
    odd_isotropicPluckerIdeal_saturated k t hs,
    fun p ↦ ⟨isotropicPluckerBigCellEquiv p (oddPluckerForms k)⟩,
    odd_richardson_flat_family k t hs,?_,?_,⟨oddGoodQuotientEquiv k t hs⟩,?_,
    homogeneousQuotient_degree_zero _,
    augmentedQuotient_scalar_injective _ (oddAugmentation k t),
    ⟨⟨HomogeneousIdealPieces.grading _ (isotropicPluckerIdeal_isHomogeneous _),
      HomogeneousIdealPieces.grading_piece _ _⟩⟩,
    homogeneousQuotient_mul_mem _,⟨BarFree.residueEquivCoefficients (oddAugmentation k t)⟩,
    oddTorInternalPieces_iSup k t hs,odd_actual_Tor_internal_degree k t hs⟩
  · exact ⟨inferInstance,
      ⟨Hibi.hibiSpecialFiberEquiv α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)⟩,
      fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  · intro c hc
    exact ⟨Hibi.hibiNonzeroFiberEquiv α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) c hc⟩
  · obtain ⟨m,hm⟩ := odd_good_exists_quadratic_groebner (K := K) k t hs
    exact ⟨m,oddQuadraticSet k t hs,hm⟩

/-- A literal case split on the requested plane dimension.  Degree zero
is outside the geometric clause; the theorem below assumes `0<s` and hence
never proves that branch.  Every positive dimension occurs in exactly one
of the actual one-plane or higher-plane statements above. -/
def OddPluckerConclusions (k s : ℕ) (hs : s≤k+1) : Prop :=
  match s,hs with
  | 0,_ => False
  | 1,_ => OddOnePlaneConclusions (K := K) k
  | t+2,h => OddHigherPlaneConclusions (K := K) k t h

theorem odd_all_positive_plane_conclusions (k s : ℕ)
    (hpos : 0<s) (hs : s≤k+1) : OddPluckerConclusions (K := K) k s hs := by
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ s =>
    cases s with
    | zero => exact odd_onePlane_conclusions k
    | succ t => exact odd_higherPlane_conclusions k t hs

/-- All clauses of Theorem 1.3 for the canonical odd pencil, over every
characteristic-zero field, every odd dimension `2*k+1`, every exterior degree,
and the complete positive range `1≤s≤k+1` for the two degenerations, quadratic
Gröbner presentation and homological Koszul assertion. -/
theorem paper_theorem_1_3 (k : ℕ) :
    (∀ s,∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2*k+1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0<s) (hs : s≤k+1),OddPluckerConclusions (K := K) k s hs) :=
  ⟨paper_theorem_1_3_exterior_basis k,odd_all_positive_plane_conclusions k⟩

end PaperVerification.AlternatingForms

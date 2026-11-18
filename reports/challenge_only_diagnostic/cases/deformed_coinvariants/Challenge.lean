module
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
/-!
# Coinvariants of weighted differential power operators
The joint image is the vector-space sum of the actual differential-operator
images. The selected statements include the exact Hivert--Thiery basis and
graded representation range, the complete weighted-tail theorem, weighted
Jacobian equality, isolated-hypersurface resonant defects and arbitrary
homogeneous Milnor-basis lifts, their finite-group equivariant decomposition
and homogeneous splitting, and the complete-intersection scalar and all-group
equivariant defect statements. All quotient spaces, operators, gradings and
actual coefficient subalgebras are explicit below. Sections marked incomplete
in the retained README remain unformalized; this selection makes no claim about
their unresolved conclusions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators
namespace PaperVerification.EulerJacobian
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
/-- The degrees of nonzero homogeneous polynomials, namely the paper's set `S`. -/ def occurringDegrees (w : ι → ℕ) : Set ℕ :=
  {d | ∃ f : MvPolynomial ι K, f ≠ 0 ∧ f.IsWeightedHomogeneous w d}
end PaperVerification.EulerJacobian
namespace PaperVerification.VectorJacobian
open scoped BigOperators
open MvPolynomial
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Contraction with every row of the ordinary polynomial Jacobian. -/ def jacobianMap (F : κ → P) : (ι → P) →ₗ[K] (κ → P) where
  toFun g a := ∑ i, pderiv i (F a) * g i
  map_add' g h := by
    funext a
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext a
    simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm, Finset.smul_sum]
/-- The paper's normalized rows; scaling by nonzero degrees preserves the actual kernel. -/ def normalizedJacobianMap (F : κ → P) (h : κ → ℕ) :
    (ι → P) →ₗ[K] (κ → P) where
  toFun g a := (h a : K)⁻¹ • jacobianMap F g a
  map_add' g g' := by
    funext a
    simp only [map_add, Pi.add_apply, smul_add]
  map_smul' c g := by
    funext a
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_comm c]
end PaperVerification.VectorJacobian
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
local instance vectorEulerBasicDecidableEq : DecidableEq ι := Classical.decEq ι
/-- Literal PaperVerification.VectorEuler.coefficientSpace; precise source and scope recorded in the extraction map. -/ def coefficientSpace (F : κ → P) (h : κ → ℕ) : Submodule K M :=
  LinearMap.range (VectorJacobian.normalizedJacobianMap F h)
end PaperVerification.VectorEuler
namespace PaperVerification.EulerReduction
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
/-- The full differential perturbation of a coefficient map. -/ def perturbed (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) : U →ₗ[K] V :=
  C + t • (L.comp D)
end PaperVerification.EulerReduction
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- The usual divergence of a polynomial vector field. -/ def divergence : (ι → P) →ₗ[K] P where
  toFun g := ∑ i, pderiv i (g i)
  map_add' g h := by simp [Finset.sum_add_distrib]
  map_smul' a g := by simp [Finset.smul_sum]
end PaperVerification.JacobianDivergence
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
attribute [local instance] PaperVerification.VectorEuler.vectorEulerBasicDecidableEq
/-- Multiplication by the entire vector of defining equations. -/ def potential (F : κ → P) : P →ₗ[K] M where
  toFun p a := F a * p
  map_add' p q := by funext a; exact mul_add _ _ _
  map_smul' c p := by funext a; exact mul_smul_comm _ _ _
/-- Literal PaperVerification.VectorEuler.aggregate; precise source and scope recorded in the extraction map. -/ def aggregate (F : κ → P) (h : κ → ℕ) (t : K) : (ι → P) →ₗ[K] M :=
  EulerReduction.perturbed (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (potential F) t
/-- Literal PaperVerification.VectorEuler.hit; precise source and scope recorded in the extraction map. -/ def hit (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K M :=
  LinearMap.range (aggregate F h t)
/-- Literal PaperVerification.VectorEuler.Defect; precise source and scope recorded in the extraction map. -/ abbrev Defect (F : κ → P) (h : κ → ℕ) (t : K) :=
  coefficientSpace F h ⧸ (hit F h t).comap (coefficientSpace F h).subtype
/-- Literal PaperVerification.VectorEuler.defectImage; precise source and scope recorded in the extraction map. -/ def defectImage (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K (M ⧸ hit F h t) :=
  (coefficientSpace F h).map (hit F h t).mkQ
end PaperVerification.VectorEuler
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
/-- Literal PaperVerification.VectorEuler.integerWeights; precise source and scope recorded in the extraction map. -/ def integerWeights (w : ι → ℕ) : ι → ℤ := fun i => (w i : ℤ)
/-- This is the paper's literal target grading, including negative degrees. -/ def targetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) : Submodule K M :=
  Submodule.pi Set.univ fun a =>
    weightedHomogeneousSubmodule K (integerWeights w) (e + (h a : ℤ))
/-- Literal PaperVerification.VectorEuler.quotientTargetPiece; precise source and scope recorded in the extraction map. -/ def quotientTargetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (U : Submodule K M) :
    Submodule K (M ⧸ U) := (targetPiece w h e).map U.mkQ
end PaperVerification.VectorEuler
namespace PaperVerification.VectorEuler
open MvPolynomial RingTheory.Sequence
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
/-- All scalar claims of Proposition 6.5. The coefficient identity is stated for every integer target degree, so it is precisely the Laurent Hilbert-series identity even when the baseline has nonzero negative-degree components. -/ theorem paper_proposition_6_5_scalar (hn : 0 < n)
    (F : Fin n → P) (h w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F)) :
    (∀ t : K, hit F h t ≤ coefficientSpace F h) ∧
    (∀ t : K, hit F h t ≠ coefficientSpace F h ↔
      ∃ d ∈ EulerJacobian.occurringDegrees (K := K) w,
        t = -(1 : K) / ((∑ i, w i : ℕ) + d : K)) ∧
    (∀ d : ℕ,
      let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
      Nonempty (weightedHomogeneousSubmodule K w d ≃ₗ[K] Defect F h t) ∧
      defectImage F h t ≤ quotientTargetPiece w h (d : ℤ) (hit F h t) ∧
      ∀ e : ℤ,
        Module.finrank K (quotientTargetPiece w h e (hit F h t)) =
          Module.finrank K (quotientTargetPiece w h e (coefficientSpace F h)) +
            if e = (d : ℤ) then Module.finrank K (weightedHomogeneousSubmodule K w d) else 0) := by sorry
end PaperVerification.VectorEuler
namespace MvPolynomial
open Matrix MulOpposite
variable {σ R : Type*} [Fintype σ] [CommSemiring R]
/-- The linear change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` given by a square matrix `M`. -/ noncomputable def linearSubst (M : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ ∑ j, C (M i j) * X j
end MvPolynomial
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
variable {D : Type*} [AddCommMonoid D]
/-- A matrix preserves the prescribed grading exactly when each nonzero entry mixes variables of the same weight. -/ def RespectsWeights (w : ι → D) (M : Matrix ι ι K) : Prop :=
  ∀ i j, M i j ≠ 0 → w i = w j
end PaperVerification.JacobianLinearAction
namespace PaperVerification.VectorEuler
open MvPolynomial RingTheory.Sequence
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
/-- The same canonical equivalence is an isomorphism for every actual linear group fixing every equation and preserving its positive grading. In particular this includes every finite linear group in the paper; finiteness is unnecessary for this canonical defect map. -/ theorem paper_proposition_6_5_equivariant {G : Type*} [Group G]
    (hn : 0 < n) (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F))
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K))
    (hFix : ∀ g a, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) (F a) = F a)
    (g : G) (p : weightedHomogeneousSubmodule K w d) :
    let t : K := by sorry
end PaperVerification.VectorEuler
namespace PaperVerification.EulerJacobian
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
/-- Literal PaperVerification.EulerJacobian.Poly; precise source and scope recorded in the extraction map. -/ abbrev Poly := MvPolynomial ι K
/-- The actual first-order operator, with multiplication on the displayed side. -/ def operator (A : ι → Poly (K := K) (ι := ι)) (F : Poly (K := K) (ι := ι)) (t : K)
    (i : ι) (g : Poly (K := K) (ι := ι)) : Poly (K := K) (ι := ι) :=
  A i * g + t • (F * pderiv i g)
/-- A vector-space sum of images; it is deliberately not defined as an ideal. -/ def hit (A : ι → Poly (K := K) (ι := ι)) (F : Poly (K := K) (ι := ι)) (t : K) :
    Submodule K (Poly (K := K) (ι := ι)) :=
  Submodule.span K {f | ∃ i g, f = operator A F t i g}
/-- The ordinary polynomial ideal generated by the multiplication coefficients. -/ def coefficientIdeal (A : ι → Poly (K := K) (ι := ι)) : Ideal (Poly (K := K) (ι := ι)) :=
  Ideal.span (Set.range A)
/-- The exact complex-polynomial statement of Theorem 6.2, including all variable counts; the positive-degree hypothesis itself excludes the empty variable set. -/ theorem paper_theorem_6_2 (N : ℕ) (F : MvPolynomial (Fin N) ℂ) (t : ℂ) (w : Fin N → ℕ) (h : ℕ) (hne : F ≠ 0) (hw : ∀ i, 0 < w i)
  (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) (hnr : ∀ d ∈ occurringDegrees (K := ℂ) w, t ≠ -(h : ℂ) / ((∑ i, w i : ℕ) + d :
  ℂ)) : hit (fun i => pderiv i F) F t = (coefficientIdeal (fun i => pderiv i F)).restrictScalars ℂ := by sorry
end PaperVerification.EulerJacobian
namespace PaperVerification.EulerResonance
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- The actual degree-`d` part of a polynomial quotient, presented as an image. -/ def quotientComponent (w : ι → ℕ) (d : ℕ) (U : Submodule K P) :
    Submodule K (P ⧸ U) :=
  LinearMap.range (U.mkQ.comp (weightedHomogeneousComponent w d))
end PaperVerification.EulerResonance
namespace TauCeti
open scoped DirectSum
universe u v w
variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
/-- An internal grading of an `R`-module `M` indexed by `ι`, with integer degrees by default. The `isInternal` field says that the canonical map from the external direct sum of the `piece p` to `M` is bijective. Thus elements of `M` have unique finite homogeneous decompositions. The index equality instance is required by Mathlib's `DirectSum.IsInternal` and `DirectSum.Decomposition`. For an index type without a computable equality instance, use `classical` locally to supply it; no computability assumption on the index type is needed. -/ structure InternalGrading (ι : Type := ℤ) [DecidableEq ι] where
  /-- The submodule of elements of degree `p`. -/
  piece : ι → Submodule R M
  /-- The homogeneous pieces form an internal direct sum. -/
  isInternal : DirectSum.IsInternal piece
end TauCeti
namespace PaperVerification.GradedTowers
open scoped DirectSum
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {G : Type*} [Monoid G]
/-- The natural restriction of a graded representation to one actual piece. -/ def pieceRepresentation (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (p : ℤ) :
    Representation K G (GW.piece p) :=
  σ.subrepresentation (GW.piece p) (fun g x hx => hσ g p x hx)
/-- The actual direct-sum representation on every shifted homogeneous piece. The index set is all natural numbers; no bound is imposed on the sum. -/ def shiftedPiecesRepresentation (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (h : ℕ) (p : ℤ) :
    Representation K G (⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) :=
  Representation.directSum fun j : ℕ => pieceRepresentation GW σ hσ (p + (j : ℤ) * h)
end PaperVerification.GradedTowers
namespace PaperVerification.HilbertTowerCount
variable {I : Type*}
/-- Literal PaperVerification.HilbertTowerCount.geometricInverse; precise source and scope recorded in the extraction map. -/ def geometricInverse (h : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (1 - PowerSeries.X ^ h) 1
end PaperVerification.HilbertTowerCount
namespace PaperVerification.PowerOperators
open MvPolynomial Matrix Representation
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R
/-- Literal PaperVerification.PowerOperators.ordinaryFamilyIdeal; precise source and scope recorded in the extraction map. -/ def ordinaryFamilyIdeal (f : Fin n → P) : Ideal P := Ideal.span (Set.range f)
/-- Literal PaperVerification.PowerOperators.rename_mem_ordinaryFamilyIdeal; precise source and scope recorded in the extraction map. -/ theorem rename_mem_ordinaryFamilyIdeal (e : Equiv.Perm (Fin n)) (f : Fin n → P) (hf : ∀ i, MvPolynomial.rename e (f i) = f i) {p :
  P} (hp : p ∈ ordinaryFamilyIdeal f) : MvPolynomial.rename e p ∈ ordinaryFamilyIdeal f := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Matrix Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
/-- Literal PaperVerification.PowerOperators.ordinaryQuotientDegree; precise source and scope recorded in the extraction map. -/ def ordinaryQuotientDegree (f : Fin n → P) (d : ℕ) : Submodule K (P ⧸ ordinaryFamilyIdeal f) :=
  (homogeneousSubmodule (Fin n) K d).map ((ordinaryFamilyIdeal f).mkQ.restrictScalars K)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.polynomialPermutationAction; precise source and scope recorded in the extraction map. -/ def polynomialPermutationAction (R : Type*) [CommRing R]
    (G : Subgroup (Equiv.Perm (Fin n))) :
    Representation R G (MvPolynomial (Fin n) R) where
  toFun g := (MvPolynomial.rename (g : Equiv.Perm (Fin n))).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    exact MvPolynomial.rename_id_apply p
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change MvPolynomial.rename (↑(g*h) : Equiv.Perm (Fin n)) p =
      MvPolynomial.rename (g : Equiv.Perm (Fin n))
        (MvPolynomial.rename (h : Equiv.Perm (Fin n)) p)
    rw [MvPolynomial.rename_rename]
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul]
end PaperVerification.PowerOperators
namespace PaperVerification.QuotientLinearAction
variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
/-- Literal PaperVerification.QuotientLinearAction.action; precise source and scope recorded in the extraction map. -/ def action (ρ : G →* Module.End K V) (U : Submodule K V)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) : G →* Module.End K (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (fun _ hx => hU g _ hx)
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := U.mkQ_surjective z
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := U.mkQ_surjective z
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul, Module.End.mul_apply]
end PaperVerification.QuotientLinearAction
namespace PaperVerification.PowerOperators
open MvPolynomial Matrix Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
/-- Literal PaperVerification.PowerOperators.ordinaryQuotientAction; precise source and scope recorded in the extraction map. -/ def ordinaryQuotientAction (G : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → P)
    (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i) :
    Representation K G (P ⧸ ordinaryFamilyIdeal f) := by
  refine QuotientLinearAction.action (polynomialPermutationAction K G)
    ((ordinaryFamilyIdeal f).restrictScalars K) ?_
  intro g p hp
  change MvPolynomial.rename (g : Equiv.Perm (Fin n)) p ∈ ordinaryFamilyIdeal f
  exact rename_mem_ordinaryFamilyIdeal (g : Equiv.Perm (Fin n)) f (hinv g) hp
end PaperVerification.PowerOperators
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- The actual polynomial gradient. -/ def gradient (F : P) : ι → P := fun i => pderiv i F
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.jacobianSubmodule; precise source and scope recorded in the extraction map. -/ def jacobianSubmodule (F : P) : Submodule K P :=
  (Ideal.span (Set.range (gradient F))).restrictScalars K
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.homogeneousComponent_mem_jacobian; precise source and scope recorded in the extraction map. -/ theorem homogeneousComponent_mem_jacobian [CharZero K] (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h) (d : ℕ) (p :
  P) (hp : p ∈ jacobianSubmodule F) : weightedHomogeneousComponent w d p ∈ jacobianSubmodule F := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.KoszulSyzygies
open scoped BigOperators
variable {R ι : Type*} [CommRing R] [Fintype ι]
/-- The coefficient map `(g_i) ↦ ∑ g_i f_i`. -/ def coefficient (f : ι → R) : (ι → R) →ₗ[R] R :=
  Fintype.linearCombination R f
end PaperVerification.KoszulSyzygies
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Polynomial vector fields tangent to all level sets of `F`. -/ def tangent (F : P) : Submodule P (ι → P) :=
  LinearMap.ker (KoszulSyzygies.coefficient (gradient F))
/-- Divergences of tangent fields, regarded as a coefficient-ring submodule. -/ def divergenceSpace (F : P) : Submodule K P :=
  ((tangent F).restrictScalars K).map divergence
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.BrieskornQuotient; precise source and scope recorded in the extraction map. -/ abbrev BrieskornQuotient (F : P) := P ⧸ divergenceSpace F
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Multiplication by the potential preserves the divergence subspace. -/ theorem potential_mul_mem (F u : P) (hu : u ∈ divergenceSpace F) : F * u ∈ divergenceSpace F := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.potentialAction; precise source and scope recorded in the extraction map. -/ def potentialAction (F : P) : BrieskornQuotient F →ₗ[K] BrieskornQuotient F :=
  (divergenceSpace F).mapQ (divergenceSpace F) (LinearMap.mulLeft K F)
    (fun u hu => potential_mul_mem F u hu)
/-- `K[X]` acts on the divergence quotient with `X` acting as the potential. -/ abbrev BrieskornModule (F : P) := Module.AEval' (potentialAction F)
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local instance defectDecidableEq : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K
/-- The literal quotient of Jacobian elements by the hit relations. The preceding containment identifies these relations with the paper's subspace `H_t(F)`. -/ abbrev DefectQuotient (F : P) (t : K) :=
  jacobianSubmodule F ⧸
    (EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Filter Topology
variable {K ι : Type*} [CommRing K]
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
/-- The ordinary analytic meaning of an isolated critical point at the origin. -/ def IsolatedCriticalPointAtOrigin (F : P) : Prop :=
  (∀ i, aeval (0 : Fin n → ℂ) (pderiv i F) = 0) ∧
  ∃ U : Set (Fin n → ℂ), U ∈ 𝓝 0 ∧
    ∀ x ∈ U, (∀ i, aeval x (pderiv i F) = 0) → x = 0
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
attribute [local instance] PaperVerification.JacobianDivergence.defectDecidableEq
local notation "P" => MvPolynomial ι K
/-- The image of the Jacobian ideal in the literal differential quotient. -/ def defectImage (F : P) (t : K) :
    Submodule K (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (jacobianSubmodule F).map (EulerJacobian.hit (gradient F) F t).mkQ
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.integerHilbertSeries; precise source and scope recorded in the extraction map. -/ def integerHilbertSeries (w : ι → ℕ) (U : Submodule K P) : PowerSeries ℤ :=
  PowerSeries.mk fun e => (Module.finrank K (EulerResonance.quotientComponent w e U) : ℤ)
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local instance hamiltonianDecidableEq : DecidableEq ι := Classical.decEq ι
/-- Literal PaperVerification.JacobianDivergence.hamiltonian; precise source and scope recorded in the extraction map. -/ def hamiltonian (F : P) (i j : ι) : P →ₗ[K] P :=
  (LinearMap.mulLeft K (pderiv j F)).comp (pderiv i).toLinearMap -
    (LinearMap.mulLeft K (pderiv i F)).comp (pderiv j).toLinearMap
/-- The exact `i < j` presentation printed in the paper. -/ def orderedHamiltonianSpace {n : ℕ} (F : MvPolynomial (Fin n) K) :
    Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ i j : Fin n, i < j ∧ ∃ q, p = hamiltonian F i j q}
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial Module
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.potential_transcendental; precise source and scope recorded in the extraction map. -/ theorem potential_transcendental [IsAlgClosed K] (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0) (hh : 0 < h) (hF :
  F.IsWeightedHomogeneous w h) : Transcendental K F := by sorry
/-- Literal PaperVerification.JacobianDivergence.potentialParameterEquiv; precise source and scope recorded in the extraction map. -/ def potentialParameterEquiv [IsAlgClosed K]
    (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    K[X] ≃ₐ[K] Algebra.adjoin K {F} :=
  Polynomial.algEquivOfTranscendental K F (potential_transcendental F w h hne hh hF)
/-- Literal PaperVerification.JacobianDivergence.potentialSubalgebraModule; precise source and scope recorded in the extraction map. -/ def potentialSubalgebraModule [IsAlgClosed K]
    (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    Module (Algebra.adjoin K {F}) (BrieskornModule F) :=
  Module.compHom (BrieskornModule F)
    (potentialParameterEquiv F w h hne hh hF).symm.toRingHom
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators DirectSum
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
/-- All scalar clauses, with the full nonresonant range and every resonant degree. The graded freeness assertion is supplemented by the arbitrary-basis lifting theorem below. -/ theorem paper_theorem_6_3_scalar (hn : 2 ≤ n) (F : P)
    (w : Fin n → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F) :
    (∀ t : ℂ,
      (∀ d ∈ EulerJacobian.occurringDegrees (K := ℂ) w,
        t ≠ -(h : ℂ)/((∑ i, w i : ℕ)+d : ℂ)) →
      EulerJacobian.hit (gradient F) F t = jacobianSubmodule F) ∧
    divergenceSpace F = orderedHamiltonianSpace F ∧
    (letI := potentialSubalgebraModule F w h hne hh hF
     Module.Free (Algebra.adjoin ℂ {F}) (BrieskornModule F)) ∧
    (∀ d ∈ EulerJacobian.occurringDegrees (K := ℂ) w,
      let t := -(h : ℂ)/((∑ i, w i : ℕ)+d : ℂ)
      defectImage F t ≤ EulerResonance.quotientComponent w (h+d)
          (EulerJacobian.hit (gradient F) F t) ∧
      Nonempty (DefectQuotient F t ≃ₗ[ℂ]
        EulerResonance.quotientComponent w d (orderedHamiltonianSpace F)) ∧
      integerHilbertSeries w (EulerJacobian.hit (gradient F) F t) =
        integerHilbertSeries w (jacobianSubmodule F) +
          PowerSeries.monomial (h+d)
            (PowerSeries.coeff d (integerHilbertSeries w (jacobianSubmodule F) *
              HilbertTowerCount.geometricInverse h))) := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.MilnorQuotient; precise source and scope recorded in the extraction map. -/ abbrev MilnorQuotient (F : P) := P ⧸ jacobianSubmodule F
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators DirectSum
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
/-- Every chosen homogeneous lift of every homogeneous Milnor basis is a basis over the actual subalgebra generated by `F`. -/ theorem paper_theorem_6_3_basis_lifts {I : Type*} (hn : 2 ≤ n) (F : P)
    (w : Fin n → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (b : I → P) (hbhom : ∀ i, ∃ d : ℕ, (b i).IsWeightedHomogeneous w d)
    (B : Basis I ℂ (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    letI := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra
/-- Literal PaperVerification.NegativeWeightedGrading.negativeWeights; precise source and scope recorded in the extraction map. -/ def negativeWeights (w : ι → ℕ) : ι → ℤ := fun i => -(w i : ℤ)
/-- Literal PaperVerification.NegativeWeightedGrading.grading; precise source and scope recorded in the extraction map. -/ def grading (w : ι → ℕ) : TauCeti.InternalGrading K P :=
  .ofDecomposition (weightedHomogeneousSubmodule K (negativeWeights w))
end PaperVerification.NegativeWeightedGrading
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.NegativeWeightedGrading.submodule_homogeneous; precise source and scope recorded in the extraction map. -/ theorem submodule_homogeneous (w : ι → ℕ) (U : Submodule K P) (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) :
  DirectSum.SetLike.IsHomogeneous (grading (K := K) w).piece U := by sorry
/-- Literal PaperVerification.NegativeWeightedGrading.quotientGrading; precise source and scope recorded in the extraction map. -/ def quotientGrading (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) :
    TauCeti.InternalGrading K (P ⧸ U) :=
  (grading w).quotient U (submodule_homogeneous w U hU)
end PaperVerification.NegativeWeightedGrading
namespace PaperVerification.JacobianDivergence
open MvPolynomial
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
/-- Literal PaperVerification.JacobianDivergence.milnorNegativeGrading; precise source and scope recorded in the extraction map. -/ def milnorNegativeGrading (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) : TauCeti.InternalGrading K (MilnorQuotient F) :=
  NegativeWeightedGrading.quotientGrading w (jacobianSubmodule F)
    (homogeneousComponent_mem_jacobian F w h hF)
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- Literal PaperVerification.JacobianLinearAction.linearSubst_mem_jacobianSubmodule; precise source and scope recorded in the extraction map. -/ theorem linearSubst_mem_jacobianSubmodule (M : GL) (F : P) (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P) (hp : p ∈
  jacobianSubmodule F) : linearSubst (M : Matrix ι ι K) p ∈ jacobianSubmodule F := by sorry
end PaperVerification.JacobianLinearAction
namespace MvPolynomial
open Matrix MulOpposite
variable {σ R : Type*} [Fintype σ] [CommSemiring R]
/-- Literal MvPolynomial.linearSubst_mul_apply; precise source and scope recorded in the extraction map. -/ theorem linearSubst_mul_apply (M N : Matrix σ σ R) (p : MvPolynomial σ R) : linearSubst (M * N) p = linearSubst N (linearSubst M
  p) := by sorry
/-- Literal MvPolynomial.linearSubst_one; precise source and scope recorded in the extraction map. -/ theorem linearSubst_one [DecidableEq σ] : linearSubst (1 : Matrix σ σ R) = AlgHom.id R _ := by sorry
end MvPolynomial
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
variable {G : Type*} [Group G]
/-- The usual left action on polynomial functions: `g` substitutes `g⁻¹ x`. -/ def polynomialRepresentation (ρ : G →* GL) : Representation K G P where
  toFun g := (linearSubst (ρ g⁻¹ : Matrix ι ι K)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    change linearSubst (ρ ((1 : G)⁻¹) : Matrix ι ι K) p = p
    simp only [inv_one, map_one, Units.val_one, linearSubst_one, AlgHom.id_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change linearSubst (ρ ((g * h)⁻¹) : Matrix ι ι K) p =
      linearSubst (ρ g⁻¹ : Matrix ι ι K) (linearSubst (ρ h⁻¹ : Matrix ι ι K) p)
    rw [_root_.mul_inv_rev, map_mul, Units.val_mul, linearSubst_mul_apply]
/-- The Milnor quotient action uses the actual Jacobian ideal and its proved stability. -/ def milnorRepresentation (ρ : G →* GL) (F : P)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (MilnorQuotient F) :=
  (polynomialRepresentation ρ).quotient (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hF g⁻¹) p hp)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped DirectSum BigOperators
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- Literal PaperVerification.JacobianDivergence.milnorRepresentation_preserves_negativeGrading; precise source and scope recorded in the extraction map. -/ theorem milnorRepresentation_preserves_negativeGrading (ρ : G →* GL) (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w
  h) (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K))
  : ∀ g p x, x ∈ (milnorNegativeGrading F w h hF).piece p → JacobianLinearAction.milnorRepresentation ρ F hFix g x ∈
  (milnorNegativeGrading F w h hF).piece p := by sorry
/-- Literal PaperVerification.JacobianDivergence.milnorTowerRepresentation; precise source and scope recorded in the extraction map. -/ def milnorTowerRepresentation
    (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) :
    Representation K G
      (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h)) :=
  GradedTowers.shiftedPiecesRepresentation (milnorNegativeGrading F w h hF)
    (JacobianLinearAction.milnorRepresentation ρ F hFix)
    (milnorRepresentation_preserves_negativeGrading ρ F w h hF hFix hW) h (-(d : ℤ))
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- The natural map from the literal `J(F)/H_t(F)` to `P/H_t(F)`. -/ def defectInjection (F : P) (t : K) :
    DefectQuotient F t →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (defectImage F t).subtype.comp (defectQuotientEquivImage F t).toLinearMap
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
open scoped BigOperators
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- The actual Jacobian ideal, regarded as a subrepresentation of polynomials. -/ def jacobianRepresentation (ρ : G →* GL) (F : P)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (jacobianSubmodule F) :=
  (polynomialRepresentation ρ).subrepresentation (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hFix g⁻¹) p hp)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- Literal PaperVerification.JacobianLinearAction.linearSubst_mem_hit; precise source and scope recorded in the extraction map. -/ theorem linearSubst_mem_hit (M : GL) (F : P) (t : K) (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P) (hp : p ∈
  EulerJacobian.hit (gradient F) F t) : linearSubst (M : Matrix ι ι K) p ∈ EulerJacobian.hit (gradient F) F t := by sorry
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
open scoped BigOperators
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- The action on the literal quotient `J(F)/H_t(F)` is induced from the coordinate action on the actual ideal and actual hit space. -/ def defectQuotientRepresentation (ρ : G →* GL) (F : P) (t : K)
    (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (DefectQuotient F t) :=
  (jacobianRepresentation ρ F hFix).quotient
    ((EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hFix g⁻¹) p hp)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
variable {G : Type*} [Group G]
/-- The actual perturbed differential quotient carries the coordinate action. -/ def hitQuotientRepresentation (ρ : G →* GL) (F : P) (t : K)
    (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) :
    Representation K G (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (polynomialRepresentation ρ).quotient (EulerJacobian.hit (gradient F) F t)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hF g⁻¹) p hp)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
/-- The natural projection `P/H_t(F) → P/J(F)`, induced by the identity on polynomials and the proved inclusion of the hit space in the Jacobian ideal. -/ def hitToMilnor (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    (P ⧸ EulerJacobian.hit (gradient F) F t) →ₗ[K] MilnorQuotient F :=
  Submodule.factor (hit_le_jacobian F w h t hh hF)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators DirectSum
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
/-- The full group-module clause and the natural exact sequence with an actual homogeneous equivariant section. Negative tower degrees are the zero pieces of the proved integer grading. -/ theorem paper_theorem_6_3_equivariant {G : Type*} [Group G] [Fintype G]
    (hn : 2 ≤ n) (F : P) (w : Fin n → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (ρ : G →* (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hFix : ∀ g, linearSubst (ρ g : Matrix (Fin n) (Fin n) ℂ) F = F)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) ℂ)) :
    (∀ d ∈ EulerJacobian.occurringDegrees (K := ℂ) w,
      let t := -(h : ℂ)/((∑ i, w i : ℕ)+d : ℂ)
      ∃ e : DefectQuotient F t ≃ₗ[ℂ]
          (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ)+(j : ℤ)*h)),
        ∀ g x, e (JacobianLinearAction.defectQuotientRepresentation ρ F t hFix g x) =
          milnorTowerRepresentation ρ F w h d hF hFix hW g (e x)) ∧
    (∀ t : ℂ,
      Function.Injective (JacobianLinearAction.defectInjection F t) ∧
      Function.Exact (JacobianLinearAction.defectInjection F t)
        (JacobianLinearAction.hitToMilnor F w h t hh hF) ∧
      Function.Surjective (JacobianLinearAction.hitToMilnor F w h t hh hF)) ∧
    (∀ t : ℂ, ∃ s : MilnorQuotient F →ₗ[ℂ]
        (P ⧸ EulerJacobian.hit (gradient F) F t),
      (∀ x, JacobianLinearAction.hitToMilnor F w h t hh hF (s x) = x) ∧
      (∀ g x, s (JacobianLinearAction.milnorRepresentation ρ F hFix g x) =
        JacobianLinearAction.hitQuotientRepresentation ρ F t hFix g (s x)) ∧
      ∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
        s x ∈ EulerResonance.quotientComponent w d (EulerJacobian.hit (gradient F) F t)) := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.IsArtinExponent; precise source and scope recorded in the extraction map. -/ def IsArtinExponent (m : ℕ) (a : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, a i < m + i.val
/-- Literal PaperVerification.PowerOperators.artinSpan; precise source and scope recorded in the extraction map. -/ def artinSpan (K : Type*) [Field K] (n m : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ a : Fin n →₀ ℕ,
    IsArtinExponent m a ∧ p = monomial a 1}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Module
open scoped BigOperators
/-- Literal PaperVerification.PowerOperators.ArtinIndex; precise source and scope recorded in the extraction map. -/ def ArtinIndex (n m : ℕ) := {a : Fin n →₀ ℕ // IsArtinExponent m a}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R] (n : ℕ)
/-- Literal PaperVerification.PowerOperators.ordinaryCoinvariantIdeal; precise source and scope recorded in the extraction map. -/ def ordinaryCoinvariantIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun i : Fin n => esymm (Fin n) R (i.val+1))
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.completeHomogeneousFamily; precise source and scope recorded in the extraction map. -/ def completeHomogeneousFamily (K : Type*) [Field K] (n m : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.hsymm (Fin n) K (m+i.val)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.completeHomogeneousIdeal; precise source and scope recorded in the extraction map. -/ abbrev completeHomogeneousIdeal (K : Type*) [Field K] (n m : ℕ) :
    Ideal (MvPolynomial (Fin n) K) :=
  ordinaryFamilyIdeal (completeHomogeneousFamily K n m)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
local instance palomarPowerRingDecidableEq : DecidableEq ι := Classical.decEq ι
/-- The coordinate Euler derivation `X_i ∂_i`, viewed as a linear map. -/ def euler (i : ι) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i)).comp (pderiv i).toLinearMap
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
attribute [local instance] PaperVerification.PowerOperators.palomarPowerRingDecidableEq
variable [Fintype ι]
/-- The original family `A_k = ∑ M_(X_i^k) (c_i + lamE_i)`. -/ def original (c : ι → R) (lam : R) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, (LinearMap.mulLeft R (X i ^ k)).comp
    (c i • LinearMap.id + lam • euler i)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local instance palomarPowerFieldDecidableEq : DecidableEq ι := Classical.decEq ι
/-- Literal PaperVerification.PowerOperators.originalTailHit; precise source and scope recorded in the extraction map. -/ def originalTailHit (c : ι → K) (lam : K) (m : ℕ) :
    Submodule K (MvPolynomial ι K) :=
  Submodule.span K {p | ∃ k, m ≤ k ∧ ∃ q, p = original c lam k q}
/-- The image of the genuine homogeneous polynomial piece in the original joint-image quotient. The definition also applies at resonant parameters. -/ def originalTailQuotientDegree (c : ι → K) (lam : K) (m d : ℕ) :
    Submodule K (MvPolynomial ι K ⧸ originalTailHit c lam m) :=
  (homogeneousSubmodule ι K d).map (originalTailHit c lam m).mkQ
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
attribute [local instance] PaperVerification.PowerOperators.palomarPowerRingDecidableEq
/-- One summand of the reversed weighted power operator, in expanded Euler form. -/ def component (c lam : R) (i : ι) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i ^ k)).comp
    ((c + lam * (k : R)) • LinearMap.id + lam • euler i)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
attribute [local instance] PaperVerification.PowerOperators.palomarPowerRingDecidableEq
variable [Fintype ι]
/-- The reversed family `B_k = ∑ (c_i + lamE_i) M_(X_i^k)`. -/ def reversed (c : ι → R) (lam : R) (k : ℕ) :
    MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, component (c i) lam i k
/-- The literal vector-space sum of the images of every operator in a tail. -/ def tailHit (c : ι → R) (lam : R) (m : ℕ) : Submodule R (MvPolynomial ι R) :=
  Submodule.span R {p | ∃ k, m ≤ k ∧ ∃ q, p = reversed c lam k q}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Module Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
/-- The literal degree-`d` subspace of the polynomial quotient. -/ def tailQuotientDegree (c : Fin n → R) (lam : R) (m d : ℕ) :
    Submodule R (MvPolynomial (Fin n) R ⧸ tailHit c lam m) :=
  (homogeneousSubmodule (Fin n) R d).map (tailHit c lam m).mkQ
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.rename_mem_originalTailHit; precise source and scope recorded in the extraction map. -/ theorem rename_mem_originalTailHit (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K) (hfix : ∀ i, c (e i) = c i) (m : ℕ) {p :
  MvPolynomial (Fin n) K} (hp : p ∈ originalTailHit c lam m) : MvPolynomial.rename e p ∈ originalTailHit c lam m := by sorry
/-- Literal PaperVerification.PowerOperators.originalTailQuotientAction; precise source and scope recorded in the extraction map. -/ def originalTailQuotientAction (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → K) (lam : K) (m : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    Representation K G (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) := by
  refine QuotientLinearAction.action (polynomialPermutationAction K G)
    (originalTailHit c lam m) ?_
  intro g p hp
  change MvPolynomial.rename (g : Equiv.Perm (Fin n)) p ∈ originalTailHit c lam m
  exact rename_mem_originalTailHit (g : Equiv.Perm (Fin n)) c lam (hfix g) m hp
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
/-- The full condition `NR_m` from equation (2.1), with no degree truncation. -/ def Nonresonant (c : ι → R) (lam : R) (m : ℕ) : Prop :=
  ∀ I : Finset ι, I.Nonempty → ∀ s : ℕ, m * I.card ≤ s →
    (∑ i ∈ I, c i) + lam * (s : R) ≠ 0
/-- The exact exceptional set `E_n` in Theorem 1.1. -/ def exceptionalSet (K : Type*) [Field K] (n : ℕ) : Set K :=
  {α | ∃ r s : ℕ, 1 ≤ r ∧ r ≤ n ∧ r ≤ s ∧ α = -(r : K) / (s : K)}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.rename_mem_tailHit; precise source and scope recorded in the extraction map. -/ theorem rename_mem_tailHit (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R) (hfix : ∀ i, c (e i) = c i) (m : ℕ) {p :
  MvPolynomial (Fin n) R} (hp : p ∈ tailHit c lam m) : MvPolynomial.rename e p ∈ tailHit c lam m := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
variable (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ)
variable (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
/-- The actual induced representation on the complete joint-image quotient. -/ def tailQuotientAction : Representation K G (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  QuotientLinearAction.action (polynomialPermutationAction K G) (tailHit c lam m)
    (fun g _ hp => rename_mem_tailHit (g : Equiv.Perm (Fin n)) c lam (hfix g) m hp)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open PaperVerification.EquivariantHomMatrices
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.completeHomogeneousFamily_invariant; precise source and scope recorded in the extraction map. -/ theorem completeHomogeneousFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) (g : G) (i : Fin n) : MvPolynomial.rename
  (g : Equiv.Perm (Fin n)) (completeHomogeneousFamily K n m i) = completeHomogeneousFamily K n m i := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation Module
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.completeHomogeneousAction; precise source and scope recorded in the extraction map. -/ def completeHomogeneousAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    Representation K G (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) :=
  ordinaryQuotientAction G (completeHomogeneousFamily K n m)
    (completeHomogeneousFamily_invariant G m)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.powerSumFamily; precise source and scope recorded in the extraction map. -/ def powerSumFamily (K : Type*) [Field K] (n m : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.psum (Fin n) K (m+i.val)
/-- Literal PaperVerification.PowerOperators.powerSumIdeal; precise source and scope recorded in the extraction map. -/ abbrev powerSumIdeal (K : Type*) [Field K] (n m : ℕ) :
    Ideal (MvPolynomial (Fin n) K) := ordinaryFamilyIdeal (powerSumFamily K n m)
/-- Literal PaperVerification.PowerOperators.powerSumFamily_invariant; precise source and scope recorded in the extraction map. -/ theorem powerSumFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) (g : G) (i : Fin n) : MvPolynomial.rename (g :
  Equiv.Perm (Fin n)) (powerSumFamily K n m i) = powerSumFamily K n m i := by sorry
/-- Literal PaperVerification.PowerOperators.powerSumAction; precise source and scope recorded in the extraction map. -/ def powerSumAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) :
    Representation K G (MvPolynomial (Fin n) K ⧸ powerSumIdeal K n m) :=
  ordinaryQuotientAction G (powerSumFamily K n m) (powerSumFamily_invariant G m)
end PaperVerification.PowerOperators
namespace PaperVerification
open MvPolynomial Representation Module
open scoped BigOperators
/-- Literal PaperVerification.GradedRepresentationEquivalent; precise source and scope recorded in the extraction map. -/ def GradedRepresentationEquivalent
    {K G V W : Type*} [Semiring K] [Monoid G]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (A : ℕ → Submodule K V) (B : ℕ → Submodule K W) : Prop :=
  ∃ e : ρ.Equiv σ, ∀ d x, x ∈ A d ↔ e x ∈ B d
end PaperVerification
namespace PaperVerification.PowerOperators
open MvPolynomial Representation Module
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.elementaryCoinvariantFamily; precise source and scope recorded in the extraction map. -/ def elementaryCoinvariantFamily (K : Type*) [Field K] (n : ℕ) :
    Fin n → MvPolynomial (Fin n) K := fun i => esymm (Fin n) K (i.val+1)
/-- Literal PaperVerification.PowerOperators.ordinaryCoinvariantDegree; precise source and scope recorded in the extraction map. -/ def ordinaryCoinvariantDegree (K : Type*) [Field K] (n d : ℕ) :
    Submodule K (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientDegree (elementaryCoinvariantFamily K n) d
/-- Literal PaperVerification.PowerOperators.elementaryCoinvariantFamily_invariant; precise source and scope recorded in the extraction map. -/ theorem elementaryCoinvariantFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (g : G) (i : Fin n) : rename (g : Equiv.Perm
  (Fin n)) (elementaryCoinvariantFamily K n i) = elementaryCoinvariantFamily K n i := by sorry
/-- Literal PaperVerification.PowerOperators.ordinaryCoinvariantAction; precise source and scope recorded in the extraction map. -/ def ordinaryCoinvariantAction (G : Subgroup (Equiv.Perm (Fin n))) :
    Representation K G (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientAction G (elementaryCoinvariantFamily K n)
    (elementaryCoinvariantFamily_invariant G)
/-- Literal PaperVerification.PowerOperators.permutationToTop; precise source and scope recorded in the extraction map. -/ def permutationToTop (n : ℕ) :
    Equiv.Perm (Fin n) →* (⊤ : Subgroup (Equiv.Perm (Fin n))) where
  toFun σ := ⟨σ, trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl
/-- Literal PaperVerification.PowerOperators.ordinaryCoinvariantRepresentation; precise source and scope recorded in the extraction map. -/ def ordinaryCoinvariantRepresentation :
    Representation K (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  (ordinaryCoinvariantAction ⊤).comp (permutationToTop n)
/-- Literal PaperVerification.PowerOperators.originalCoinvariantRepresentation; precise source and scope recorded in the extraction map. -/ def originalCoinvariantRepresentation (α : K) :
    Representation K (Equiv.Perm (Fin n))
      (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1) :=
  (originalTailQuotientAction ⊤ (fun _ : Fin n => (1 : K)) α 1
    (fun _ _ => rfl)).comp (permutationToTop n)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
/-- Literal PaperVerification.PowerOperators.paper_theorem_1_1; precise source and scope recorded in the extraction map. -/ theorem paper_theorem_1_1 (α : K) : (α ∉ exceptionalSet K n → (∃ B : Basis (ArtinIndex n 1) K (MvPolynomial (Fin n) K ⧸
  originalTailHit (fun _ => (1 : K)) α 1), ∀ a, B a = (originalTailHit (fun _ => (1 : K)) α 1).mkQ (monomial a.val 1)) ∧
  PaperVerification.GradedRepresentationEquivalent (originalCoinvariantRepresentation α) (ordinaryCoinvariantRepresentation (K :=
  K) (n := n)) (originalTailQuotientDegree (fun _ : Fin n => (1 : K)) α 1) (ordinaryCoinvariantDegree K n)) ∧ (2 ≤ n → (artinSpan
  K n 1).map (originalTailHit (fun _ : Fin n => (1 : K)) α 1).mkQ = ⊤ → α ∉ exceptionalSet K n) := by sorry
end PaperVerification.PowerOperators
namespace PalomarDeformed
open MvPolynomial Module Representation
open scoped BigOperators Classical
open PaperVerification PaperVerification.PowerOperators
variable {K : Type*} [Field K] {n : ℕ}
/-- The Hilbert series of the actual homogeneous subspaces of the reversed joint-image quotient. -/ def tailHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (tailQuotientDegree c lam m d) : ℤ)
/-- The Hilbert series of the actual homogeneous subspaces of the original joint-image quotient. -/ def originalHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (originalTailQuotientDegree c lam m d) : ℤ)
/-- The finite polynomial 1+q+...+q^(j-1). -/ def qIntegerPolynomial (j : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range j, Polynomial.X ^ i
/-- Every clause of Theorem 2.2, with both genuine quotient Hilbert series and every coefficient-fixing subgroup. -/ theorem weighted_tail_theorem (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m) : (∃ B : Basis
  (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m), ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1)) ∧
  (tailHilbertSeries c lam m = ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧ (∀ (G :
  Subgroup (Equiv.Perm (Fin n))) (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i), GradedRepresentationEquivalent
  (tailQuotientAction G c lam m hfix) (completeHomogeneousAction G m) (tailQuotientDegree c lam m) (ordinaryQuotientDegree
  (completeHomogeneousFamily K n m))) ∧ (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)),
  GradedRepresentationEquivalent (tailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl)) (powerSumAction G m)
  (tailQuotientDegree (fun _ : Fin n => a) lam m) (ordinaryQuotientDegree (powerSumFamily K n m))) ∧ (∀ hlow : ∀ i, ∀ a : ℕ, a < m
  → c i + lam * (a : K) ≠ 0, (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m), ∀ a, B a =
  (originalTailHit c lam m).mkQ (monomial a.val 1)) ∧ (originalHilbertSeries c lam m = ((∏ j ∈ Finset.Ico m (m+n),
  qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧ (∀ (G : Subgroup (Equiv.Perm (Fin n))) (hfix : ∀ g : G, ∀ i, c ((g :
  Equiv.Perm (Fin n)) i) = c i), GradedRepresentationEquivalent (originalTailQuotientAction G c lam m hfix)
  (completeHomogeneousAction G m) (originalTailQuotientDegree c lam m) (ordinaryQuotientDegree (completeHomogeneousFamily K n m)))
  ∧ (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)), GradedRepresentationEquivalent (originalTailQuotientAction G
  (fun _ : Fin n => a) lam m (fun _ _ => rfl)) (powerSumAction G m) (originalTailQuotientDegree (fun _ : Fin n => a) lam m)
  (ordinaryQuotientDegree (powerSumFamily K n m)))) := by sorry
end PalomarDeformed

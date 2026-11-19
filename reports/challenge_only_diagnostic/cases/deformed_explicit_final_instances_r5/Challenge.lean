module
public import Mathlib.RingTheory.PowerSeries.Inverse
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
@[expose] public section
namespace PalomarDeformedSupport
universe uK uR uM uS
theorem fieldIdentitySurjective {K : Type uK} [Field K] : RingHomSurjective (RingHom.id K) := by sorry
theorem fieldIdentityCompTriple {K : Type uK} [Field K] : RingHomCompTriple (RingHom.id K) (RingHom.id K) (RingHom.id K) := by sorry
theorem fieldIdentityInvPair {K : Type uK} [Field K] : RingHomInvPair (RingHom.id K) (RingHom.id K) := by sorry
theorem ringIdentitySurjective {R : Type uR} [Ring R] : RingHomSurjective (RingHom.id R) := by sorry
theorem permutationSubmonoid (n : ℕ) : SubmonoidClass (Subgroup (Equiv.Perm (Fin n))) (Equiv.Perm (Fin n)) := by sorry
theorem submoduleAddSubmonoid {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] : AddSubmonoidClass (Submodule R M) M := by sorry
theorem subtypeScalarCompatible {R : Type uR} {M : Type uM} {S : Type uS} [Semiring R] [Semiring S] [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (U : Submodule S M) : LinearMap.CompatibleSMul U M R S := by sorry
theorem quotientScalarCompatible {R : Type uR} {M : Type uM} {S : Type uS} [Ring R] [Ring S] [SMul R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (U : Submodule S M) : LinearMap.CompatibleSMul M (M ⧸ U) R S := by sorry
attribute [instance 2000] fieldIdentitySurjective fieldIdentityCompTriple fieldIdentityInvPair permutationSubmonoid submoduleAddSubmonoid subtypeScalarCompatible quotientScalarCompatible
attribute [instance 1900] ringIdentitySurjective
theorem fieldDivisionIdentityInvPair {K : Type uK} [hK : Field K] :
    @RingHomInvPair K K hK.toDivisionRing.toRing.toSemiring hK.toDivisionRing.toRing.toSemiring
      (@RingHom.id K hK.toDivisionRing.toRing.toSemiring.toNonAssocSemiring)
      (@RingHom.id K hK.toDivisionRing.toRing.toSemiring.toNonAssocSemiring) := by infer_instance
theorem fieldDivisionIdentitySurjective {K : Type uK} [hK : Field K] :
    @RingHomSurjective K K hK.toDivisionRing.toRing.toSemiring hK.toDivisionRing.toRing.toSemiring
      (@RingHom.id K hK.toDivisionRing.toRing.toSemiring.toNonAssocSemiring) := by infer_instance
theorem commRingIdentitySurjective {R : Type uR} [hR : CommRing R] :
    @RingHomSurjective R R hR.toRing.toSemiring hR.toRing.toSemiring
      (@RingHom.id R hR.toRing.toSemiring.toNonAssocSemiring) := by infer_instance
theorem finitePolynomialSelfTower {K : Type uK} [hK : Field K] (n : ℕ) :
    IsScalarTower K (@MvPolynomial (Fin n) K hK.toCommRing.toCommSemiring)
      (@MvPolynomial (Fin n) K hK.toCommRing.toCommSemiring) := by infer_instance
theorem ringSubmoduleAddSubmonoid {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M] : AddSubmonoidClass (Submodule R M) M := by infer_instance
theorem submoduleScalarTower {R : Type uR} {M : Type uM} {S : Type uS} [Semiring R] [Semiring S] [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (U : Submodule S M) : IsScalarTower R S U := by infer_instance
attribute [instance 2200] fieldDivisionIdentityInvPair fieldDivisionIdentitySurjective commRingIdentitySurjective finitePolynomialSelfTower ringSubmoduleAddSubmonoid submoduleScalarTower
section
universe u v w
theorem mapIdentitySurjective {K : Type u} [CommRing K] : RingHomSurjective (RingHom.id K) := by infer_instance
variable {K : Type u} {M : Type v} {N : Type w} [CommRing K]
  [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]
def explicitMap (f : M →ₗ[K] N) (p : Submodule K M) : Submodule K N := @Submodule.map K K M N _ _ _ _ _ _ (RingHom.id K) mapIdentitySurjective f p
def explicitRange (f : M →ₗ[K] N) : Submodule K N := @LinearMap.range K K M N _ _ _ _ _ _ (RingHom.id K) mapIdentitySurjective f
end
section
universe u v w z
theorem explicitIdentityComp {K : Type u} [Field K] : RingHomCompTriple (RingHom.id K) (RingHom.id K) (RingHom.id K) := by infer_instance
theorem explicitIdentityInv {K : Type u} [Field K] : RingHomInvPair (RingHom.id K) (RingHom.id K) := by infer_instance
variable {K : Type u} {M : Type v} {N : Type w} {O : Type z} [Field K]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup O] [Module K M] [Module K N] [Module K O]
def explicitEquivTrans (e : M ≃ₗ[K] N) (f : N ≃ₗ[K] O) : M ≃ₗ[K] O :=
  @LinearEquiv.trans K K K M N O _ _ _ _ _ _ _ _ _
    (RingHom.id K) (RingHom.id K) (RingHom.id K)
    (RingHom.id K) (RingHom.id K) (RingHom.id K)
    explicitIdentityComp explicitIdentityComp
    explicitIdentityInv explicitIdentityInv explicitIdentityInv
    explicitIdentityInv explicitIdentityInv explicitIdentityInv e f
end
end PalomarDeformedSupport
end
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
theorem iSupIndep.map_of_ker_inf_iSup_le {R ι M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] {A : ι → Submodule R M}
    (hA : iSupIndep A) (f : M →ₗ[R] N)
    (hker : LinearMap.ker f ⊓ (⨆ i, A i) ≤ ⨆ i, LinearMap.ker f ⊓ A i) :
    iSupIndep fun i ↦ (A i).map f := by sorry
namespace PaperVerification.EulerJacobian
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
 abbrev Poly := MvPolynomial ι K
 def operator (A : ι → Poly (K := K) (ι := ι)) (F : Poly (K := K) (ι := ι)) (t : K) (i : ι) (g : Poly (K := K) (ι := ι)) : Poly (K := K) (ι := ι) :=
  A i * g + t • (F * pderiv i g)
 def hit (A : ι → Poly (K := K) (ι := ι)) (F : Poly (K := K) (ι := ι)) (t : K) : Submodule K (Poly (K := K) (ι := ι)) :=
  Submodule.span K {f | ∃ i g, f = operator A F t i g}
 def coefficientIdeal (A : ι → Poly (K := K) (ι := ι)) : Ideal (Poly (K := K) (ι := ι)) :=
  Ideal.span (Set.range A)
 def occurringDegrees (w : ι → ℕ) : Set ℕ :=
  {d | ∃ f : MvPolynomial ι K, f ≠ 0 ∧ f.IsWeightedHomogeneous w d}
theorem eigenvalue_zero_iff [CharZero K] [Nonempty ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i) (h d : ℕ) (t : K) : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0 ↔ t = -(h : K) / ((∑ i, w i : ℕ) + d : K) := by sorry
theorem paper_theorem_6_2 (N : ℕ) (F : MvPolynomial (Fin N) ℂ) (t : ℂ) (w : Fin N → ℕ) (h : ℕ) (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) (hnr : ∀ d ∈ occurringDegrees (K := ℂ) w, t ≠ -(h : ℂ) / ((∑ i, w i : ℕ) + d : ℂ)) : hit (fun i => pderiv i F) F t = (coefficientIdeal (fun i => pderiv i F)).restrictScalars ℂ := by sorry
end PaperVerification.EulerJacobian
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def divergence : (ι → P) →ₗ[K] P where
  toFun g := ∑ i, pderiv i (g i)
  map_add' g h := by simp [Finset.sum_add_distrib]
  map_smul' a g := by simp [Finset.smul_sum]
 def gradient (F : P) : ι → P := fun i => pderiv i F
end PaperVerification.JacobianDivergence
namespace PaperVerification.PowerOperators
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
 def Nonresonant (c : ι → R) (lam : R) (m : ℕ) : Prop :=
  ∀ I : Finset ι, I.Nonempty → ∀ s : ℕ, m * I.card ≤ s →
    (∑ i ∈ I, c i) + lam * (s : R) ≠ 0
 def exceptionalSet (K : Type*) [Field K] (n : ℕ) : Set K :=
  {α | ∃ r s : ℕ, 1 ≤ r ∧ r ≤ n ∧ r ≤ s ∧ α = -(r : K) / (s : K)}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
 def completeHomogeneousFamily (K : Type*) [Field K] (n m : ℕ) : Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.hsymm (Fin n) K (m+i.val)
theorem completeHomogeneousFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) (g : G) (i : Fin n) : MvPolynomial.rename (g : Equiv.Perm (Fin n)) (completeHomogeneousFamily K n m i) = completeHomogeneousFamily K n m i := by sorry
 def powerSumFamily (K : Type*) [Field K] (n m : ℕ) : Fin n → MvPolynomial (Fin n) K := fun i => MvPolynomial.psum (Fin n) K (m+i.val)
theorem powerSumFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) (g : G) (i : Fin n) : MvPolynomial.rename (g : Equiv.Perm (Fin n)) (powerSumFamily K n m i) = powerSumFamily K n m i := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation Module
variable {K : Type*} [Field K] {n : ℕ}
 def elementaryCoinvariantFamily (K : Type*) [Field K] (n : ℕ) : Fin n → MvPolynomial (Fin n) K := fun i => esymm (Fin n) K (i.val+1)
theorem elementaryCoinvariantFamily_invariant (G : Subgroup (Equiv.Perm (Fin n))) (g : G) (i : Fin n) : rename (g : Equiv.Perm (Fin n)) (elementaryCoinvariantFamily K n i) = elementaryCoinvariantFamily K n i := by sorry
 def permutationToTop (n : ℕ) : Equiv.Perm (Fin n) →* (⊤ : Subgroup (Equiv.Perm (Fin n))) where
  toFun σ := ⟨σ, trivial⟩
  map_one' := rfl
  map_mul' _ _ := rfl
end PaperVerification.PowerOperators
namespace PaperVerification.EulerReduction
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
 def perturbed (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : U →ₗ[K] V :=
  C + t • (L.comp D)
end PaperVerification.EulerReduction
namespace PaperVerification.EulerInjective
open EulerReduction
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
 def hit (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : Submodule K V := PalomarDeformedSupport.explicitRange (perturbed C D L t)
 abbrev Defect (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) :=
  PalomarDeformedSupport.explicitRange C ⧸ (hit C D L t).comap (PalomarDeformedSupport.explicitRange C).subtype
 def defectImage (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : Submodule K (V ⧸ hit C D L t) :=
  PalomarDeformedSupport.explicitMap (hit C D L t).mkQ (PalomarDeformedSupport.explicitRange C)
 def defectToQuotient (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : PalomarDeformedSupport.explicitRange C →ₗ[K] (V ⧸ hit C D L t) :=
  (hit C D L t).mkQ.comp (PalomarDeformedSupport.explicitRange C).subtype
theorem defectToQuotient_kernel (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : LinearMap.ker (defectToQuotient C D L t) = (hit C D L t).comap (PalomarDeformedSupport.explicitRange C).subtype := by sorry
theorem defectToQuotient_range (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : LinearMap.range (defectToQuotient C D L t) = defectImage C D L t := by sorry
 def defectEquivImage (C : U →ₗ[K] V) (D : U →ₗ[K] W) (L : W →ₗ[K] V) (t : K) : Defect C D L t ≃ₗ[K] defectImage C D L t :=
  PalomarDeformedSupport.explicitEquivTrans
    (Submodule.quotEquivOfEq _ _ (defectToQuotient_kernel C D L t).symm)
    (PalomarDeformedSupport.explicitEquivTrans (defectToQuotient C D L t).quotKerEquivRange
      (LinearEquiv.ofEq _ _ (defectToQuotient_range C D L t)))
end PaperVerification.EulerInjective
namespace PaperVerification.EulerResonance
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def quotientComponent (w : ι → ℕ) (d : ℕ) (U : Submodule K P) : Submodule K (P ⧸ U) :=
  PalomarDeformedSupport.explicitRange (U.mkQ.comp (weightedHomogeneousComponent w d))
end PaperVerification.EulerResonance
namespace PaperVerification.HilbertTowerCount
variable {I : Type*}
 def geometricInverse (h : ℕ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (1 - PowerSeries.X ^ h) 1
end PaperVerification.HilbertTowerCount
namespace PaperVerification.PowerOperators
open MvPolynomial Matrix Representation
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) R
 def ordinaryFamilyIdeal (f : Fin n → P) : Ideal P := Ideal.span (Set.range f)
theorem rename_mem_ordinaryFamilyIdeal (e : Equiv.Perm (Fin n)) (f : Fin n → P) (hf : ∀ i, MvPolynomial.rename e (f i) = f i) {p : P} (hp : p ∈ ordinaryFamilyIdeal f) : MvPolynomial.rename e p ∈ ordinaryFamilyIdeal f := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
 def IsArtinExponent (m : ℕ) (a : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, a i < m + i.val
 def artinSpan (K : Type*) [Field K] (n m : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ a : Fin n →₀ ℕ,
    IsArtinExponent m a ∧ p = monomial a 1}
 abbrev completeHomogeneousIdeal (K : Type*) [Field K] (n m : ℕ) : Ideal (MvPolynomial (Fin n) K) :=
  ordinaryFamilyIdeal (completeHomogeneousFamily K n m)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Matrix Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
 def ordinaryQuotientDegree (f : Fin n → P) (d : ℕ) : Submodule K (P ⧸ ordinaryFamilyIdeal f) :=
  PalomarDeformedSupport.explicitMap ((ordinaryFamilyIdeal f).mkQ.restrictScalars K) (homogeneousSubmodule (Fin n) K d)
end PaperVerification.PowerOperators
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local instance hamiltonianDecidableEq : DecidableEq ι := Classical.decEq ι
 def hamiltonian (F : P) (i j : ι) : P →ₗ[K] P :=
  (LinearMap.mulLeft K (pderiv j F)).comp (pderiv i).toLinearMap -
    (LinearMap.mulLeft K (pderiv i F)).comp (pderiv j).toLinearMap
 def orderedHamiltonianSpace {n : ℕ} (F : MvPolynomial (Fin n) K) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ i j : Fin n, i < j ∧ ∃ q, p = hamiltonian F i j q}
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def integerHilbertSeries (w : ι → ℕ) (U : Submodule K P) : PowerSeries ℤ :=
  PowerSeries.mk fun e => (Module.finrank K (EulerResonance.quotientComponent w e U) : ℤ)
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Filter Topology
variable {K ι : Type*} [CommRing K]
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
 def IsolatedCriticalPointAtOrigin (F : P) : Prop :=
  (∀ i, aeval (0 : Fin n → ℂ) (pderiv i F) = 0) ∧
  ∃ U : Set (Fin n → ℂ), U ∈ 𝓝 0 ∧
    ∀ x ∈ U, (∀ i, aeval x (pderiv i F) = 0) → x = 0
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
variable {D : Type*} [AddCommMonoid D]
 def RespectsWeights (w : ι → D) (M : Matrix ι ι K) : Prop :=
  ∀ i j, M i j ≠ 0 → w i = w j
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial Module
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
theorem potential_transcendental [IsAlgClosed K] (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : Transcendental K F := by sorry
 def potentialParameterEquiv [IsAlgClosed K] (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : K[X] ≃ₐ[K] Algebra.adjoin K {F} :=
  Polynomial.algEquivOfTranscendental K F (potential_transcendental F w h hne hh hF)
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def jacobianSubmodule (F : P) : Submodule K P :=
  (Ideal.span (Set.range (gradient F))).restrictScalars K
 abbrev MilnorQuotient (F : P) := P ⧸ jacobianSubmodule F
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local instance defectDecidableEq : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K
 def defectImage (F : P) (t : K) : Submodule K (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  PalomarDeformedSupport.explicitMap (EulerJacobian.hit (gradient F) F t).mkQ (jacobianSubmodule F)
theorem hit_le_jacobian [CharZero K] (F : P) (w : ι → ℕ) (h : ℕ) (t : K) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : EulerJacobian.hit (gradient F) F t ≤ jacobianSubmodule F := by sorry
 abbrev DefectQuotient (F : P) (t : K) :=
  jacobianSubmodule F ⧸
    (EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype
 def defectToHit (F : P) (t : K) : jacobianSubmodule F →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (EulerJacobian.hit (gradient F) F t).mkQ.comp (jacobianSubmodule F).subtype
theorem defectToHit_kernel (F : P) (t : K) : LinearMap.ker (defectToHit F t) = (EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype := by sorry
theorem defectToHit_range (F : P) (t : K) : (@LinearMap.range K K _ _ _ _ _ _ _ _ (RingHom.id K) PalomarDeformedSupport.fieldDivisionIdentitySurjective (defectToHit F t)) = defectImage F t := by sorry
 def defectQuotientEquivImage (F : P) (t : K) : DefectQuotient F t ≃ₗ[K] defectImage F t :=
  (Submodule.quotEquivOfEq _ _ (defectToHit_kernel F t).symm).trans
    (LinearEquiv.trans (M₂ := (@LinearMap.range K K _ _ _ _ _ _ _ _ (RingHom.id K) PalomarDeformedSupport.fieldDivisionIdentitySurjective (defectToHit F t))) (module_M₂ := (inferInstance : Module K (@LinearMap.range K K _ _ _ _ _ _ _ _ (RingHom.id K) PalomarDeformedSupport.fieldDivisionIdentitySurjective (defectToHit F t)))) (defectToHit F t).quotKerEquivRange
      (LinearEquiv.ofEq (@LinearMap.range K K _ _ _ _ _ _ _ _ (RingHom.id K) PalomarDeformedSupport.fieldDivisionIdentitySurjective (defectToHit F t)) _ (defectToHit_range F t)))
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
 def hitToMilnor (F : P) (w : ι → ℕ) (h : ℕ) (t : K) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : (P ⧸ EulerJacobian.hit (gradient F) F t) →ₗ[K] MilnorQuotient F :=
  Submodule.factor (hit_le_jacobian F w h t hh hF)
 def defectInjection (F : P) (t : K) : DefectQuotient F t →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (defectImage F t).subtype.comp (defectQuotientEquivImage F t).toLinearMap
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
theorem homogeneousComponent_mem_jacobian [CharZero K] (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h) (d : ℕ) (p : P) (hp : p ∈ jacobianSubmodule F) : weightedHomogeneousComponent w d p ∈ jacobianSubmodule F := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.KoszulSyzygies
open scoped BigOperators
variable {R ι : Type*} [CommRing R] [Fintype ι]
 def coefficient (f : ι → R) : (ι → R) →ₗ[R] R :=
  Fintype.linearCombination R f
end PaperVerification.KoszulSyzygies
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def tangent (F : P) : Submodule P (ι → P) :=
  LinearMap.ker (KoszulSyzygies.coefficient (gradient F))
 def divergenceSpace (F : P) : Submodule K P :=
  ((tangent F).restrictScalars K).map divergence
theorem potential_mul_mem (F u : P) (hu : u ∈ divergenceSpace F) : F * u ∈ divergenceSpace F := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 abbrev BrieskornQuotient (F : P) := P ⧸ divergenceSpace F
theorem brieskornScalarComm (F : P) : SMulCommClass K K (BrieskornQuotient F) := by infer_instance
theorem brieskornScalarSelfTower (F : P) : IsScalarTower K K (BrieskornQuotient F) := by infer_instance
theorem brieskornEndScalarTower (F : P) : IsScalarTower K (Module.End K (BrieskornQuotient F)) (BrieskornQuotient F) := by infer_instance
attribute [instance 2200] brieskornScalarComm brieskornScalarSelfTower brieskornEndScalarTower
 def potentialAction (F : P) : BrieskornQuotient F →ₗ[K] BrieskornQuotient F :=
  (divergenceSpace F).mapQ (divergenceSpace F) (LinearMap.mulLeft K F)
    (fun u hu => potential_mul_mem F u hu)
 abbrev BrieskornModule (F : P) := Module.AEval' (potentialAction F)
def palomarBrieskornAddCommGroup (F : P) : AddCommGroup (BrieskornModule F) := inferInstance
attribute [instance 2400] palomarBrieskornAddCommGroup
attribute [reducible] palomarBrieskornAddCommGroup
def palomarBrieskornModule (F : P) : Module K (BrieskornModule F) := inferInstance
attribute [instance 2400] palomarBrieskornModule
attribute [reducible] palomarBrieskornModule
def palomarBrieskornPolynomialModule (F : P) : Module K[X] (BrieskornModule F) := inferInstance
attribute [instance 2400] palomarBrieskornPolynomialModule
attribute [reducible] palomarBrieskornPolynomialModule
 def classOf (F : P) : P →ₗ[K] BrieskornModule F :=
  (Module.AEval'.of (potentialAction F)).toLinearMap.comp (divergenceSpace F).mkQ
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Polynomial Module
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def potentialSubalgebraModule [IsAlgClosed K] (F : P) (w : ι → ℕ) (h : ℕ) (hne : F ≠ 0) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : Module (Algebra.adjoin K {F}) (BrieskornModule F) :=
  letI : AddCommMonoid (BrieskornModule F) := (palomarBrieskornAddCommGroup F).toAddCommMonoid
  letI : Module K[X] (BrieskornModule F) := palomarBrieskornPolynomialModule F
  Module.compHom (BrieskornModule F)
    (potentialParameterEquiv F w h hne hh hF).symm.toRingHom
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators DirectSum
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
 theorem paper_theorem_6_3_scalar (hn : 2 ≤ n) (F : P)
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
 theorem paper_theorem_6_3_basis_lifts {I : Type*} (hn : 2 ≤ n) (F : P)
    (w : Fin n → ℕ) (h : ℕ) (hne : F ≠ 0)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hiso : IsolatedCriticalPointAtOrigin F)
    (b : I → P) (hbhom : ∀ i, ∃ d : ℕ, (b i).IsWeightedHomogeneous w d)
    (B : Basis I ℂ (MilnorQuotient F))
    (hB : ∀ i, (jacobianSubmodule F).mkQ (b i) = B i) :
    letI := potentialSubalgebraModule F w h hne hh hF
    ∃ basis : Basis I (Algebra.adjoin ℂ {F}) (BrieskornModule F),
      ∀ i, basis i = classOf F (b i) := by sorry
end PaperVerification.JacobianDivergence
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra
 def negativeWeights (w : ι → ℕ) : ι → ℤ := fun i => -(w i : ℤ)
end PaperVerification.NegativeWeightedGrading
namespace PaperVerification.PowerOperators
open MvPolynomial Module
open scoped BigOperators
 def ArtinIndex (n m : ℕ) := {a : Fin n →₀ ℕ // IsArtinExponent m a}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable (R : Type*) [CommRing R] (n : ℕ)
 def ordinaryCoinvariantIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun i : Fin n => esymm (Fin n) R (i.val+1))
def palomarOrdinaryCoinvariantModule : Module R (MvPolynomial (Fin n) R ⧸ ordinaryCoinvariantIdeal R n) := inferInstance
attribute [instance 2400] palomarOrdinaryCoinvariantModule
attribute [reducible] palomarOrdinaryCoinvariantModule
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
local instance palomarPowerRingDecidableEq : DecidableEq ι := Classical.decEq ι
 def euler (i : ι) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i)).comp (pderiv i).toLinearMap
 def component (c lam : R) (i : ι) (k : ℕ) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  (LinearMap.mulLeft R (X i ^ k)).comp
    ((c + lam * (k : R)) • LinearMap.id + lam • euler i)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R]
attribute [local instance] PaperVerification.PowerOperators.palomarPowerRingDecidableEq
variable [Fintype ι]
 def reversed (c : ι → R) (lam : R) (k : ℕ) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, component (c i) lam i k
 def original (c : ι → R) (lam : R) (k : ℕ) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  ∑ i, (LinearMap.mulLeft R (X i ^ k)).comp
    (c i • LinearMap.id + lam • euler i)
 def tailHit (c : ι → R) (lam : R) (m : ℕ) : Submodule R (MvPolynomial ι R) :=
  Submodule.span R {p | ∃ k, m ≤ k ∧ ∃ q, p = reversed c lam k q}
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
 def polynomialPermutationAction (R : Type*) [CommRing R] (G : Subgroup (Equiv.Perm (Fin n))) : Representation R G (MvPolynomial (Fin n) R) where
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
theorem rename_mem_tailHit (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R) (hfix : ∀ i, c (e i) = c i) (m : ℕ) {p : MvPolynomial (Fin n) R} (hp : p ∈ tailHit c lam m) : MvPolynomial.rename e p ∈ tailHit c lam m := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local instance palomarPowerFieldDecidableEq : DecidableEq ι := Classical.decEq ι
 def originalTailHit (c : ι → K) (lam : K) (m : ℕ) : Submodule K (MvPolynomial ι K) :=
  Submodule.span K {p | ∃ k, m ≤ k ∧ ∃ q, p = original c lam k q}
 def originalTailQuotientDegree (c : ι → K) (lam : K) (m d : ℕ) : Submodule K (MvPolynomial ι K ⧸ originalTailHit c lam m) :=
  PalomarDeformedSupport.explicitMap (originalTailHit c lam m).mkQ (homogeneousSubmodule ι K d)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
theorem rename_mem_originalTailHit (e : Equiv.Perm (Fin n)) (c : Fin n → K) (lam : K) (hfix : ∀ i, c (e i) = c i) (m : ℕ) {p : MvPolynomial (Fin n) K} (hp : p ∈ originalTailHit c lam m) : MvPolynomial.rename e p ∈ originalTailHit c lam m := by sorry
 abbrev powerSumIdeal (K : Type*) [Field K] (n m : ℕ) : Ideal (MvPolynomial (Fin n) K) := ordinaryFamilyIdeal (powerSumFamily K n m)
end PaperVerification.PowerOperators
namespace PalomarDeformed
open scoped BigOperators
open MvPolynomial Module Representation
open scoped BigOperators Classical
open PaperVerification PaperVerification.PowerOperators
variable {K : Type*} [Field K] {n : ℕ}
 def originalHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (originalTailQuotientDegree c lam m d) : ℤ)
 def qIntegerPolynomial (j : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range j, Polynomial.X ^ i
end PalomarDeformed
namespace PaperVerification.PowerOperators
open MvPolynomial Module Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
 def tailQuotientDegree (c : Fin n → R) (lam : R) (m d : ℕ) : Submodule R (MvPolynomial (Fin n) R ⧸ tailHit c lam m) :=
  (homogeneousSubmodule (Fin n) R d).map (tailHit c lam m).mkQ
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation Module
variable {K : Type*} [Field K] {n : ℕ}
 def ordinaryCoinvariantDegree (K : Type*) [Field K] (n d : ℕ) : Submodule K (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientDegree (elementaryCoinvariantFamily K n) d
end PaperVerification.PowerOperators
namespace PaperVerification
open MvPolynomial Representation Module
open scoped BigOperators
 def GradedRepresentationEquivalent {K G V W : Type*} [Semiring K] [Monoid G] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] (ρ : Representation K G V) (σ : Representation K G W) (A : ℕ → Submodule K V) (B : ℕ → Submodule K W) : Prop :=
  ∃ e : ρ.Equiv σ, ∀ d x, x ∈ A d ↔ e x ∈ B d
end PaperVerification
namespace PaperVerification.QuotientLinearAction
variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
 def action (ρ : G →* Module.End K V) (U : Submodule K V) (hU : ∀ g x, x ∈ U → ρ g x ∈ U) : G →* Module.End K (V ⧸ U) where
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
theorem palomarOrdinaryAction_preserves (G : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → P) (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i) :
    ∀ (g : G) (p : P), p ∈ ordinaryFamilyIdeal f → polynomialPermutationAction K G g p ∈ ordinaryFamilyIdeal f := by
  sorry
 def ordinaryQuotientAction (G : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → P) (hinv : ∀ g : G, ∀ i, MvPolynomial.rename (g : Equiv.Perm (Fin n)) (f i) = f i) : Representation K G (P ⧸ ordinaryFamilyIdeal f) :=
  QuotientLinearAction.action (polynomialPermutationAction K G)
    ((ordinaryFamilyIdeal f).restrictScalars K) (palomarOrdinaryAction_preserves G f hinv)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
theorem palomarOriginalTailAction_preserves (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ) (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) :
    ∀ (g : G) (p : MvPolynomial (Fin n) K), p ∈ originalTailHit c lam m → polynomialPermutationAction K G g p ∈ originalTailHit c lam m := by
  sorry
 def originalTailQuotientAction (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ) (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) : Representation K G (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m) :=
  QuotientLinearAction.action (polynomialPermutationAction K G)
    (originalTailHit c lam m) (palomarOriginalTailAction_preserves G c lam m hfix)
 def powerSumAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) : Representation K G (MvPolynomial (Fin n) K ⧸ powerSumIdeal K n m) :=
  ordinaryQuotientAction G (powerSumFamily K n m) (powerSumFamily_invariant G m)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Representation Module
variable {K : Type*} [Field K] {n : ℕ}
 def completeHomogeneousAction (G : Subgroup (Equiv.Perm (Fin n))) (m : ℕ) : Representation K G (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) :=
  ordinaryQuotientAction G (completeHomogeneousFamily K n m)
    (completeHomogeneousFamily_invariant G m)
 def ordinaryCoinvariantAction (G : Subgroup (Equiv.Perm (Fin n))) : Representation K G (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  ordinaryQuotientAction G (elementaryCoinvariantFamily K n)
    (elementaryCoinvariantFamily_invariant G)
 def originalCoinvariantRepresentation (α : K) : Representation K (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1) :=
  (originalTailQuotientAction ⊤ (fun _ : Fin n => (1 : K)) α 1
    (fun _ _ => rfl)).comp (permutationToTop n)
 def ordinaryCoinvariantRepresentation : Representation K (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) K ⧸ ordinaryCoinvariantIdeal K n) :=
  (ordinaryCoinvariantAction ⊤).comp (permutationToTop n)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
variable (G : Subgroup (Equiv.Perm (Fin n))) (c : Fin n → K) (lam : K) (m : ℕ)
variable (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i)
 def tailQuotientAction : Representation K G (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  QuotientLinearAction.action (polynomialPermutationAction K G) (tailHit c lam m)
    (fun g _ hp => rename_mem_tailHit (g : Equiv.Perm (Fin n)) c lam (hfix g) m hp)
end PaperVerification.PowerOperators
namespace PaperVerification.PowerOperators
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
theorem paper_theorem_1_1 (α : K) : (α ∉ exceptionalSet K n → (∃ B : Basis (ArtinIndex n 1) K (MvPolynomial (Fin n) K ⧸ originalTailHit (fun _ => (1 : K)) α 1), ∀ a, B a = (originalTailHit (fun _ => (1 : K)) α 1).mkQ (monomial a.val 1)) ∧ PaperVerification.GradedRepresentationEquivalent (originalCoinvariantRepresentation α) (ordinaryCoinvariantRepresentation (K := K) (n := n)) (originalTailQuotientDegree (fun _ : Fin n => (1 : K)) α 1) (ordinaryCoinvariantDegree K n)) ∧ (2 ≤ n → (artinSpan K n 1).map (originalTailHit (fun _ : Fin n => (1 : K)) α 1).mkQ = ⊤ → α ∉ exceptionalSet K n) := by sorry
end PaperVerification.PowerOperators
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
local instance vectorEulerBasicDecidableEq : DecidableEq ι := Classical.decEq ι
 def potential (F : κ → P) : P →ₗ[K] M where
  toFun p a := F a * p
  map_add' p q := by funext a; exact mul_add _ _ _
  map_smul' c p := by funext a; exact mul_smul_comm _ _ _
end PaperVerification.VectorEuler
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
 def integerWeights (w : ι → ℕ) : ι → ℤ := fun i => (w i : ℤ)
 def targetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) : Submodule K M :=
  Submodule.pi Set.univ fun a =>
    weightedHomogeneousSubmodule K (integerWeights w) (e + (h a : ℤ))
 def quotientTargetPiece (w : ι → ℕ) (h : κ → ℕ) (e : ℤ) (U : Submodule K M) : Submodule K (M ⧸ U) := PalomarDeformedSupport.explicitMap U.mkQ (targetPiece w h e)
end PaperVerification.VectorEuler
namespace PaperVerification.VectorJacobian
open scoped BigOperators
open MvPolynomial
variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def jacobianMap (F : κ → P) : (ι → P) →ₗ[K] (κ → P) where
  toFun g a := ∑ i, pderiv i (F a) * g i
  map_add' g h := by
    funext a
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext a
    simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm, Finset.smul_sum]
 def normalizedJacobianMap (F : κ → P) (h : κ → ℕ) : (ι → P) →ₗ[K] (κ → P) where
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
attribute [local instance] PaperVerification.VectorEuler.vectorEulerBasicDecidableEq
 def aggregate (F : κ → P) (h : κ → ℕ) (t : K) : (ι → P) →ₗ[K] M :=
  EulerReduction.perturbed (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (potential F) t
 def coefficientSpace (F : κ → P) (h : κ → ℕ) : Submodule K M :=
  PalomarDeformedSupport.explicitRange (VectorJacobian.normalizedJacobianMap F h)
 def hit (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K M :=
  PalomarDeformedSupport.explicitRange (aggregate F h t)
 abbrev Defect (F : κ → P) (h : κ → ℕ) (t : K) :=
  coefficientSpace F h ⧸ (hit F h t).comap (coefficientSpace F h).subtype
 def defectImage (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K (M ⧸ hit F h t) :=
  PalomarDeformedSupport.explicitMap (hit F h t).mkQ (coefficientSpace F h)
 def potentialToQuotient (F : κ → P) (h : κ → ℕ) (t : K) : P →ₗ[K] (M ⧸ hit F h t) := (hit F h t).mkQ.comp (potential F)
theorem potentialToQuotient_range (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) : LinearMap.range (potentialToQuotient F h t) = defectImage F h t := by sorry
 def defectEquivImage (F : κ → P) (h : κ → ℕ) (t : K) : Defect F h t ≃ₗ[K] defectImage F h t :=
  EulerInjective.defectEquivImage (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (potential F) t
 def homogeneousPotentialMap (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) : weightedHomogeneousSubmodule K w d →ₗ[K] defectImage F h t :=
  ((potentialToQuotient F h t).domRestrict (weightedHomogeneousSubmodule K w d)).codRestrict
    (defectImage F h t) (fun p => by
      rw [← potentialToQuotient_range F h w t hh hF]
      exact ⟨p, rfl⟩)
theorem homogeneousPotentialMap_bijective (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h)) (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) : Function.Bijective (homogeneousPotentialMap F h w t d hh hF) := by sorry
 def homogeneousDefectEquiv (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h)) (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) : weightedHomogeneousSubmodule K w d ≃ₗ[K] defectImage F h t :=
  LinearEquiv.ofBijective (homogeneousPotentialMap F h w t d hh hF)
    (homogeneousPotentialMap_bijective F h w t d hh hF hC hres)
end PaperVerification.VectorEuler
namespace PaperVerification.VectorEuler
open MvPolynomial RingTheory.Sequence
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
theorem regular_coefficient_injective (F : Fin n → P) (h w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (hreg : IsWeaklyRegular P (List.ofFn F)) : Function.Injective (VectorJacobian.normalizedJacobianMap F h) := by sorry
 def regularDefectEquiv (hn : 0 < n) (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a) (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) (hreg : IsWeaklyRegular P (List.ofFn F)) : weightedHomogeneousSubmodule K w d ≃ₗ[K] Defect F h (-(1 : K) / ((∑ i, w i : ℕ) + d : K)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
  have hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0 := by
    simpa only [Nat.cast_one] using (EulerJacobian.eigenvalue_zero_iff w hw 1 d t).mpr
      (by simp only [Nat.cast_one, t])
  exact (homogeneousDefectEquiv F h w t d hh hF
    (regular_coefficient_injective F h w hw hh hF hreg) hres).trans
      (defectEquivImage F h t).symm
 theorem paper_proposition_6_5_scalar (hn : 0 < n)
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
namespace TauCeti
open scoped DirectSum
theorem DirectSum.isInternal_comap {R ι M N : Type*} [Semiring R] [DecidableEq ι] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] (𝓝 : ι → Submodule R N) (f : N →ₗ[R] M) (hf : Function.Injective f) (hmem : ∀ i x, x ∈ 𝓝 i ↔ f x ∈ ℳ i) (hproj : ∀ i x, (DirectSum.decompose ℳ (f x) i : M) ∈ LinearMap.range f) : DirectSum.IsInternal 𝓝 := by sorry
end TauCeti
namespace TauCeti
open scoped DirectSum
universe u v w
variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
 structure InternalGrading (ι : Type := ℤ) [DecidableEq ι] where
  piece : ι → Submodule R M
  isInternal : DirectSum.IsInternal piece
end TauCeti
namespace TauCeti.InternalGrading
open scoped DirectSum
universe u v w
variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
variable {R M} {ι : Type} [DecidableEq ι]
noncomputable instance canonicalDecomposition (G : InternalGrading R M ι) : DirectSum.Decomposition G.piece :=
  G.isInternal.chooseDecomposition
theorem palomarDecomposition_isInternal (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] : DirectSum.IsInternal ℳ := by sorry
 noncomputable def ofDecomposition (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ] : InternalGrading R M ι :=
  ⟨ℳ, palomarDecomposition_isInternal ℳ⟩
end TauCeti.InternalGrading
namespace PaperVerification.GradedTowers
open scoped DirectSum
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {G : Type*} [Monoid G]
 def pieceRepresentation (GW : TauCeti.InternalGrading K W) (σ : Representation K G W) (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (p : ℤ) : Representation K G (GW.piece p) :=
  σ.subrepresentation (GW.piece p) (fun g x hx => hσ g p x hx)
 def shiftedPiecesRepresentation (GW : TauCeti.InternalGrading K W) (σ : Representation K G W) (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (h : ℕ) (p : ℤ) : Representation K G (⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) :=
  Representation.directSum fun j : ℕ => pieceRepresentation GW σ hσ (p + (j : ℤ) * h)
end PaperVerification.GradedTowers
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra
 def grading (w : ι → ℕ) : TauCeti.InternalGrading K P :=
  .ofDecomposition (weightedHomogeneousSubmodule K (negativeWeights w))
end PaperVerification.NegativeWeightedGrading
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
theorem submodule_homogeneous (w : ι → ℕ) (U : Submodule K P) (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) : DirectSum.SetLike.IsHomogeneous (grading (K := K) w).piece U := by sorry
end PaperVerification.NegativeWeightedGrading
namespace TauCeti.InternalGrading
open _root_.DirectSum
variable {R M : Type*} {ι : Type} [DecidableEq ι]
variable {S : Type*} [Semiring R] [Semiring S] [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)
include hU
 theorem palomarSubmoduleIsInternal : DirectSum.IsInternal (fun p => (G.piece p).comap (U.subtype.restrictScalars R)) :=
  DirectSum.isInternal_comap G.piece _ (U.subtype.restrictScalars R)
    Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun p x ↦ ⟨⟨_, hU p x.2⟩, rfl⟩
noncomputable def submodule : InternalGrading R U ι where
  piece p := (G.piece p).comap (U.subtype.restrictScalars R)
  isInternal := palomarSubmoduleIsInternal G U hU
end TauCeti.InternalGrading
namespace TauCeti.InternalGrading
open _root_.DirectSum
variable {R M : Type*} {ι : Type} [DecidableEq ι]
variable {S : Type*} [Semiring R] [Semiring S] [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)
theorem submodule_piece (p : ι) : (G.submodule U hU).piece p = (G.piece p).comap (U.subtype.restrictScalars R) := by sorry
end TauCeti.InternalGrading
namespace TauCeti.InternalGrading
open _root_.DirectSum
variable {R M : Type*} {ι : Type} [DecidableEq ι]
variable {S : Type*} [Ring R] [Ring S] [SMul R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (G : InternalGrading R M ι) (U : Submodule S M) (hU : SetLike.IsHomogeneous G.piece U)
include hU
include hU in
theorem palomarQuotient_isInternal : DirectSum.IsInternal (fun p => (G.piece p).map (U.mkQ.restrictScalars R)) := by
  sorry
 noncomputable def quotient : InternalGrading R (M ⧸ U) ι where
  piece p := (G.piece p).map (U.mkQ.restrictScalars R)
  isInternal := palomarQuotient_isInternal G U hU
end TauCeti.InternalGrading
namespace PaperVerification.NegativeWeightedGrading
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def quotientGrading (w : ι → ℕ) (U : Submodule K P) (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) : TauCeti.InternalGrading K (P ⧸ U) :=
  (grading w).quotient U (submodule_homogeneous w U hU)
end PaperVerification.NegativeWeightedGrading
namespace PaperVerification.JacobianDivergence
open MvPolynomial
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
 def milnorNegativeGrading (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h) : TauCeti.InternalGrading K (MilnorQuotient F) :=
  NegativeWeightedGrading.quotientGrading w (jacobianSubmodule F)
    (homogeneousComponent_mem_jacobian F w h hF)
end PaperVerification.JacobianDivergence
namespace MvPolynomial
open Matrix MulOpposite
variable {σ R : Type*} [Fintype σ] [CommSemiring R]
 noncomputable def linearSubst (M : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ ∑ j, C (M i j) * X j
theorem linearSubst_one [DecidableEq σ] : linearSubst (1 : Matrix σ σ R) = AlgHom.id R _ := by sorry
theorem linearSubst_mul_apply (M N : Matrix σ σ R) (p : MvPolynomial σ R) : linearSubst (M * N) p = linearSubst N (linearSubst M p) := by sorry
end MvPolynomial
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
theorem linearSubst_mem_jacobianSubmodule (M : GL) (F : P) (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P) (hp : p ∈ jacobianSubmodule F) : linearSubst (M : Matrix ι ι K) p ∈ jacobianSubmodule F := by sorry
theorem linearSubst_mem_hit (M : GL) (F : P) (t : K) (hF : linearSubst (M : Matrix ι ι K) F = F) (p : P) (hp : p ∈ EulerJacobian.hit (gradient F) F t) : linearSubst (M : Matrix ι ι K) p ∈ EulerJacobian.hit (gradient F) F t := by sorry
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianLinearAction
open MvPolynomial Matrix JacobianDivergence
open scoped BigOperators Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
variable {G : Type*} [Group G]
 abbrev polynomialRepresentation (ρ : G →* GL) : Representation K G P where
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
 def milnorRepresentation (ρ : G →* GL) (F : P) (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) : Representation K G (MilnorQuotient F) :=
  (polynomialRepresentation ρ).quotient (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hF g⁻¹) p hp)
 def hitQuotientRepresentation (ρ : G →* GL) (F : P) (t : K) (hF : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) : Representation K G (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (polynomialRepresentation ρ).quotient (EulerJacobian.hit (gradient F) F t)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hF g⁻¹) p hp)
theorem polynomialRepresentation_preserves_weights {D : Type*} [AddCommMonoid D] (ρ : G →* GL) (w : ι → D) (hW : ∀ g, RespectsWeights w (ρ g : Matrix ι ι K)) (g : G) {p : P} {d : D} (hp : p.IsWeightedHomogeneous w d) : (polynomialRepresentation ρ g p).IsWeightedHomogeneous w d := by sorry
end PaperVerification.JacobianLinearAction
namespace PaperVerification.VectorEuler
open MvPolynomial
open scoped BigOperators
variable {K ι κ G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
local notation "GL" => (Matrix ι ι K)ˣ
 abbrev targetRepresentation (ρ : G →* GL) : Representation K G M where
  toFun g := LinearMap.pi fun a =>
    (JacobianLinearAction.polynomialRepresentation ρ g).comp (LinearMap.proj a)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext a
    exact congrArg (fun f : Module.End K P => f (v a))
      (JacobianLinearAction.polynomialRepresentation ρ).map_one
  map_mul' g g' := by
    apply LinearMap.ext
    intro v
    funext a
    exact congrArg (fun f : Module.End K P => f (v a))
      ((JacobianLinearAction.polynomialRepresentation ρ).map_mul g g')
 theorem targetRepresentation_preserves_coefficient (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (hF : ∀ g a, linearSubst (ρ g : Matrix ι
  ι K) (F a) = F a) (g : G) (v : M) (hv : v ∈ coefficientSpace F h) : targetRepresentation ρ g v ∈ coefficientSpace F h := by
  sorry
theorem targetRepresentation_preserves_hit (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K) (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) (g : G) (v : M) (hv : v ∈ hit F h t) : targetRepresentation ρ g v ∈ hit F h t := by sorry
 def coefficientRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) : Representation K G (coefficientSpace F h) :=
  (targetRepresentation ρ).subrepresentation (coefficientSpace F h)
    (fun g v hv => targetRepresentation_preserves_coefficient ρ F h hF g v hv)
 def defectQuotientRepresentation (ρ : G →* GL) (F : κ → P) (h : κ → ℕ) (t : K) (hF : ∀ g a, linearSubst (ρ g : Matrix ι ι K) (F a) = F a) : Representation K G (Defect F h t) :=
  (coefficientRepresentation ρ F h hF).quotient
    ((hit F h t).comap (coefficientSpace F h).subtype)
    (fun g v hv => targetRepresentation_preserves_hit ρ F h t hF g v hv)
 def homogeneousPolynomialRepresentation (ρ : G →* GL) (w : ι → ℕ) (d : ℕ) (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) : Representation K G (weightedHomogeneousSubmodule K w d) :=
  (JacobianLinearAction.polynomialRepresentation ρ).subrepresentation
    (weightedHomogeneousSubmodule K w d)
    (fun g p hp => JacobianLinearAction.polynomialRepresentation_preserves_weights ρ w hW g hp)
end PaperVerification.VectorEuler
namespace PaperVerification.VectorEuler
open MvPolynomial RingTheory.Sequence
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
 theorem paper_proposition_6_5_equivariant {G : Type*} [Group G]
    (hn : 0 < n) (F : Fin n → P) (h w : Fin n → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hreg : IsWeaklyRegular P (List.ofFn F))
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix (Fin n) (Fin n) K))
    (hFix : ∀ g a, linearSubst (ρ g : Matrix (Fin n) (Fin n) K) (F a) = F a)
    (g : G) (p : weightedHomogeneousSubmodule K w d) :
    let t : K := -(1 : K) / ((∑ i, w i : ℕ) + d : K)
    regularDefectEquiv hn F h w d hw hh hF hreg
        (homogeneousPolynomialRepresentation ρ w d hW g p) =
      defectQuotientRepresentation ρ F h t hFix g
        (regularDefectEquiv hn F h w d hw hh hF hreg p) := by sorry
end PaperVerification.VectorEuler
namespace PaperVerification.JacobianLinearAction
open MvPolynomial JacobianDivergence
open scoped BigOperators
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι] [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
 def jacobianRepresentation (ρ : G →* GL) (F : P) (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) : Representation K G (jacobianSubmodule F) :=
  (polynomialRepresentation ρ).subrepresentation (jacobianSubmodule F)
    (fun g p hp => linearSubst_mem_jacobianSubmodule (ρ g⁻¹) F (hFix g⁻¹) p hp)
 def defectQuotientRepresentation (ρ : G →* GL) (F : P) (t : K) (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) : Representation K G (DefectQuotient F t) :=
  (jacobianRepresentation ρ F hFix).quotient
    ((EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype)
    (fun g p hp => linearSubst_mem_hit (ρ g⁻¹) F t (hFix g⁻¹) p hp)
end PaperVerification.JacobianLinearAction
namespace PaperVerification.JacobianDivergence
open MvPolynomial
open scoped DirectSum BigOperators
variable {K ι G : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
variable [Group G]
local notation "P" => MvPolynomial ι K
local notation "GL" => (Matrix ι ι K)ˣ
theorem milnorRepresentation_preserves_negativeGrading (ρ : G →* GL) (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h) (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) : ∀ g p x, x ∈ (milnorNegativeGrading F w h hF).piece p → JacobianLinearAction.milnorRepresentation ρ F hFix g x ∈ (milnorNegativeGrading F w h hF).piece p := by sorry
 def milnorTowerRepresentation (ρ : G →* GL) (F : P) (w : ι → ℕ) (h d : ℕ) (hF : F.IsWeightedHomogeneous w h) (hFix : ∀ g, linearSubst (ρ g : Matrix ι ι K) F = F) (hW : ∀ g, JacobianLinearAction.RespectsWeights w (ρ g : Matrix ι ι K)) : Representation K G (⨁ j : ℕ, (milnorNegativeGrading F w h hF).piece (-(d : ℤ) + (j : ℤ) * h)) :=
  GradedTowers.shiftedPiecesRepresentation (milnorNegativeGrading F w h hF)
    (JacobianLinearAction.milnorRepresentation ρ F hFix)
    (milnorRepresentation_preserves_negativeGrading ρ F w h hF hFix hW) h (-(d : ℤ))
end PaperVerification.JacobianDivergence
namespace PaperVerification.JacobianDivergence
open MvPolynomial Module
open scoped BigOperators DirectSum
variable {n : ℕ}
local notation "P" => MvPolynomial (Fin n) ℂ
 theorem paper_theorem_6_3_equivariant {G : Type*} [Group G] [Fintype G]
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
namespace PalomarDeformed
open scoped BigOperators
open MvPolynomial Module Representation
open scoped BigOperators Classical
open PaperVerification PaperVerification.PowerOperators
variable {K : Type*} [Field K] {n : ℕ}
 def tailHilbertSeries (c : Fin n → K) (lam : K) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d => (Module.finrank K (tailQuotientDegree c lam m d) : ℤ)
theorem weighted_tail_theorem (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m) (hnr : Nonresonant c lam m) : (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m), ∀ a, B a = (tailHit c lam m).mkQ (monomial a.val 1)) ∧ (tailHilbertSeries c lam m = ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧ (∀ (G : Subgroup (Equiv.Perm (Fin n))) (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i), GradedRepresentationEquivalent (tailQuotientAction G c lam m hfix) (completeHomogeneousAction G m) (tailQuotientDegree c lam m) (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧ (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)), GradedRepresentationEquivalent (tailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl)) (powerSumAction G m) (tailQuotientDegree (fun _ : Fin n => a) lam m) (ordinaryQuotientDegree (powerSumFamily K n m))) ∧ (∀ hlow : ∀ i, ∀ a : ℕ, a < m → c i + lam * (a : K) ≠ 0, (∃ B : Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ originalTailHit c lam m), ∀ a, B a = (originalTailHit c lam m).mkQ (monomial a.val 1)) ∧ (originalHilbertSeries c lam m = ((∏ j ∈ Finset.Ico m (m+n), qIntegerPolynomial j : Polynomial ℤ) : PowerSeries ℤ)) ∧ (∀ (G : Subgroup (Equiv.Perm (Fin n))) (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i), GradedRepresentationEquivalent (originalTailQuotientAction G c lam m hfix) (completeHomogeneousAction G m) (originalTailQuotientDegree c lam m) (ordinaryQuotientDegree (completeHomogeneousFamily K n m))) ∧ (∀ a : K, (∀ i, c i = a) → ∀ G : Subgroup (Equiv.Perm (Fin n)), GradedRepresentationEquivalent (originalTailQuotientAction G (fun _ : Fin n => a) lam m (fun _ _ => rfl)) (powerSumAction G m) (originalTailQuotientDegree (fun _ : Fin n => a) lam m) (ordinaryQuotientDegree (powerSumFamily K n m)))) := by sorry
end PalomarDeformed

end
end
namespace PalomarDiagnostic
meta partial def parents (e : Lean.Expr) (path : Array String := #[]) : StateM (Nat × Array Lean.Json) Unit := do
  let (fuel, rows) ← get
  if fuel == 0 || rows.size >= 16 then return
  set (fuel - 1, rows)
  let args := e.getAppArgs
  if args.any (fun a => match a.getAppFn with | .const n _ => (n.toString.splitOn "._proof_").length > 1 | _ => false) then
    let head := match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant"
    let heads := args.map fun a => match a.getAppFn with | .const n _ => n.toString | .bvar i => "bvar" ++ toString i | _ => "other"
    modify fun (f, rs) => (f, rs.push (Lean.Json.mkObj [("parent", Lean.toJson head), ("argument_heads", Lean.toJson heads), ("path", Lean.toJson path)]))
  match e with
  | .app .. => for i in [:args.size] do parents args[i]! (path.push ((match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant") ++ ":" ++ toString i))
  | .lam _ t b _ | .forallE _ t b _ => parents t path; parents b path
  | .letE _ t v b _ => parents t path; parents v path; parents b path
  | .mdata _ b | .proj _ _ b => parents b path
  | _ => pure ()
end PalomarDiagnostic
run_cmd do
  for n in #[`PaperVerification.JacobianDivergence.defectQuotientEquivImage, `PaperVerification.JacobianDivergence.potentialSubalgebraModule] do
    if let some ci := (← Lean.getEnv).find? n then
      if let some v := ci.value? (allowOpaque := true) then
        let (_, (remaining, rows)) := (do PalomarDiagnostic.parents ci.type; PalomarDiagnostic.parents v).run (100000, #[])
        Lean.logInfo m!"{(Lean.Json.mkObj [("name", Lean.toJson n.toString), ("remaining", Lean.toJson remaining), ("parents", Lean.Json.arr rows)]).compress}"

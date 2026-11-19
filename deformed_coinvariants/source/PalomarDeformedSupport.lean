module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section
namespace PalomarDeformedSupport
universe uK uR uM uS
/-- The actual identity map on the coefficient field is surjective. -/
theorem fieldIdentitySurjective {K : Type uK} [Field K] : RingHomSurjective (RingHom.id K) := by infer_instance
/-- The literal identity coefficient maps compose. -/
theorem fieldIdentityCompTriple {K : Type uK} [Field K] : RingHomCompTriple (RingHom.id K) (RingHom.id K) (RingHom.id K) := by infer_instance
/-- The actual coefficient identity map is its own inverse. -/
theorem fieldIdentityInvPair {K : Type uK} [Field K] : RingHomInvPair (RingHom.id K) (RingHom.id K) := by infer_instance
/-- The identity map on any coefficient ring is surjective. -/
theorem ringIdentitySurjective {R : Type uR} [Ring R] : RingHomSurjective (RingHom.id R) := by infer_instance
/-- Permutation subgroups carry their actual submonoid membership laws. -/
theorem permutationSubmonoid (n : ℕ) : SubmonoidClass (Subgroup (Equiv.Perm (Fin n))) (Equiv.Perm (Fin n)) := by infer_instance
/-- Submodules retain their actual additive-submonoid laws. -/
theorem submoduleAddSubmonoid {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M] : AddSubmonoidClass (Submodule R M) M := by infer_instance
/-- Scalar restriction on the actual subtype uses the original scalar actions. -/
theorem subtypeScalarCompatible {R : Type uR} {M : Type uM} {S : Type uS} [Semiring R] [Semiring S] [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (U : Submodule S M) : LinearMap.CompatibleSMul U M R S := by infer_instance
/-- Scalar restriction on the actual quotient uses the original scalar actions. -/
theorem quotientScalarCompatible {R : Type uR} {M : Type uM} {S : Type uS} [Ring R] [Ring S] [SMul R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (U : Submodule S M) : LinearMap.CompatibleSMul M (M ⧸ U) R S := by infer_instance
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
end PalomarDeformedSupport
end

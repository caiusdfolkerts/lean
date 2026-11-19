module
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
namespace PalomarDeformedSupport
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
example (e : M ≃ₗ[K] N) (f : N ≃ₗ[K] O) : explicitEquivTrans e f = e.trans f := rfl
end PalomarDeformedSupport

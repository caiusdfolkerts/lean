module
public import Mathlib.Algebra.Module.Submodule.Range
@[expose] public section
namespace PalomarDeformedSupport
universe u v w
theorem mapIdentitySurjective {K : Type u} [CommRing K] : RingHomSurjective (RingHom.id K) := by infer_instance
variable {K : Type u} {M : Type v} {N : Type w} [CommRing K]
  [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]
def explicitMap (f : M →ₗ[K] N) (p : Submodule K M) : Submodule K N :=
  @Submodule.map K K M N _ _ _ _ _ _ (RingHom.id K) mapIdentitySurjective f p
def explicitRange (f : M →ₗ[K] N) : Submodule K N :=
  @LinearMap.range K K M N _ _ _ _ _ _ (RingHom.id K) mapIdentitySurjective f
example (f : M →ₗ[K] N) (p : Submodule K M) : explicitMap f p = p.map f := rfl
example (f : M →ₗ[K] N) : explicitRange f = LinearMap.range f := rfl
end PalomarDeformedSupport

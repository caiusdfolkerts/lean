module
public import Mathlib
@[expose] public noncomputable section
universe u v w x
variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} {Z : Type x}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]
def actualKernelElement (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : g.comp f = 0) (z : X) : LinearMap.ker g :=
  ⟨f z, by
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun h z⟩
theorem actualKernelElement_val (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : g.comp f = 0) (z : X) : (actualKernelElement f g h z).val = f z := rfl
#print axioms actualKernelElement
#print axioms actualKernelElement_val

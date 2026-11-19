module

public import ToricPower.DivisorWeightTensorNaturality
public import ToricPower.SchemeModulesBaseLinear
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# The actual tensor product is linear over the scheme's base ring

The proof uses the genuine inserted pure tensors and the actual action
of a base scalar as multiplication by a restricted global function. Thus
tensoring retains the specified scheme scalar action.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace ToricPower
private theorem tensorLinearMap_smul_right {S M N P : Type*}
    [CommRing S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P]
    (f : M ⊗[S] N →ₗ[S] P) (a : S) (s : M) (t : N) :
    f (s ⊗ₜ[S] (a • t)) = a • f (s ⊗ₜ[S] t) := by
  rw [TensorProduct.tmul_smul, map_smul]

private theorem tensorLinearMap_smul_left {S M N P : Type*}
    [CommRing S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P]
    (f : M ⊗[S] N →ₗ[S] P) (a : S) (s : M) (t : N) :
    f ((a • s) ⊗ₜ[S] t) = a • f (s ⊗ₜ[S] t) := by
  rw [← TensorProduct.smul_tmul', map_smul]

universe u
variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The genuine pure-tensor insertion is linear in its second argument. -/
theorem schemeTensorSection_smul_right (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    schemeTensorSection M N U s (a • t) = a • schemeTensorSection M N U s t := by
  exact tensorLinearMap_smul_right
    (S := X.sheaf.obj.obj (op U))
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget X.ringCatSheaf) M N).app (op U)).hom
    a s t

/-- The genuine pure-tensor insertion is linear in its first argument. -/
theorem schemeTensorSection_smul_left (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (s : Γ(M, U)) (t : Γ(N, U)) :
    schemeTensorSection M N U (a • s) t = a • schemeTensorSection M N U s t := by
  exact tensorLinearMap_smul_left
    (S := X.sheaf.obj.obj (op U))
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget X.ringCatSheaf) M N).app (op U)).hom
    a s t

/-- Left tensoring preserves the actual base-ring scalar on sheaf maps. -/
instance schemeTensorLeft_baseLinear (M : X.Modules) : (tensorLeft M).Linear R where
  map_smul {N P} f r := by
    apply schemeTensorHom_ext
    intro U s t
    change Scheme.Modules.Hom.app (M ◁ (r • f)) U (schemeTensorSection M N U s t) =
      Scheme.Modules.Hom.app (r • (M ◁ f)) U (schemeTensorSection M N U s t)
    have first := schemeTensorSection_naturality (𝟙 M) (r • f) U s t
    have second := schemeTensorSection_naturality (𝟙 M) f U s t
    rw [id_tensorHom] at first second
    rw [first, Scheme.Modules.base_smul_app, Scheme.Modules.base_smul_app, second]
    exact schemeTensorSection_smul_right X M P U _ s (Scheme.Modules.Hom.app f U t)

/-- Right tensoring preserves the same actual base-ring scalar. -/
instance schemeTensorRight_baseLinear (M : X.Modules) : (tensorRight M).Linear R where
  map_smul {N P} f r := by
    apply schemeTensorHom_ext
    intro U s t
    change Scheme.Modules.Hom.app ((r • f) ▷ M) U (schemeTensorSection N M U s t) =
      Scheme.Modules.Hom.app (r • (f ▷ M)) U (schemeTensorSection N M U s t)
    have first := schemeTensorSection_naturality (r • f) (𝟙 M) U s t
    have second := schemeTensorSection_naturality f (𝟙 M) U s t
    rw [tensorHom_id] at first second
    rw [first, Scheme.Modules.base_smul_app, Scheme.Modules.base_smul_app, second]
    exact schemeTensorSection_smul_left X P M U _ (Scheme.Modules.Hom.app f U s) t

end ToricPower

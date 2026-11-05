module

public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor multiplicity spaces as functors on all linear maps

The symmetric group acts on an actual tensor power by
`σ (⊗ᵢ vᵢ) = ⊗ᵢ v_(σ⁻¹ i)`.  Applying the same linear map in every
factor intertwines this action.  Consequently the multiplicity space of
any fixed symmetric-group representation is functorial in the original
module, including maps between modules of different ranks.

Specializing the fixed representation to a Specht representation gives
the Schur multiplicity functor.  None of the results below assumes a
stable range, a dimension inequality, or invertibility of the input map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace PaperVerification.TensorMultiplicity

universe u v v₁ v₂ w

variable {R : Type u} [CommRing R] {d : ℕ}
variable {M : Type v} {N : Type v₁} {P : Type v₂} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map applied in every tensor factor, as an actual
intertwiner of the permutation actions. -/
def tensorMap (f : M →ₗ[R] N) :
    Representation.IntertwiningMap
      (PiTensorProduct.reindexRepresentation R M (Fin d))
      (PiTensorProduct.reindexRepresentation R N (Fin d)) where
  toLinearMap := PiTensorProduct.map fun _ : Fin d ↦ f
  isIntertwining' σ := by
    simp only [PiTensorProduct.reindexRepresentation_apply]
    exact PiTensorProduct.map_comp_reindex_eq (fun _ : Fin d ↦ f) σ

@[simp] theorem tensorMap_apply (f : M →ₗ[R] N) (v : TensorPower R d M) :
    tensorMap (d := d) f v = PiTensorProduct.map (fun _ : Fin d ↦ f) v := rfl

@[simp] theorem tensorMap_tprod (f : M →ₗ[R] N) (v : Fin d → M) :
    tensorMap (d := d) f (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i ↦ f (v i)) :=
  PiTensorProduct.map_tprod (fun _ : Fin d ↦ f) v

@[simp] theorem tensorMap_id_apply (v : TensorPower R d M) :
    tensorMap (d := d) (LinearMap.id : M →ₗ[R] M) v = v := by
  simp only [tensorMap_apply, PiTensorProduct.map_id, LinearMap.id_apply]

@[simp] theorem tensorMap_comp_apply (g : N →ₗ[R] P) (f : M →ₗ[R] N)
    (v : TensorPower R d M) :
    tensorMap (d := d) (g.comp f) v = tensorMap g (tensorMap f v) := by
  exact congrArg (fun h : TensorPower R d M →ₗ[R] TensorPower R d P ↦ h v)
    (PiTensorProduct.map_comp (fun _ : Fin d ↦ g) (fun _ : Fin d ↦ f))

variable {W : Type w} [AddCommGroup W] [Module R W]
  (ρ : Representation R (Equiv.Perm (Fin d)) W)

/-- The literal equivariant-linear-map multiplicity space. -/
abbrev Space (M : Type v) [AddCommGroup M] [Module R M] :=
  Representation.IntertwiningMap ρ
    (PiTensorProduct.reindexRepresentation R M (Fin d))

/-- Functoriality on every linear map, by postcomposition with its
tensor power. -/
def map (f : M →ₗ[R] N) : Space ρ M →ₗ[R] Space ρ N :=
  Representation.IntertwiningMap.llcomp ρ _ _ (tensorMap f)

@[simp] theorem map_apply (f : M →ₗ[R] N) (s : Space ρ M) (w : W) :
    map ρ f s w = tensorMap f (s w) := rfl

@[simp] theorem map_id : map ρ (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext s w
  exact tensorMap_id_apply (s w)

@[simp] theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map ρ (g.comp f) = (map ρ g).comp (map ρ f) := by
  ext s w
  exact tensorMap_comp_apply g f (s w)

/-- Change of frame on the multiplicity space is an actual linear
equivalence; its inverse comes from the inverse frame. -/
def congr (e : M ≃ₗ[R] N) : Space ρ M ≃ₗ[R] Space ρ N :=
  LinearEquiv.ofLinearMap (map ρ e.toLinearMap) (map ρ e.symm.toLinearMap)
    (by rw [← map_comp, e.comp_symm, map_id])
    (by rw [← map_comp, e.symm_comp, map_id])

@[simp] theorem congr_apply (e : M ≃ₗ[R] N) (s : Space ρ M) :
    congr ρ e s = map ρ e.toLinearMap s := rfl

/-- The multiplicity construction is a functor on the actual category
of modules.  It is polynomial in morphisms, so no additivity of this
functor is asserted. -/
def functor : ModuleCat.{v} R ⥤ ModuleCat.{max v w u} R where
  obj M := ModuleCat.of R (Space ρ M)
  map f := ModuleCat.ofHom (map ρ f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact map_id ρ
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact map_comp ρ g.hom f.hom

end PaperVerification.TensorMultiplicity

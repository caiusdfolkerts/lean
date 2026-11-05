module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Natural ordered multiplication of exterior tensors

The map in this file is defined by the actual ordered exterior product. Its
naturality is proved before any bases, dimensions, coefficient quotients or
representations are introduced. It is intended for the genuine color-block
comparison in Theorem 8.1. 
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion.NaturalExteriorTensor

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {n : ℕ}

/-- Insert each exterior factor into the original exterior algebra, then
multiply in increasing index order. No action is transported to define this map. -/
def assemble (d : Fin n → ℕ) (e : Fin n → V →ₗ[R] W) :
    (⨂[R] i : Fin n, (⋀[R]^(d i) V)) →ₗ[R] ExteriorAlgebra R W :=
  PiTensorProduct.lift <|
    (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R W)).compLinearMap
      (fun i ↦ (ExteriorAlgebra.map (e i)).toLinearMap.comp (Submodule.subtype _))

@[simp] theorem assemble_tprod (d : Fin n → ℕ) (e : Fin n → V →ₗ[R] W)
    (x : ∀ i, ⋀[R]^(d i) V) :
    assemble d e (PiTensorProduct.tprod R x) =
      (List.ofFn (fun i ↦ ExteriorAlgebra.map (e i) (x i))).prod := by
  simp only [assemble, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.coe_subtype]

/-- Naturality for independently specified local maps and an actual global
map, with the commuting square stated on the original vector spaces. -/
theorem assemble_natural (d : Fin n → ℕ) (e : Fin n → V →ₗ[R] W)
    (g : Fin n → V →ₗ[R] V) (h : W →ₗ[R] W)
    (he : ∀ i, h.comp (e i) = (e i).comp (g i)) :
    (ExteriorAlgebra.map h).toLinearMap.comp (assemble d e) =
      (assemble d e).comp (PiTensorProduct.map (fun i ↦ exteriorPower.map (d i) (g i))) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    assemble_tprod, PiTensorProduct.map_tprod, AlgHom.toLinearMap_apply,
    exteriorPower.coe_map, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change ((ExteriorAlgebra.map h).comp (ExteriorAlgebra.map (e i))) (x i) =
    ((ExteriorAlgebra.map (e i)).comp (ExteriorAlgebra.map (g i))) (x i)
  rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, he i]

/-- The vector form of the same commuting square, for arbitrary tensors. -/
theorem assemble_natural_apply (d : Fin n → ℕ) (e : Fin n → V →ₗ[R] W)
    (g : Fin n → V →ₗ[R] V) (h : W →ₗ[R] W)
    (he : ∀ i, h.comp (e i) = (e i).comp (g i))
    (x : ⨂[R] i : Fin n, (⋀[R]^(d i) V)) :
    ExteriorAlgebra.map h (assemble d e x) =
      assemble d e (PiTensorProduct.map (fun i ↦ exteriorPower.map (d i) (g i)) x) :=
  LinearMap.congr_fun (assemble_natural d e g h he) x

end PaperVerification.Fermion.NaturalExteriorTensor

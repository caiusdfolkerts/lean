module
public import consolidated_dev.minkowski_map_core
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option Elab.async false

section BundlePart0
/- Source: Papers/AffineInterpolation.lean -/





@[expose] public section

/-! Affine interpolation on an arbitrary affinely independent family. -/
noncomputable section
namespace Papers.AffineInterpolation

open Set Module Papers.Coordinates

variable {I V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem exists_affine_interpolant (x : I → V) (hx : AffineIndependent ℝ x)
    (y : I → W) : ∃ f : V →ᵃ[ℝ] W, ∀ i, f (x i)=y i := by
  let v : I → V × ℝ := fun i => homogenize (x i)
  have hv : LinearIndependent ℝ v := (linearIndependent_homogenize_iff x).mpr hx
  let H := Submodule.span ℝ (Set.range v)
  let b : Module.Basis I ℝ H := Module.Basis.span hv
  let f0 : H →ₗ[ℝ] W := b.constr ℝ y
  obtain ⟨L,hL⟩ := LinearMap.exists_extend f0
  let f : V →ᵃ[ℝ] W :=
    { toFun := fun z => L (z,1)
      linear := L.comp (LinearMap.inl ℝ V ℝ)
      map_vadd' p z := by
        change L (z+p,1)=L (z,0)+L (p,1)
        rw [← map_add]
        congr 1
        simp only [Prod.mk_add_mk,zero_add] }
  refine ⟨f,?_⟩
  intro i
  have hbi : (b i : V × ℝ)=v i := Module.Basis.coe_span_apply hv i
  calc
    f (x i)=L (v i) := rfl
    _ = (L.comp H.subtype) (b i) := by change L (v i)=L (b i); rw [hbi]
    _ = f0 (b i) := by rw [hL]
    _ = y i := b.constr_basis ℝ y i

end Papers.AffineInterpolation

end
end
end BundlePart0

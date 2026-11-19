module

public import ToricPower.DiagonalCartierFrames
public import ToricPower.SchemePullbackTensorCoherence

/-!
# Actual tensor-frame transport through an open pullback square

The specified pullback tensor and unit maps carry an exterior product
frame to the tensor of its two actual transported factor maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ToricPower

section TensorSquare

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The actual tensor frame transported around an open base-change
square is the tensor of the two separately transported frames, followed
by the literal tensor insertion of restriction. -/
@[reassoc]
theorem pullbackSquareTensorFrame_map
    (hsq : j ≫ f = g ≫ k) {M N : Y.Modules} {P Q : X.Modules}
    (first : 𝟙_ Y'.Modules ≅ (Scheme.Modules.pullback k).obj M)
    (second : 𝟙_ Y'.Modules ≅ (Scheme.Modules.pullback k).obj N)
    (u : (Scheme.Modules.pullback f).obj M ⟶ P)
    (v : (Scheme.Modules.pullback f).obj N ⟶ Q) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map (schemePullbackTensorFrame k first second).hom ≫
        (pullbackSquareIso f g j k hsq).hom.app (M ⊗ N) ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj (M ⊗ N)) ≫
        (Scheme.Modules.restrictFunctor j).map
          (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N ≫ (u ⊗ₘ v)) =
      (λ_ (𝟙_ X'.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso g).inv ≫
            (Scheme.Modules.pullback g).map first.hom ≫
            (pullbackSquareIso f g j k hsq).hom.app M ≫
            (Scheme.Modules.pullback j).map u ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app P) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
            (Scheme.Modules.pullback g).map second.hom ≫
            (pullbackSquareIso f g j k hsq).hom.app N ≫
            (Scheme.Modules.pullback j).map v ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app Q)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) P Q := by
  let σ := (Scheme.Modules.restrictFunctorIsoPullback j).inv
  have hrestrict :
      σ.app ((Scheme.Modules.pullback f).obj (M ⊗ N)) ≫
          (Scheme.Modules.restrictFunctor j).map
            (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N ≫ (u ⊗ₘ v)) =
        (Scheme.Modules.pullback j).map
            (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N) ≫
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback j) _ _ ≫
          (((Scheme.Modules.pullback j).map u ≫ σ.app P) ⊗ₘ
            ((Scheme.Modules.pullback j).map v ≫ σ.app Q)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor j) P Q := by
    rw [Functor.map_comp, ← σ.naturality_assoc,
      Scheme.Modules.restrictFunctorIsoPullback_inv_tensor]
    simp only [Category.assoc]
    rw [← Functor.LaxMonoidal.μ_natural, tensorHom_comp_tensorHom_assoc,
      ← σ.naturality, ← σ.naturality]
  have hframe : (schemePullbackTensorFrame k first second).hom ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback k) M N =
      (λ_ (𝟙_ Y'.Modules)).inv ≫ (first.hom ⊗ₘ second.hom) := by
    simp only [schemePullbackTensorFrame, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, Category.assoc,
      ← Scheme.Modules.pullbackTensorIsoOfOpenImmersion_hom,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [show (Scheme.Modules.restrictFunctorIsoPullback j).inv = σ from rfl,
    hrestrict, pullbackSquareIso_tensor_assoc,
    ← Functor.map_comp_assoc, hframe,
    Scheme.Modules.pullback_tensor_unit_maps_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

end TensorSquare

end ToricPower

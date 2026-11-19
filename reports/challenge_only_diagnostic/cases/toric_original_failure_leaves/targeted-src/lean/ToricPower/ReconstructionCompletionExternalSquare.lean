module

public import ToricPower.SchemePullbackTensorFrame
public import ToricPower.SchemeExternalSectionRetraction

/-!
# Arbitrary exterior sections through the diagonal square

The actual pullback and ordinary restriction maps carry an arbitrary
tensor of unit-source maps through the geometric diagonal square.
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

/-- Arbitrary unit-source maps are carried around the open square by
the tensor of their separate transports, followed by ordinary restriction. -/
@[reassoc]
theorem pullbackSquareTensorUnitMaps_map
    (hsq : j ≫ f = g ≫ k) {M N : Y.Modules} {P Q : X.Modules}
    (first : 𝟙_ Y'.Modules ⟶ (Scheme.Modules.pullback k).obj M)
    (second : 𝟙_ Y'.Modules ⟶ (Scheme.Modules.pullback k).obj N)
    (u : (Scheme.Modules.pullback f).obj M ⟶ P)
    (v : (Scheme.Modules.pullback f).obj N ⟶ Q) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        (Scheme.Modules.pullback g).map ((λ_ (𝟙_ Y'.Modules)).inv ≫ (first ⊗ₘ second) ≫
          (Scheme.Modules.pullbackTensorIsoOfOpenImmersion k M N).inv) ≫
        (pullbackSquareIso f g j k hsq).hom.app (M ⊗ N) ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj (M ⊗ N)) ≫
        (Scheme.Modules.restrictFunctor j).map
          (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N ≫ (u ⊗ₘ v)) =
      (λ_ (𝟙_ X'.Modules)).inv ≫
        (((Scheme.Modules.pullbackObjUnitIso g).inv ≫
            (Scheme.Modules.pullback g).map first ≫
            (pullbackSquareIso f g j k hsq).hom.app M ≫
            (Scheme.Modules.pullback j).map u ≫
            (Scheme.Modules.restrictFunctorIsoPullback j).inv.app P) ⊗ₘ
          ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
            (Scheme.Modules.pullback g).map second ≫
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
  have hframe : ((λ_ (𝟙_ Y'.Modules)).inv ≫ (first ⊗ₘ second) ≫
          (Scheme.Modules.pullbackTensorIsoOfOpenImmersion k M N).inv) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback k) M N =
      (λ_ (𝟙_ Y'.Modules)).inv ≫ (first ⊗ₘ second) := by
    simp only [Category.assoc,
      ← Scheme.Modules.pullbackTensorIsoOfOpenImmersion_hom,
      Iso.inv_hom_id, Category.comp_id]
  rw [show (Scheme.Modules.restrictFunctorIsoPullback j).inv = σ from rfl,
    hrestrict, pullbackSquareIso_tensor_assoc,
    ← Functor.map_comp_assoc, hframe,
    Scheme.Modules.pullback_tensor_unit_maps_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

end TensorSquare

end ToricPower

module

public import ToricPower.SchemeRestrictionTensor
public import ToricPower.OpenBaseChangeNaturality

/-!
# Canonical tensor and unit coherence of actual scheme pullbacks

These equalities compare the specified pullback, restriction, composition,
and unit maps. In particular, they retain the actual tensor comparison,
rather than replacing it by an unspecified isomorphism of objects.
Development source pending the pinned compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y Z W : Scheme.{u}}

/-- The oplax unit arising from the genuine restriction adjunction is
the usual sectionwise identification of the restricted structure sheaf. -/
theorem restrictAdjunction_oplax_η (j : X ⟶ Y) [IsOpenImmersion j] :
    letI := (restrictAdjunction j).leftAdjointOplaxMonoidal
    Functor.OplaxMonoidal.η (restrictFunctor j) = (restrictUnitIso j).hom := by
  letI := (restrictAdjunction j).leftAdjointOplaxMonoidal
  rw [Adjunction.leftAdjointOplaxMonoidal_η, pushforward_ε, Adjunction.homEquiv_counit]
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change X.presheaf.map (eqToHom (j.preimage_image_eq U).symm).op
      (j.app (j ''ᵁ U) a) = (j.appIso U).hom a
  exact (ConcreteCategory.congr_hom (j.appIso_hom U) a).symm

/-- The actual restriction--pullback isomorphism preserves the specified
structure-sheaf unit map. -/
@[reassoc]
theorem restrictFunctorIsoPullback_inv_comp_unit (j : X ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctorIsoPullback j).inv.app (𝟙_ Y.Modules) ≫
      (restrictUnitIso j).hom = (pullbackObjUnitIso j).hom := by
  letI := (restrictAdjunction j).leftAdjointOplaxMonoidal
  let σ := (restrictFunctorIsoPullback j).inv
  have hσ : conjugateEquiv (restrictAdjunction j) (pullbackPushforwardAdjunction j)
      σ = 𝟙 _ := by
    simp [σ, restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  have h := Adjunction.app_tensorUnit_comp_η_of_conjugateEquiv _ _ hσ
  simpa only [σ, restrictAdjunction_oplax_η, pullback_η] using h

/-- An actual pulled-back unit-source map becomes its literal restricted
map under the canonical restriction comparison. -/
@[reassoc]
theorem pullback_unit_map_restriction (j : X ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} (s : 𝟙_ Y.Modules ⟶ M) :
    (pullbackObjUnitIso j).inv ≫ (pullback j).map s ≫
        (restrictFunctorIsoPullback j).inv.app M =
      (restrictUnitIso j).inv ≫ (restrictFunctor j).map s := by
  rw [(restrictFunctorIsoPullback j).inv.naturality, ← Category.assoc]
  congr 1
  apply (cancel_mono (restrictUnitIso j).hom).mp
  rw [Category.assoc, restrictFunctorIsoPullback_inv_comp_unit,
    Iso.inv_hom_id, Iso.inv_hom_id]

/-- The actual restriction--pullback isomorphism carries the canonical
pullback tensor map to the literal tensor insertion for restriction. -/
@[reassoc]
theorem restrictFunctorIsoPullback_inv_tensor (j : X ⟶ Y) [IsOpenImmersion j]
    (M N : Y.Modules) :
    (restrictFunctorIsoPullback j).inv.app (M ⊗ N) =
      Functor.OplaxMonoidal.δ (pullback j) M N ≫
        ((restrictFunctorIsoPullback j).inv.app M ⊗ₘ
          (restrictFunctorIsoPullback j).inv.app N) ≫
        Functor.LaxMonoidal.μ (restrictFunctor j) M N := by
  letI := (restrictAdjunction j).leftAdjointOplaxMonoidal
  let σ := (restrictFunctorIsoPullback j).inv
  have hσ : conjugateEquiv (restrictAdjunction j) (pullbackPushforwardAdjunction j)
      σ = 𝟙 _ := by
    simp [σ, restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  have hδ := Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _ hσ M N
  rw [Adjunction.leftAdjointOplaxMonoidal_δ] at hδ
  have hinv := (restrictAdjunction j).inv_μ_eq_homEquiv_symm
    (restrictAdjunction_counit_app_tensor j) M N
  erw [← hinv] at hδ
  have h := congrArg (fun k => k ≫ Functor.LaxMonoidal.μ (restrictFunctor j) M N) hδ
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

/-- Pullback of the tensor of the two unit sections is the tensor of
their actual pullbacks. This is the oplax unit law with the prescribed
structure-sheaf comparison, for an arbitrary scheme morphism. -/
@[reassoc]
theorem pullback_unit_tensor (f : X ⟶ Y) :
    (pullback f).map (λ_ (𝟙_ Y.Modules)).inv ≫
        Functor.OplaxMonoidal.δ (pullback f)
          (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
        ((pullbackObjUnitIso f).hom ⊗ₘ (pullbackObjUnitIso f).hom) =
      (pullbackObjUnitIso f).hom ≫ (λ_ (𝟙_ X.Modules)).inv := by
  rw [← pullback_η, tensorHom_def,
    ← Functor.OplaxMonoidal.left_unitality_assoc]
  exact (leftUnitor_inv_naturality (Functor.OplaxMonoidal.η (pullback f))).symm

/-- The canonical tensor comparison carries a pulled-back tensor of
two unit-source maps to the tensor of their actual pullback frames. -/
@[reassoc]
theorem pullback_tensor_unit_maps (f : X ⟶ Y) {M N : Y.Modules}
    (first : 𝟙_ Y.Modules ⟶ M)
    (second : 𝟙_ Y.Modules ⟶ N) :
    (pullback f).map
        ((λ_ (𝟙_ Y.Modules)).inv ≫ (first ⊗ₘ second)) ≫
        Functor.OplaxMonoidal.δ (pullback f) M N =
      (pullbackObjUnitIso f).hom ≫
        (λ_ (𝟙_ X.Modules)).inv ≫
        (((pullbackObjUnitIso f).inv ≫ (pullback f).map first) ⊗ₘ
          ((pullbackObjUnitIso f).inv ≫ (pullback f).map second)) := by
  have unit := congrArg (fun k => k ≫
    ((pullbackObjUnitIso f).inv ⊗ₘ (pullbackObjUnitIso f).inv)) (pullback_unit_tensor f)
  simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id,
    id_tensorHom_id, Category.comp_id] at unit
  rw [Functor.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural,
    ← Category.assoc, unit]
  simp only [Category.assoc, tensorHom_comp_tensorHom]

/-- Equality transport of scheme morphisms preserves the actual tensor
comparison of their pullback functors. -/
@[reassoc]
theorem pullbackCongr_tensor {f g : X ⟶ Y} (h : f = g) (M N : Y.Modules) :
    (pullbackCongr h).hom.app (M ⊗ N) ≫ Functor.OplaxMonoidal.δ (pullback g) M N =
      Functor.OplaxMonoidal.δ (pullback f) M N ≫
        ((pullbackCongr h).hom.app M ⊗ₘ (pullbackCongr h).hom.app N) := by
  subst g
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules

namespace ToricPower

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The canonical comparison for a commutative square is compatible
with the canonical tensor maps of the two composite pullback functors. -/
@[reassoc]
theorem pullbackSquareIso_tensor (hsq : j ≫ f = g ≫ k) (M N : Y.Modules) :
    (pullbackSquareIso f g j k hsq).hom.app (M ⊗ N) ≫
        (Scheme.Modules.pullback j).map
          (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N) ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback j) _ _ =
      (Scheme.Modules.pullback g).map
          (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback k) M N) ≫
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) _ _ ≫
        ((pullbackSquareIso f g j k hsq).hom.app M ⊗ₘ
          (pullbackSquareIso f g j k hsq).hom.app N) := by
  apply (cancel_mono
    ((Scheme.Modules.pullbackComp j f).hom.app M ⊗ₘ
      (Scheme.Modules.pullbackComp j f).hom.app N)).mp
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app,
    Category.comp_id, id_tensorHom_id]
  rw [← Scheme.Modules.pullback_comp_δ,
    Scheme.Modules.pullbackCongr_tensor,
    TauCeti.AlgebraicGeometry.pullbackComp_hom_app_comp_δ_assoc]
  simp only [tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

end ToricPower

end

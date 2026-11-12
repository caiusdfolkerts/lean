module

public import ToricPower.TensorCompatibleTransformation
public import ToricPower.MonoidalProjectionComparison
public import ToricPower.OpenBaseChangeNaturality
public import ToricPower.SchemeRestrictionTensor

/-!
# Projection comparisons and actual open base change

The canonical projection morphism commutes with restriction to a Cartesian
open square.  The proof uses the genuine adjunction mate and the tensor
compatibility of the restriction units and counits.  Consequently the
affine projection formula can be checked on actual toric affine charts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace ToricPower

section Abstract

variable {C D C' D' : Type*}
  [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  [Category C'] [MonoidalCategory C'] [Category D'] [MonoidalCategory D']
  {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
  (adj : F ⊣ G) (adj' : F' ⊣ G')
  {K : C ⥤ C'} {J : D ⥤ D'}
  [G.LaxMonoidal] [G'.LaxMonoidal] [K.LaxMonoidal] [J.LaxMonoidal]
  (γ : K ⋙ F' ⟶ F ⋙ J)

/-- The projection comparison commutes with a tensor-compatible adjunction mate. -/
theorem monoidalProjectionComparison_mate
    [TensorCompatible (mateEquiv adj adj' γ)] (M : C) (N : D) :
    μ K M (G.obj N) ≫ K.map ((monoidalProjectionComparison adj N).app M) ≫
        (mateEquiv adj adj' γ).app (F.obj M ⊗ N) =
      (K.obj M ◁ (mateEquiv adj adj' γ).app N) ≫
        (monoidalProjectionComparison adj' (J.obj N)).app (K.obj M) ≫
        G'.map (γ.app M ▷ J.obj N) ≫ G'.map (μ J (F.obj M) N) := by
  let β := mateEquiv adj adj' γ
  have tensor := TensorCompatible.tensor (α := β) (F.obj M) N
  simp only [comp_μ, Functor.comp_obj, Category.assoc] at tensor
  dsimp only [monoidalProjectionComparison]
  simp only [Functor.comp_obj, K.map_comp, Category.assoc]
  rw [← μ_natural_left_assoc, tensor]
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, unit_mateEquiv,
    comp_whiskerRight_assoc, whisker_exchange_assoc]
  simp only [Functor.id_obj, Functor.comp_obj]
  have exchange :
      G'.map (γ.app M) ▷ K.obj (G.obj N) ≫
          G'.obj (J.obj (F.obj M)) ◁ β.app N =
        G'.obj (F'.obj (K.obj M)) ◁ β.app N ≫
          G'.map (γ.app M) ▷ G'.obj (J.obj N) := by
    simpa only [Functor.comp_obj] using
      (whisker_exchange (G'.map (γ.app M)) (β.app N)).symm
  rw [← Category.assoc (G'.map (γ.app M) ▷ K.obj (G.obj N)), exchange,
    Category.assoc]
  have natural :
      G'.map (γ.app M) ▷ G'.obj (J.obj N) ≫
          μ G' (J.obj (F.obj M)) (J.obj N) =
        μ G' (F'.obj (K.obj M)) (J.obj N) ≫ G'.map (γ.app M ▷ J.obj N) := by
    simpa only [Functor.comp_obj] using μ_natural_left G' (γ.app M) (J.obj N)
  rw [← Category.assoc (G'.map (γ.app M) ▷ G'.obj (J.obj N)), natural]
  simp only [Category.assoc]
  rfl

end Abstract

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

instance restrictionUnit_tensorCompatible :
    TensorCompatible (Scheme.Modules.restrictAdjunction j).unit where
  tensor M N := by
    simpa only [Functor.LaxMonoidal.id_μ, Category.id_comp,
      Functor.LaxMonoidal.comp_μ, Category.assoc] using
      Scheme.Modules.restrictAdjunction_unit_app_tensor j M N

instance restrictionCounit_tensorCompatible :
    TensorCompatible (Scheme.Modules.restrictAdjunction j).counit where
  tensor M N := by
    simpa only [Functor.LaxMonoidal.id_μ, Category.comp_id,
      Functor.LaxMonoidal.comp_μ, Category.assoc] using
      Scheme.Modules.restrictAdjunction_counit_app_tensor j M N

/-- Tensor compatibility of the actual direct-image square. -/
instance pushforwardSquareIso_isMonoidal (hsq : j ≫ f = g ≫ k) :
    NatTrans.IsMonoidal (pushforwardSquareIso f g j k hsq).hom := by
  dsimp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The actual open base-change mate preserves tensor products. -/
theorem pushforwardRestrictionMate_tensorCompatible (hsq : j ≫ f = g ≫ k) :
    TensorCompatible (mateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (pullbackRestrictionSquareIso f g j k hsq).hom) := by
  have equality : mateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (pullbackRestrictionSquareIso f g j k hsq).hom =
      (mateEquiv (Scheme.Modules.restrictAdjunction j)
        (Scheme.Modules.restrictAdjunction k)).symm
        (pushforwardSquareIso f g j k hsq).hom := by
    ext M
    rw [← pushforwardRestrictionMap_eq_pullback_mate,
      pushforwardRestrictionMap_eq_mate]
  rw [equality]
  exact TensorCompatible.inverseMate _ _ _

/-- Restriction of the genuine projection map is the genuine local
projection map, with the canonical pullback and direct-image comparisons. -/
theorem projectionComparison_openBaseChange (hsq : j ≫ f = g ≫ k)
    (M : Y.Modules) (N : X.Modules) :
    μ (Scheme.Modules.restrictFunctor k) M ((Scheme.Modules.pushforward f).obj N) ≫
        (Scheme.Modules.restrictFunctor k).map
          ((monoidalProjectionComparison
            (Scheme.Modules.pullbackPushforwardAdjunction f) N).app M) ≫
        pushforwardRestrictionMap f g j k hsq ((Scheme.Modules.pullback f).obj M ⊗ N) =
      ((Scheme.Modules.restrictFunctor k).obj M ◁
        pushforwardRestrictionMap f g j k hsq N) ≫
        (monoidalProjectionComparison
          (Scheme.Modules.pullbackPushforwardAdjunction g)
          ((Scheme.Modules.restrictFunctor j).obj N)).app
          ((Scheme.Modules.restrictFunctor k).obj M) ≫
        (Scheme.Modules.pushforward g).map
          ((pullbackRestrictionSquareIso f g j k hsq).hom.app M ▷
            (Scheme.Modules.restrictFunctor j).obj N) ≫
        (Scheme.Modules.pushforward g).map
          (μ (Scheme.Modules.restrictFunctor j) ((Scheme.Modules.pullback f).obj M) N) := by
  letI := pushforwardRestrictionMate_tensorCompatible f g j k hsq
  simp only [pushforwardRestrictionMap_eq_pullback_mate]
  exact monoidalProjectionComparison_mate _ _ _ M N

/-- Invertibility of the genuine projection comparison can be verified
after an actual Cartesian open restriction. -/
theorem projectionComparison_restrict_isIso
    (hsq : j ≫ f = g ≫ k) (hpre : f ⁻¹ᵁ k.opensRange ≤ j.opensRange)
    (M : Y.Modules) (N : X.Modules)
    (localIso : IsIso ((monoidalProjectionComparison
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      ((Scheme.Modules.restrictFunctor j).obj N)).app
      ((Scheme.Modules.restrictFunctor k).obj M))) :
    IsIso ((Scheme.Modules.restrictFunctor k).map
      ((monoidalProjectionComparison
        (Scheme.Modules.pullbackPushforwardAdjunction f) N).app M)) := by
  letI := localIso
  letI (P : X.Modules) : IsIso (pushforwardRestrictionMap f g j k hsq P) :=
    (pushforwardRestrictionIso f g j k hsq hpre P).isIso_hom
  have comparison : IsIso
      (μ (Scheme.Modules.restrictFunctor k) M ((Scheme.Modules.pushforward f).obj N) ≫
        (Scheme.Modules.restrictFunctor k).map
          ((monoidalProjectionComparison
            (Scheme.Modules.pullbackPushforwardAdjunction f) N).app M) ≫
        pushforwardRestrictionMap f g j k hsq ((Scheme.Modules.pullback f).obj M ⊗ N)) := by
    rw [projectionComparison_openBaseChange]
    infer_instance
  have remaining := (isIso_comp_left_iff
    (μ (Scheme.Modules.restrictFunctor k) M ((Scheme.Modules.pushforward f).obj N)) _).mp
    comparison
  exact (isIso_comp_right_iff _
    (pushforwardRestrictionMap f g j k hsq ((Scheme.Modules.pullback f).obj M ⊗ N))).mp
    remaining

end ToricPower

end

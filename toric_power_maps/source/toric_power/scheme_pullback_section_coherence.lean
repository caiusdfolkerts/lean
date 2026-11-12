module

public import ToricPower.SchemePullbackTensorCoherence
public import ToricPower.SheafRestrictionPullbackCoherence

/-!
# Canonical pullback coherence for a section and its chart squares

These identities retain the specified unit, composition, and ordinary
restriction maps of actual scheme-module pullback. They can be applied
independently of toric geometry or a chosen Cartier frame.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y Z W T : Scheme.{u}}

/-- A chosen section of a morphism identifies the pullback of its first
factor with the original module by the canonical composition and identity
maps. -/
def sectionPullbackIso (d : X ⟶ Y) (p : Y ⟶ X) (hd : d ≫ p = 𝟙 X) :
    pullback p ⋙ pullback d ≅ 𝟭 X.Modules :=
  pullbackComp d p ≪≫ pullbackCongr hd ≪≫ pullbackId X

/-- The composition map of actual pullbacks sends the two normalized
unit maps to the normalized unit map of the composite. -/
@[reassoc]
theorem pullback_unit_inv_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackObjUnitIso f).inv ≫ (pullback f).map (pullbackObjUnitIso g).inv ≫
      (pullbackComp f g).hom.app ((𝟙_ Z.Modules)) =
      (pullbackObjUnitIso (f ≫ g)).inv := by
  apply (cancel_mono (pullbackObjUnitIso (f ≫ g)).hom).mp
  simp only [Iso.inv_hom_id]
  rw [← pullbackObjUnitIso_comp f g]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp, Iso.inv_hom_id]
  erw [(pullback f).map_id]
  simp only [Category.id_comp]
  exact (pullbackObjUnitIso f).inv_hom_id

/-- Normalized pullback of a unit-source morphism is compatible with
composition, including the specified structure-sheaf frame. -/
@[reassoc]
theorem pullback_unit_map_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : (𝟙_ Z.Modules) ⟶ M) :
    (pullbackObjUnitIso f).inv ≫
        (pullback f).map ((pullbackObjUnitIso g).inv ≫ (pullback g).map a) ≫
        (pullbackComp f g).hom.app M =
      (pullbackObjUnitIso (f ≫ g)).inv ≫ (pullback (f ≫ g)).map a := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(pullbackComp f g).hom.naturality a]
  exact pullback_unit_inv_comp_assoc f g _

/-- Replacing the morphism by an equal one does not alter the normalized
pullback of a unit-source morphism. -/
@[reassoc]
theorem pullback_unit_map_congr {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (a : (𝟙_ Y.Modules) ⟶ M) :
    (pullbackObjUnitIso f).inv ≫ (pullback f).map a ≫
        (pullbackCongr h).hom.app M =
      (pullbackObjUnitIso g).inv ≫ (pullback g).map a := by
  subst g
  simp [pullbackCongr]

/-- Associativity with the final equality transport on the other side,
so that it rewrites a composition without requiring a particular suffix. -/
@[reassoc]
theorem pullbackComp_assoc_hom (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : W.Modules) :
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M =
      (pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by simp) := by
  have associativity :=
    pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app f g h M
  have reversed := congrArg (fun a => a ≫ eqToHom
    (show (pullback (f ≫ (g ≫ h))).obj M =
      (pullback ((f ≫ g) ≫ h)).obj M by simp)) associativity.symm
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using reversed

/-- Pasting the actual diagonal square with a projection square gives
the direct composition comparison. This is the associativity and unit
coherence of the actual scheme-module pullback pseudofunctor. -/
@[reassoc]
theorem pullback_section_square_factor
    (d : X ⟶ Y) (p : Y ⟶ X) (j : W ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (l : Z ⟶ T)
    (hd : d ≫ p = 𝟙 X) (hsq : j ≫ d = g ≫ k)
    (hk : k ≫ p = l ≫ e)
    (hj : (g ≫ l) ≫ e = j) (M : X.Modules) :
    (pullback g).map
        ((pullbackComp l e).hom.app M ≫
          (pullbackCongr hk).inv.app M ≫ (pullbackComp k p).inv.app M) ≫
      (ToricPower.pullbackSquareIso d g j k hsq).hom.app ((pullback p).obj M) ≫
      (pullback j).map ((sectionPullbackIso d p hd).hom.app M) =
    (pullbackComp g l).hom.app ((pullback e).obj M) ≫
      (pullbackComp (g ≫ l) e).hom.app M ≫ (pullbackCongr hj).hom.app M := by
  dsimp only [ToricPower.pullbackSquareIso, sectionPullbackIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    pseudofunctor_left_unitality_app]
  simp only [Category.assoc, eqToHom_trans]
  rw [pullbackComp_assoc_hom_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  have congruence := pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app
    g hk.symm M
  have pasted := congrArg (fun a =>
    (pullbackComp g (l ≫ e)).hom.app M ≫ a ≫
      (pullbackComp g (k ≫ p)).hom.app M) congruence
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id] at pasted
  rw [show (pullbackCongr hk).inv = (pullbackCongr hk.symm).hom by
    simp only [pullbackCongr, eqToIso.inv, eqToIso.hom]]
  simp only [Functor.map_comp, Category.assoc, Category.comp_id]
  rw [reassoc_of% pasted,
    pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc]
  simp only [pullbackCongr, eqToIso.hom, eqToHom_app,
    Category.assoc, eqToHom_trans]

/-- The open-restriction composition map is the actual conjugate of the
ordinary direct-image composition map. Its proof is a computation of the
specified restriction unit and counit on each open. -/
theorem restrictFunctorComp_conjugate (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  exact ToricPower.conjugateEquiv_restrictFunctorComp_hom f g

/-- Composition of the canonical restriction--pullback comparison agrees
with the literal sectionwise restriction comparison. -/
@[reassoc]
theorem pullback_restriction_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (pullback f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (pullbackComp f g).hom.app M ≫
        (restrictFunctorIsoPullback (f ≫ g)).inv.app M =
      (restrictFunctorIsoPullback f).inv.app ((restrictFunctor g).obj M) ≫
        (restrictFunctorComp f g).inv.app M := by
  apply (cancel_mono ((restrictFunctorIsoPullback (f ≫ g)).hom.app M)).mp
  apply (cancel_epi ((restrictFunctorIsoPullback f).hom.app
    ((restrictFunctor g).obj M))).mp
  apply (cancel_epi ((restrictFunctorComp f g).hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc,
    Category.comp_id, Category.id_comp]
  have naturality :
      (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app ((pullback g).obj M) =
      (restrictFunctorIsoPullback f).hom.app ((restrictFunctor g).obj M) ≫
        (pullback f).map ((restrictFunctorIsoPullback g).hom.app M) :=
    (restrictFunctorIsoPullback f).hom.naturality ((restrictFunctorIsoPullback g).hom.app M)
  have precomposed := congrArg (fun a => (restrictFunctorComp f g).hom.app M ≫
    a ≫ (pullbackComp f g).hom.app M) naturality.symm
  exact precomposed.trans (ToricPower.restrictFunctorComp_toPullback_app f g M)

/-- The same normalization after replacement of the composite by an
equal actual open immersion. -/
@[reassoc]
theorem pullback_restriction_comp_congr (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    (hh : f ≫ g = h) (M : Z.Modules) :
    (pullback f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
        (pullbackComp f g).hom.app M ≫ (pullbackCongr hh).hom.app M ≫
        (restrictFunctorIsoPullback h).inv.app M =
      (restrictFunctorIsoPullback f).inv.app ((restrictFunctor g).obj M) ≫
        (restrictFunctorComp f g).inv.app M ≫
        (restrictFunctorCongr hh).hom.app M := by
  subst h
  have identity : (restrictFunctorCongr (rfl : f ≫ g = f ≫ g)).hom.app M = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
      M.presheaf.map_id, Hom.id_app]
    rfl
  simpa only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, identity, Category.comp_id] using pullback_restriction_comp f g M

/-- The normalized frame transported around the two squares is the
normalized pullback along the composite, before comparing with ordinary
restriction. -/
@[reassoc]
theorem section_square_frame_pullback
    (d : X ⟶ Y) (p : Y ⟶ X) (j : W ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (l : Z ⟶ T)
    (hd : d ≫ p = 𝟙 X) (hsq : j ≫ d = g ≫ k)
    (hk : k ≫ p = l ≫ e) (hj : (g ≫ l) ≫ e = j)
    (M : X.Modules)
    (a : (𝟙_ T.Modules) ⟶ (pullback e).obj M) :
    (pullbackObjUnitIso g).inv ≫
        (pullback g).map
          ((pullbackObjUnitIso l).inv ≫ (pullback l).map a ≫
            (pullbackComp l e).hom.app M ≫ (pullbackCongr hk).inv.app M ≫
            (pullbackComp k p).inv.app M) ≫
        (ToricPower.pullbackSquareIso d g j k hsq).hom.app ((pullback p).obj M) ≫
        (pullback j).map ((sectionPullbackIso d p hd).hom.app M) =
      (pullbackObjUnitIso (g ≫ l)).inv ≫ (pullback (g ≫ l)).map a ≫
        (pullbackComp (g ≫ l) e).hom.app M ≫ (pullbackCongr hj).hom.app M := by
  have pasted := pullback_section_square_factor d p j k g e l hd hsq hk hj M
  calc
    _ = (pullbackObjUnitIso g).inv ≫
        (pullback g).map (pullbackObjUnitIso l).inv ≫
        (pullback g).map ((pullback l).map a) ≫
        ((pullback g).map
          ((pullbackComp l e).hom.app M ≫ (pullbackCongr hk).inv.app M ≫
            (pullbackComp k p).inv.app M) ≫
          (ToricPower.pullbackSquareIso d g j k hsq).hom.app ((pullback p).obj M) ≫
          (pullback j).map ((sectionPullbackIso d p hd).hom.app M)) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (pullbackObjUnitIso g).inv ≫
        (pullback g).map (pullbackObjUnitIso l).inv ≫
        (pullback g).map ((pullback l).map a) ≫
        (pullbackComp g l).hom.app ((pullback e).obj M) ≫
        (pullbackComp (g ≫ l) e).hom.app M ≫ (pullbackCongr hj).hom.app M := by
      rw [pasted]
    _ = _ := by
      erw [(pullbackComp g l).hom.naturality_assoc a]
      simpa only [Category.assoc] using
        congrArg (fun v => v ≫ (pullback (g ≫ l)).map a ≫
          (pullbackComp (g ≫ l) e).hom.app M ≫ (pullbackCongr hj).hom.app M)
          (pullback_unit_inv_comp g l)

/-- The complete factor-frame path through a section square is literal
restriction along the composite. Both unit normalizations and both
pullback composition comparisons occur in the statement. -/
@[reassoc]
theorem section_square_frame_restriction
    (d : X ⟶ Y) (p : Y ⟶ X) (j : W ⟶ X) (k : Z ⟶ Y)
    (g : W ⟶ Z) (e : T ⟶ X) (l : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion e] [IsOpenImmersion (g ≫ l)]
    (hd : d ≫ p = 𝟙 X) (hsq : j ≫ d = g ≫ k)
    (hk : k ≫ p = l ≫ e) (hj : (g ≫ l) ≫ e = j)
    (M : X.Modules)
    (frame : (𝟙_ T.Modules) ⟶ (restrictFunctor e).obj M) :
    (pullbackObjUnitIso g).inv ≫
        (pullback g).map
          ((pullbackObjUnitIso l).inv ≫
            (pullback l).map (frame ≫ (restrictFunctorIsoPullback e).hom.app M) ≫
            (pullbackComp l e).hom.app M ≫ (pullbackCongr hk).inv.app M ≫
            (pullbackComp k p).inv.app M) ≫
        (ToricPower.pullbackSquareIso d g j k hsq).hom.app ((pullback p).obj M) ≫
        (pullback j).map ((sectionPullbackIso d p hd).hom.app M) ≫
        (restrictFunctorIsoPullback j).inv.app M =
      (restrictUnitIso (g ≫ l)).inv ≫ (restrictFunctor (g ≫ l)).map frame ≫
        (restrictFunctorComp (g ≫ l) e).inv.app M ≫
        (restrictFunctorCongr hj).hom.app M := by
  rw [section_square_frame_pullback_assoc d p j k g e l hd hsq hk hj,
    Functor.map_comp, Category.assoc, pullback_restriction_comp_congr]
  exact pullback_unit_map_restriction_assoc (g ≫ l) frame _

/-- Evaluation of the literal restriction path for a frame over an
actual open. The only transport is the equality of the image opens. -/
theorem restriction_composite_frame_one
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    (hh : f ≫ g = h) (M : Z.Modules)
    (frame : ((𝟙_ Z.Modules)).over g.opensRange ≅
      M.over g.opensRange) (U : X.Opens) :
    Hom.app
        ((restrictUnitIso f).inv ≫
          (restrictFunctor f).map (ToricPower.cartierOverToAffineFrame g M frame).hom ≫
          (restrictFunctorComp f g).inv.app M ≫
          (restrictFunctorCongr hh).hom.app M) U (1 : Γ(X, U)) =
      frame.hom.val.app
        (op (Over.mk (homOfLE (show h ''ᵁ U ≤ g.opensRange by
          simpa [← hh, Scheme.Hom.comp_image] using
            g.image_le_opensRange (f ''ᵁ U))))) (1 : Γ(Z, h ''ᵁ U)) := by
  simp only [ToricPower.schemeHom_comp_apply, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, ToricPower.restrictFunctor_map_app,
    ToricPower.restrictUnitIso_inv_sections, map_one]
  erw [ToricPower.cartierOverToAffineFrame_image_sections g M frame
    (f ''ᵁ U) (1 : Γ(Y, f ''ᵁ U)), map_one]
  have image₁ : (f ≫ g) ''ᵁ U = g ''ᵁ (f ''ᵁ U) := Scheme.Hom.comp_image f g U
  have image₂ : h ''ᵁ U = (f ≫ g) ''ᵁ U := by simp only [hh]
  let source : Over g.opensRange :=
    Over.mk (homOfLE (g.image_le_opensRange (f ''ᵁ U)))
  let target : Over g.opensRange :=
    Over.mk (homOfLE (show h ''ᵁ U ≤ g.opensRange by
      simpa [← hh, Scheme.Hom.comp_image] using
        g.image_le_opensRange (f ''ᵁ U)))
  change M.presheaf.map (eqToHom image₂).op
    (M.presheaf.map (eqToHom image₁).op
      (frame.hom.val.app (op source) (1 : Γ(Z, g ''ᵁ (f ''ᵁ U))))) =
    frame.hom.val.app (op target) (1 : Γ(Z, h ''ᵁ U))
  let comparison : target ⟶ source := Over.homMk (eqToHom (image₂.trans image₁))
  have naturality := ConcreteCategory.congr_hom
    (frame.hom.val.naturality comparison.op) (1 : Γ(Z, g ''ᵁ (f ''ᵁ U)))
  change frame.hom.val.app (op target)
      (Z.presheaf.map (eqToHom (image₂.trans image₁)).op 1) =
    M.presheaf.map (eqToHom (image₂.trans image₁)).op
      (frame.hom.val.app (op source) (1 : Γ(Z, g ''ᵁ (f ''ᵁ U)))) at naturality
  rw [map_one] at naturality
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans] using naturality.symm

end AlgebraicGeometry.Scheme.Modules

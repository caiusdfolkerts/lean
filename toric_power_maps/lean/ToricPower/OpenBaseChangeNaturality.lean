module

public import ToricPower.PowerSheafCore
public import ToricPower.CoherentFoundations

/-!
# Adjunction compatibility of ordinary open base change

The ordinary open restriction map is computed as the genuine mate of
the commutative square of direct images. Its mate under the other two
adjunctions is exactly the canonical comparison of the actual pullback
functors. Consequently restriction of an adjunct equals the adjunct of
the restricted map. All identities involve the actual scheme-module
functors, units, counits, and composition isomorphisms.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

section AbstractMate

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}

/-- The mate of a square transports actual adjuncts to actual adjuncts. -/
theorem mate_homEquiv (α : G ⋙ L₂ ⟶ L₁ ⋙ H) {M : C} {N : D}
    (φ : L₁.obj M ⟶ N) :
    G.map (adj₁.homEquiv M N φ) ≫ (mateEquiv adj₁ adj₂ α).app N =
      adj₂.homEquiv (G.obj M) (H.obj N) (α.app M ≫ H.map φ) := by
  let γ := mateEquiv adj₁ adj₂ α
  change G.map (adj₁.unit.app M ≫ R₁.map φ) ≫ γ.app N =
    adj₂.unit.app (G.obj M) ≫ R₂.map (α.app M ≫ H.map φ)
  have natural := γ.naturality φ
  change G.map (R₁.map φ) ≫ γ.app N = γ.app (L₁.obj M) ≫ R₂.map (H.map φ) at natural
  rw [G.map_comp, Category.assoc, natural]
  rw [← Category.assoc,unit_mateEquiv,Category.assoc,R₂.map_comp]
  rfl

end AbstractMate

universe u

variable {X X' Y Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The literal pullback comparison associated to a commutative square. -/
def pullbackSquareIso (hsq : j ≫ f = g ≫ k) :
    Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback j :=
  Scheme.Modules.pullbackComp g k ≪≫ Scheme.Modules.pullbackCongr hsq.symm ≪≫
    (Scheme.Modules.pullbackComp j f).symm

theorem conjugate_pullbackComp_hom {Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ b))
      ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))
      (Scheme.Modules.pullbackComp a b).hom =
      (Scheme.Modules.pushforwardComp a b).inv := by
  apply (cancel_epi (Scheme.Modules.pushforwardComp a b).hom).mp
  rw [Iso.hom_inv_id, ← Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id]

theorem conjugate_pullbackCongr {a b : X ⟶ Y} (h : a = b) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
      (Scheme.Modules.pullbackPushforwardAdjunction b)
      (Scheme.Modules.pullbackCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst b
  rw [Scheme.Modules.pullbackCongr]
  simp only [eqToIso_refl,Iso.refl_hom,conjugateEquiv_id]
  ext M U x
  simp only [NatTrans.id_app,Scheme.Modules.pushforwardCongr_hom_app_app,
    eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    Scheme.Modules.Hom.id_app, CategoryTheory.ConcreteCategory.id_apply]
  rfl

/-- The canonical actual pullback square is conjugate to the canonical
actual direct-image square. -/
theorem pullbackSquareIso_conjugate (hsq : j ≫ f = g ≫ k) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction j))
      ((Scheme.Modules.pullbackPushforwardAdjunction k).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g))
      (pullbackSquareIso f g j k hsq).hom =
      (pushforwardSquareIso f g j k hsq).hom := by
  unfold pullbackSquareIso pushforwardSquareIso
  simp only [Iso.trans_hom,Iso.symm_hom]
  rw [← conjugateEquiv_comp _
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ k)) _]
  rw [← conjugateEquiv_comp _
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ f)) _]
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugate_pullbackCongr,conjugate_pullbackComp_hom]
  simp only [Category.assoc]
  exact hsq

/-- The same canonical comparison with actual open restriction on the
horizontal edges. -/
def pullbackRestrictionSquareIso (hsq : j ≫ f = g ≫ k) :
    Scheme.Modules.restrictFunctor k ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback k)
      (Scheme.Modules.pullback g) ≪≫
    pullbackSquareIso f g j k hsq ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback j).symm

/-- Replacing pullback by its actual open-restriction adjoint does not
alter the canonical direct-image mate. -/
theorem pullbackRestrictionSquareIso_conjugate (hsq : j ≫ f = g ≫ k) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction j))
      ((Scheme.Modules.restrictAdjunction k).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g))
      (pullbackRestrictionSquareIso f g j k hsq).hom =
      (pushforwardSquareIso f g j k hsq).hom := by
  unfold pullbackRestrictionSquareIso
  simp only [Iso.trans_hom,Functor.isoWhiskerRight_hom,Functor.isoWhiskerLeft_hom,
    Iso.symm_hom]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction k).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction j)) _]
  rw [conjugateEquiv_whiskerLeft,conjugateEquiv_whiskerRight,
    pullbackSquareIso_conjugate]
  simp [Scheme.Modules.restrictFunctorIsoPullback,Adjunction.leftAdjointUniq]

/-- The previously constructed sectionwise open base-change map is
literally the corresponding partial mate. -/
theorem pushforwardRestrictionMap_eq_mate (hsq : j ≫ f = g ≫ k) (M : X.Modules) :
    pushforwardRestrictionMap f g j k hsq M =
      ((mateEquiv (Scheme.Modules.restrictAdjunction j)
        (Scheme.Modules.restrictAdjunction k)).symm
        (pushforwardSquareIso f g j k hsq).hom).app M := by
  simp only [pushforwardRestrictionMap,mateEquiv,Equiv.coe_fn_symm_mk,
    NatTrans.comp_app,Functor.leftUnitor_inv_app,Functor.rightUnitor_hom_app,
    Functor.whiskerLeft_app,Functor.whiskerRight_app,Functor.associator_hom_app,
    Functor.associator_inv_app,Functor.comp_map,Functor.map_id,
    Category.id_comp,Category.comp_id,Category.assoc]
  rfl

/-- The open base-change map is the mate of the canonical actual
pullback comparison, not a separately chosen abstract isomorphism. -/
theorem pushforwardRestrictionMap_eq_pullback_mate
    (hsq : j ≫ f = g ≫ k) (M : X.Modules) :
    pushforwardRestrictionMap f g j k hsq M =
      (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (pullbackRestrictionSquareIso f g j k hsq).hom).app M := by
  rw [pushforwardRestrictionMap_eq_mate]
  congr 1
  apply (mateEquiv (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.restrictAdjunction k)).injective
  rw [Equiv.apply_symm_apply,iterated_mateEquiv_conjugateEquiv,
    pullbackRestrictionSquareIso_conjugate]

/-- The concrete base-change comparison carries a global adjunct to the
adjunct of its canonically restricted map. -/
@[reassoc]
theorem pushforwardRestrictionMap_homEquiv (hsq : j ≫ f = g ≫ k)
    {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.restrictFunctor k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N φ) ≫
        pushforwardRestrictionMap f g j k hsq N =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackRestrictionSquareIso f g j k hsq).hom.app M ≫
          (Scheme.Modules.restrictFunctor j).map φ) := by
  rw [pushforwardRestrictionMap_eq_pullback_mate]
  exact mate_homEquiv _ _ _ φ

/-- The restriction comparison is the canonical pullback square, with
only the explicit open-restriction identifications on its two sides. -/
theorem pullbackRestrictionSquareIso_cancel (hsq : j ≫ f = g ≫ k)
    (M : Y.Modules) :
    (Scheme.Modules.pullback g).map
        ((Scheme.Modules.restrictFunctorIsoPullback k).inv.app M) ≫
        (pullbackRestrictionSquareIso f g j k hsq).hom.app M =
      (pullbackSquareIso f g j k hsq).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((Scheme.Modules.pullback f).obj M) := by
  simp only [pullbackRestrictionSquareIso,Iso.trans_hom,NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,Functor.isoWhiskerLeft_hom,Iso.symm_hom,
    Functor.whiskerRight_app,Functor.whiskerLeft_app,Category.assoc,
    ← Functor.map_comp,Iso.inv_hom_id_app,Functor.map_id,Category.id_comp]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The same adjunct compatibility, now starting with the literal
pullback functor on the lower open chart. -/
@[reassoc]
theorem pullback_pushforwardRestrictionMap_homEquiv (hsq : j ≫ f = g ≫ k)
    {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N φ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pushforward f).obj N) ≫
        pushforwardRestrictionMap f g j k hsq N =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso f g j k hsq).hom.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
            ((Scheme.Modules.pullback f).obj M) ≫
          (Scheme.Modules.restrictFunctor j).map φ) := by
  rw [← Category.assoc,(Scheme.Modules.restrictFunctorIsoPullback k).inv.naturality,
    Category.assoc,pushforwardRestrictionMap_homEquiv,
    ← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc,pullbackRestrictionSquareIso_cancel]
  simp only [Category.assoc]

/-- The actual base-change isomorphism for the direct image of the unit
sheaf carries a global adjunct to the precisely specified local adjunct. -/
@[reassoc]
theorem pullback_pushforwardRestrictionIso_unit_homEquiv
    (hsq : j ≫ f = g ≫ k) (hpre : f ⁻¹ᵁ k.opensRange ≤ j.opensRange)
    {M : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback k).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ φ) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
        (pushforwardRestrictionIso f g j k hsq hpre
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.restrictUnitIso j).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso f g j k hsq).hom.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
            ((Scheme.Modules.pullback f).obj M) ≫
          (Scheme.Modules.restrictFunctor j).map φ ≫
          (Scheme.Modules.restrictUnitIso j).hom) := by
  change (Scheme.Modules.pullback k).map _ ≫
    (Scheme.Modules.restrictFunctorIsoPullback k).inv.app _ ≫
    pushforwardRestrictionMap f g j k hsq _ ≫ _ = _
  have square := pullback_pushforwardRestrictionMap_homEquiv f g j k hsq φ
  have post := congrArg (fun h => h ≫
    (Scheme.Modules.pushforward g).map (Scheme.Modules.restrictUnitIso j).hom) square
  have natural := Adjunction.homEquiv_naturality_right
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    ((pullbackSquareIso f g j k hsq).hom.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
        ((Scheme.Modules.pullback f).obj M) ≫ (Scheme.Modules.restrictFunctor j).map φ)
    (Scheme.Modules.restrictUnitIso j).hom
  simpa only [Category.assoc] using post.trans natural.symm

end ToricPower

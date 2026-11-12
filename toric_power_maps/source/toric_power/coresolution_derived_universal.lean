module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Absolute right derivation from a concrete coresolution

A functorial coaugmentation into a coresolution gives a right derived
functor when localization inverts the coaugmentation and the resolved
functor factors through localization. The two iterated coaugmentations
must agree after applying the target functor. This file proves the full
universal property, including uniqueness and arbitrary postcomposition.

The result is a categorical construction. A geometric application must
still construct the coresolution and prove each displayed hypothesis.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

universe u v u' v' w z w' z'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  {E : Type w} [Category.{z} E]
  {E' : Type w'} [Category.{z'} E']
  (R : C ⥤ C) (η : 𝟭 C ⟶ R)

/-- The coaugmentation becomes an actual natural isomorphism under a
functor which inverts every component. -/
def coresolutionCompIso (L : C ⥤ D)
    (hη : ∀ X : C, IsIso (L.map (η.app X))) : L ≅ R ⋙ L :=
  NatIso.ofComponents (fun X => by
    letI := hη X
    exact asIso (L.map (η.app X))) (fun f => by
      dsimp
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map (η.naturality f))

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (hη : ∀ X : C, IsIso (L.map (η.app X)))
  (F : C ⥤ E) (RF : D ⥤ E) (e : L ⋙ RF ≅ R ⋙ F)

/-- The actual comparison from the original functor to the resolved one. -/
def coresolutionDerivedUnit : F ⟶ L ⋙ RF :=
  F.leftUnitor.inv ≫ whiskerRight η F ≫ e.inv

@[simp]
theorem coresolutionDerivedUnit_app (X : C) :
    (coresolutionDerivedUnit R η L F RF e).app X =
      F.map (η.app X) ≫ e.inv.app X := by
  simp only [coresolutionDerivedUnit, NatTrans.comp_app, whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp]

variable {F RF}

/-- The universal descent map before restriction along localization is
inverted by its fully faithful functor. -/
def coresolutionDerivedDescPre (G : D ⥤ E) (β : F ⟶ L ⋙ G) :
    L ⋙ RF ⟶ L ⋙ G :=
  e.hom ≫ whiskerLeft R β ≫
    (coresolutionCompIso R η (L ⋙ G) (fun X => by
      letI := hη X
      exact inferInstanceAs (IsIso (G.map (L.map (η.app X)))))).inv

/-- Full faithfulness of restriction produces the actual descent map. -/
def coresolutionDerivedDesc (G : D ⥤ E) (β : F ⟶ L ⋙ G) : RF ⟶ G :=
  (Localization.whiskeringLeftFunctor' L W E).preimage
    (coresolutionDerivedDescPre R η L hη e G β)

@[simp]
theorem coresolutionDerivedDesc_app (G : D ⥤ E) (β : F ⟶ L ⋙ G) (X : C) :
    letI := hη X
    (coresolutionDerivedDesc R η L W hη e G β).app (L.obj X) =
      e.hom.app X ≫ β.app (R.obj X) ≫ inv (G.map (L.map (η.app X))) := by
  letI := hη X
  exact congr_app (Functor.map_preimage
    (Localization.whiskeringLeftFunctor' L W E)
    (coresolutionDerivedDescPre R η L hη e G β)) X

/-- The concrete descent map satisfies the required factorization. -/
theorem coresolutionDerivedDesc_fac (G : D ⥤ E) (β : F ⟶ L ⋙ G) :
    coresolutionDerivedUnit R η L F RF e ≫
      whiskerLeft L (coresolutionDerivedDesc R η L W hη e G β) = β := by
  apply NatTrans.ext
  funext X
  letI := hη X
  simp only [NatTrans.comp_app, whiskerLeft_app, coresolutionDerivedUnit_app,
    coresolutionDerivedDesc_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := β.naturality (η.app X)
  dsimp only [Functor.comp_map] at hn
  have h := congrArg (fun f => f ≫ inv (G.map (L.map (η.app X)))) hn
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
  exact h

variable (hcoh : ∀ X : C,
  F.map (R.map (η.app X)) = F.map (η.app (R.obj X)))

include hη hcoh

/-- Coherence of the iterated coaugmentations proves uniqueness; it is
not an assumed Kan-extension property. -/
theorem coresolutionDerivedDesc_unique (G : D ⥤ E) (β : F ⟶ L ⋙ G)
    (γ : RF ⟶ G)
    (hγ : ∀ X : C, F.map (η.app X) ≫ e.inv.app X ≫ γ.app (L.obj X) = β.app X) :
    γ = coresolutionDerivedDesc R η L W hη e G β := by
  apply Localization.natTrans_ext L W
  intro X
  letI := hη X
  apply (cancel_epi (e.inv.app X)).1
  rw [coresolutionDerivedDesc_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply (cancel_mono (G.map (L.map (η.app X)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let δ : R ⋙ F ⟶ L ⋙ G := e.inv ≫ whiskerLeft L γ
  have hn := δ.naturality (η.app X)
  dsimp only [δ, NatTrans.comp_app, whiskerLeft_app, Functor.comp_map] at hn
  rw [hcoh X] at hn
  simp only [Category.assoc, hγ (R.obj X)] at hn
  exact hn.symm

/-- The actual factorization is a right derived functor. -/
theorem coresolution_isRightDerivedFunctor :
    RF.IsRightDerivedFunctor (coresolutionDerivedUnit R η L F RF e) W := by
  apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ W).2
  refine ⟨⟨IsInitial.ofUniqueHom (fun G =>
    StructuredArrow.homMk
      (coresolutionDerivedDesc R η L W hη e G.right G.hom)
      (coresolutionDerivedDesc_fac R η L W hη e G.right G.hom)) ?_⟩⟩
  intro G γ
  apply StructuredArrow.hom_ext
  apply coresolutionDerivedDesc_unique R η L W hη e hcoh G.right G.hom γ.right
  intro X
  have h := congr_app γ.w X
  simp only [Functor.LeftExtension.mk, StructuredArrow.mk_right,
    NatTrans.comp_app, whiskerLeft_app, Category.id_comp, Category.assoc] at h
  change (coresolutionDerivedUnit R η L F RF e).app X ≫
    γ.right.app (L.obj X) = G.hom.app X at h
  rw [coresolutionDerivedUnit_app] at h
  simpa only [Category.assoc] using h

/-- Arbitrary postcomposition preserves this right-derived universal
property, giving the absolute comparison needed for a derived adjunction. -/
theorem coresolution_isAbsoluteRightDerivedFunctor (T : E ⥤ E') :
    (RF ⋙ T).IsRightDerivedFunctor
      (whiskerRight (coresolutionDerivedUnit R η L F RF e) T ≫
        (Functor.associator L RF T).hom) W := by
  let eT : L ⋙ (RF ⋙ T) ≅ R ⋙ (F ⋙ T) :=
    (Functor.associator L RF T).symm ≪≫ isoWhiskerRight e T ≪≫
      Functor.associator R F T
  have hT := coresolution_isRightDerivedFunctor R η L W hη eT
    (fun X => congrArg T.map (hcoh X))
  have he : coresolutionDerivedUnit R η L (F ⋙ T) (RF ⋙ T) eT =
      whiskerRight (coresolutionDerivedUnit R η L F RF e) T ≫
        (Functor.associator L RF T).hom := by
    apply NatTrans.ext
    funext X
    simp only [coresolutionDerivedUnit_app, eT, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      isoWhiskerRight_inv, whiskerRight_app, Functor.comp_map,
      Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp]
  rwa [he] at hT

include e

omit hη hcoh in
/-- A factorization through localization identifies resolved images of
maps which have become equal there. This is a consequence of the actual
factorization isomorphism and its naturality. -/
theorem coresolution_resolved_map_eq {X Y : C} (f g : X ⟶ Y)
    (hfg : L.map f = L.map g) : F.map (R.map f) = F.map (R.map g) := by
  apply (cancel_epi (e.hom.app X)).1
  change e.hom.app X ≫ (R ⋙ F).map f = e.hom.app X ≫ (R ⋙ F).map g
  rw [← e.hom.naturality f, ← e.hom.naturality g]
  change RF.map (L.map f) ≫ e.hom.app Y = RF.map (L.map g) ≫ e.hom.app Y
  rw [hfg]

omit hcoh in
/-- It suffices that the target functor invert coaugmentation on
resolved objects. Naturality and the localization factorization then
prove the iterated-coaugmentation coherence, rather than assuming it.

For a finite Čech construction this hypothesis can be checked by an
actual contraction on its open-extension terms. -/
theorem coresolution_coherence_of_resolved_isIso
    (hresolved : ∀ X : C, IsIso (F.map (η.app (R.obj X)))) (X : C) :
    F.map (R.map (η.app X)) = F.map (η.app (R.obj X)) := by
  letI := hη X
  have hloc : L.map (R.map (η.app X)) = L.map (η.app (R.obj X)) := by
    apply (cancel_epi (L.map (η.app X))).1
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map (η.naturality (η.app X)).symm
  have hr := coresolution_resolved_map_eq R L e
    (R.map (η.app X)) (η.app (R.obj X)) hloc
  letI := hresolved X
  letI := hresolved (R.obj X)
  have hnr : F.map (R.map (η.app (R.obj X))) =
      F.map (η.app (R.obj (R.obj X))) := by
    apply (cancel_epi (F.map (η.app (R.obj X)))).1
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (η.naturality (η.app (R.obj X))).symm
  have hn := congrArg F.map (η.naturality (R.map (η.app X)))
  simp only [Functor.id_map, Functor.map_comp] at hn
  rw [hr, hnr] at hn
  exact (cancel_mono (F.map (η.app (R.obj (R.obj X))))).1 hn

omit hcoh in
/-- A coresolution whose already resolved objects are acyclic for the
comparison gives the full right-derived universal property. -/
theorem coresolution_isRightDerivedFunctor_of_resolved_isIso
    (hresolved : ∀ X : C, IsIso (F.map (η.app (R.obj X)))) :
    RF.IsRightDerivedFunctor (coresolutionDerivedUnit R η L F RF e) W :=
  coresolution_isRightDerivedFunctor R η L W hη e
    (coresolution_coherence_of_resolved_isIso R η L hη e hresolved)

end ToricPower

end

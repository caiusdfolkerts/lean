module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# An absolute derived universal property from an actual resolution

Let `R` be an endofunctor with an augmentation `ε : R ⟶ Id`.  Suppose
its components become isomorphisms under the localization `L`, and an
actual factorization identifies `L ⋙ LF` with `R ⋙ F`.  If `F` identifies
the two iterated augmentations `R ε` and `ε R`, then the comparison
`L ⋙ LF ⟶ F` is a genuine right Kan extension, hence a left derived
functor.  The proof constructs the universal lift and proves uniqueness.

The hypotheses are purely categorical and are discharged for the actual
cellular cone replacement in `CellularDerivedRealization`.  In particular,
the coherence hypothesis is not an assumed derived adjunction.

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
  (R : C ⥤ C) (ε : R ⟶ 𝟭 C)

/-- The actual augmentation gives an isomorphism after any functor that
inverts its components. -/
def resolutionCompIso (L : C ⥤ D)
    (hε : ∀ X : C, IsIso (L.map (ε.app X))) : R ⋙ L ≅ L :=
  NatIso.ofComponents (fun X => by
    letI := hε X
    exact asIso (L.map (ε.app X))) (fun f => by
      dsimp
      rw [← L.map_comp, ← L.map_comp]
      exact congrArg L.map (ε.naturality f))

@[simp]
theorem resolutionCompIso_hom_app (L : C ⥤ D)
    (hε : ∀ X : C, IsIso (L.map (ε.app X))) (X : C) :
    (resolutionCompIso R ε L hε).hom.app X = L.map (ε.app X) := rfl

@[simp]
theorem resolutionCompIso_inv_app (L : C ⥤ D)
    (hε : ∀ X : C, IsIso (L.map (ε.app X))) (X : C) :
    letI := hε X
    (resolutionCompIso R ε L hε).inv.app X = inv (L.map (ε.app X)) := rfl

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (hε : ∀ X : C, IsIso (L.map (ε.app X)))
  (F : C ⥤ E) (LF : D ⥤ E) (e : L ⋙ LF ≅ R ⋙ F)

/-- The actual comparison from the localized resolved functor. -/
def resolutionDerivedCounit : L ⋙ LF ⟶ F :=
  e.hom ≫ whiskerRight ε F ≫ F.leftUnitor.hom

@[simp]
theorem resolutionDerivedCounit_app (X : C) :
    (resolutionDerivedCounit R ε L F LF e).app X =
      e.hom.app X ≫ F.map (ε.app X) := by
  simp only [resolutionDerivedCounit, NatTrans.comp_app, whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.comp_id]
  change e.hom.app X ≫ F.map (ε.app X) ≫ 𝟙 (F.obj X) = _
  exact congrArg (fun f => e.hom.app X ≫ f) (Category.comp_id (F.map (ε.app X)))

variable {F LF}

/-- The universal lift on the original category, before using the fully
faithful restriction functor of the localization. -/
def resolutionDerivedLiftPre (G : D ⥤ E) (β : L ⋙ G ⟶ F) :
    L ⋙ G ⟶ L ⋙ LF :=
  (resolutionCompIso R ε (L ⋙ G) (fun X => by
    letI := hε X
    exact inferInstanceAs (IsIso (G.map (L.map (ε.app X)))))).inv ≫
      whiskerLeft R β ≫ e.inv

@[simp]
theorem resolutionDerivedLiftPre_app (G : D ⥤ E) (β : L ⋙ G ⟶ F) (X : C) :
    letI := hε X
    (resolutionDerivedLiftPre R ε L hε e G β).app X =
      inv (G.map (L.map (ε.app X))) ≫ β.app (R.obj X) ≫ e.inv.app X := rfl

/-- The actual universal candidate, obtained from full faithfulness of
restriction along the localization. -/
def resolutionDerivedLift (G : D ⥤ E) (β : L ⋙ G ⟶ F) : G ⟶ LF :=
  (Localization.whiskeringLeftFunctor' L W E).preimage
    (resolutionDerivedLiftPre R ε L hε e G β)

@[simp]
theorem resolutionDerivedLift_app (G : D ⥤ E) (β : L ⋙ G ⟶ F) (X : C) :
    letI := hε X
    (resolutionDerivedLift R ε L W hε e G β).app (L.obj X) =
      inv (G.map (L.map (ε.app X))) ≫ β.app (R.obj X) ≫ e.inv.app X := by
  letI := hε X
  exact congr_app (Functor.map_preimage
    (Localization.whiskeringLeftFunctor' L W E)
    (resolutionDerivedLiftPre R ε L hε e G β)) X

/-- The displayed universal candidate factors the original comparison. -/
theorem resolutionDerivedLift_fac (G : D ⥤ E) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (resolutionDerivedLift R ε L W hε e G β) ≫
      resolutionDerivedCounit R ε L F LF e = β := by
  ext X
  letI := hε X
  simp only [NatTrans.comp_app, whiskerLeft_app, resolutionDerivedLift_app,
    resolutionDerivedCounit_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := β.naturality (ε.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, IsIso.inv_hom_id_assoc]
  rfl

/- The two augmentation maps agree after applying the target functor.
This is the precise coherence used in the uniqueness argument. -/
variable (hcoh : ∀ X : C,
  F.map (R.map (ε.app X)) = F.map (ε.app (R.obj X)))

include hε hcoh

theorem resolutionDerivedLift_unique (G : D ⥤ E) (β : L ⋙ G ⟶ F)
    (γ : G ⟶ LF)
    (hγ : ∀ X : C, γ.app (L.obj X) ≫ e.hom.app X ≫ F.map (ε.app X) = β.app X) :
    γ = resolutionDerivedLift R ε L W hε e G β := by
  apply Localization.natTrans_ext L W
  intro X
  letI := hε X
  apply (cancel_mono (e.hom.app X)).1
  rw [resolutionDerivedLift_app]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply (cancel_epi (G.map (L.map (ε.app X)))).1
  simp only [IsIso.hom_inv_id_assoc]
  change G.map (L.map (ε.app X)) ≫ γ.app (L.obj X) ≫ e.hom.app X =
    β.app (R.obj X) ≫ 𝟙 (F.obj (R.obj X))
  rw [Category.comp_id]
  let δ : L ⋙ G ⟶ R ⋙ F := whiskerLeft L γ ≫ e.hom
  have hn := δ.naturality (ε.app X)
  dsimp only [δ, NatTrans.comp_app, whiskerLeft_app, Functor.comp_map] at hn
  rw [hcoh X] at hn
  simp only [Category.assoc, hγ (R.obj X)] at hn
  exact hn

/-- A genuine left-derived universal property.  Neither existence nor
uniqueness of the universal lift is assumed. -/
theorem resolution_isLeftDerivedFunctor :
    LF.IsLeftDerivedFunctor (resolutionDerivedCounit R ε L F LF e) W := by
  apply (Functor.isLeftDerivedFunctor_iff_isRightKanExtension _ _ W).2
  refine ⟨⟨IsTerminal.ofUniqueHom (fun G =>
    CostructuredArrow.homMk
      (resolutionDerivedLift R ε L W hε e G.left G.hom)
      (resolutionDerivedLift_fac R ε L W hε e G.left G.hom)) ?_⟩⟩
  intro G γ
  apply CostructuredArrow.hom_ext
  apply resolutionDerivedLift_unique R ε L W hε e hcoh G.left G.hom γ.left
  intro X
  have h := congr_app γ.w X
  simp only [Functor.RightExtension.mk, CostructuredArrow.mk_left,
    NatTrans.comp_app, whiskerLeft_app, resolutionDerivedCounit_app,
    Category.comp_id, Category.assoc] at h
  change γ.left.app (L.obj X) ≫
    (resolutionDerivedCounit R ε L F LF e).app X = G.hom.app X at h
  rw [resolutionDerivedCounit_app] at h
  exact h

/-- The same concrete construction remains universal after every
postcomposition.  This is the absolute, rather than merely total,
left-derived property. -/
theorem resolution_isAbsoluteLeftDerivedFunctor (T : E ⥤ E') :
    (LF ⋙ T).IsLeftDerivedFunctor
      ((Functor.associator L LF T).inv ≫
        whiskerRight (resolutionDerivedCounit R ε L F LF e) T) W := by
  let eT : L ⋙ (LF ⋙ T) ≅ R ⋙ (F ⋙ T) :=
    (Functor.associator L LF T).symm ≪≫ isoWhiskerRight e T ≪≫
      Functor.associator R F T
  have hT := resolution_isLeftDerivedFunctor R ε L W hε eT
    (fun X => congrArg T.map (hcoh X))
  have he : resolutionDerivedCounit R ε L (F ⋙ T) (LF ⋙ T) eT =
      (Functor.associator L LF T).inv ≫
        whiskerRight (resolutionDerivedCounit R ε L F LF e) T := by
    ext X
    simp only [resolutionDerivedCounit_app, eT, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      isoWhiskerRight_hom, whiskerRight_app, Functor.comp_map,
      Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp]
  rwa [he] at hT

end ToricPower

end

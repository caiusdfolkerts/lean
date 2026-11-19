module

public import ToricPower.CategoricalFoundations
public import ToricPower.CompactGeneratorExtraction
public import ToricPower.CoproductCompactFunctor
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Reflecting generation through a fully faithful exact functor

Splitting the pulled-back idempotent proves that a fully faithful
functor from an idempotent-complete category has a retract-closed image.
Consequently it preserves and reflects the actual thick envelopes.
Compact extraction then turns a right generator in the unbounded
ambient category into a classical generator in the source category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w

section Retracts

variable {C : Type u} [Category.{v} C] [IsIdempotentComplete C]
  {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) [F.Full] [F.Faithful]

/-- A target retract is the image of the actual splitting of its
pulled-back idempotent. -/
theorem fullyFaithful_map_stableUnderRetracts (P : ObjectProperty C)
    [P.IsStableUnderRetracts] : (P.map F).IsStableUnderRetracts where
  of_retract {Y Z} r hZ := by
    obtain ⟨X,hX,⟨e⟩⟩ := hZ
    let r' : Retract Y (F.obj X) := r.trans (Retract.ofIso e.symm)
    let p : X ⟶ X := F.preimage (r'.r ≫ r'.i)
    have map_p : F.map p = r'.r ≫ r'.i := F.map_preimage _
    have idem : p ≫ p = p := by
      apply F.map_injective
      rw [Functor.map_comp,map_p]
      simp only [Category.assoc,Retract.retract_assoc]
    obtain ⟨X',a,b,ab,ba⟩ := IsIdempotentComplete.idempotents_split X p idem
    have hX' : P X' := P.prop_of_retract (⟨a,b,ab⟩ : Retract X' X) hX
    have fixed : F.map a ≫ (r'.r ≫ r'.i) = F.map a := by
      rw [← map_p,← Functor.map_comp,← ba,← Category.assoc,ab,Category.id_comp]
    let iso : F.obj X' ≅ Y :=
      { hom := F.map a ≫ r'.r
        inv := r'.i ≫ F.map b
        hom_inv_id := by
          calc
            (F.map a ≫ r'.r) ≫ (r'.i ≫ F.map b) =
                (F.map a ≫ (r'.r ≫ r'.i)) ≫ F.map b := by simp only [Category.assoc]
            _ = F.map a ≫ F.map b := by rw [fixed]
            _ = 𝟙 _ := by rw [← Functor.map_comp,ab,CategoryTheory.Functor.map_id]
        inv_hom_id := by
          calc
            (r'.i ≫ F.map b) ≫ (F.map a ≫ r'.r) =
                r'.i ≫ (F.map b ≫ F.map a) ≫ r'.r := by simp only [Category.assoc]
            _ = r'.i ≫ (r'.r ≫ r'.i) ≫ r'.r := by
              rw [← Functor.map_comp,ba,map_p]
            _ = 𝟙 _ := by simp only [← Category.assoc,r'.retract,Category.id_comp] }
    exact ⟨X',hX',⟨iso⟩⟩

end Retracts

section Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [IsIdempotentComplete C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ] [F.IsTriangulated]

/-- The image is precisely the thick envelope of the image objects;
the reverse inclusion uses actual idempotent splitting. -/
theorem fullyFaithful_map_triangEnvelope (P : ObjectProperty C) [P.Nonempty] :
    P.triangEnvelope.map F = (P.map F).triangEnvelope := by
  letI := fullyFaithful_map_stableUnderRetracts F P.triangEnvelope
  apply le_antisymm
  · rintro Y ⟨X,hX,⟨e⟩⟩
    exact (P.map F).triangEnvelope.prop_of_iso e
      (exactFunctor_map_mem_triangEnvelope F P hX)
  · apply ((P.map F).triangEnvelope_le_iff (Q := P.triangEnvelope.map F)).mpr
    rintro Y ⟨X,hX,⟨e⟩⟩
    exact ⟨X,P.le_triangEnvelope X hX,⟨e⟩⟩

/-- Membership is reflected through the actual full and faithful
morphism map, not through a comparison of numerical invariants. -/
theorem fullyFaithful_mem_singleton_triangEnvelope_iff (G X : C) :
    (ObjectProperty.singleton (F.obj G)).triangEnvelope (F.obj X) ↔
      (ObjectProperty.singleton G).triangEnvelope X := by
  rw [← singleton_map_triangEnvelope F G,← fullyFaithful_map_triangEnvelope F]
  constructor
  · rintro ⟨Y,hY,⟨e⟩⟩
    exact (ObjectProperty.singleton G).triangEnvelope.prop_of_iso (F.preimageIso e) hY
  · intro hX
    exact ⟨X,hX,⟨Iso.refl _⟩⟩

variable [HasCoproducts.{w} D] [LocallySmall.{w} D]

/-- Compactness and right generation are required in the genuine
unbounded ambient category. The conclusion is classical generation
in the entire idempotent-complete source category. -/
theorem classicalGenerator_of_compact_rightGenerator_image
    (compact : ∀ X : C, CompactExtraction.CoproductCompact.{u',v',w} (F.obj X))
    (G : C) (generator : CompactExtraction.IsRightGenerator (F.obj G)) :
    (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  let P : ObjectProperty D := (⊤ : ObjectProperty C).map F
  let Q := (ObjectProperty.singleton (F.obj G)).triangEnvelope
  letI : P.IsTriangulated := by
    dsimp only [P]
    rw [ObjectProperty.map_top]
    infer_instance
  letI : P.IsStableUnderRetracts := fullyFaithful_map_stableUnderRetracts F ⊤
  have contained : Q ≤ P := by
    apply ((ObjectProperty.singleton (F.obj G)).triangEnvelope_le_iff (Q := P)).mpr
    rw [ObjectProperty.singleton_le_iff]
    exact ⟨G,trivial,⟨Iso.refl _⟩⟩
  have compactImage (Y : D) (hY : P Y) :
      CompactExtraction.CoproductCompact.{u',v',w} Y := by
    obtain ⟨X,_,⟨e⟩⟩ := hY
    exact CompactExtraction.coproductCompact_of_iso e (compact X)
  have whole := CompactExtraction.le_of_rightGenerator P Q contained compactImage
    (F.obj G) ((ObjectProperty.singleton (F.obj G)).le_triangEnvelope _ (by simp)) generator
  apply le_antisymm le_top
  intro X _
  apply (fullyFaithful_mem_singleton_triangEnvelope_iff F G X).mp
  exact whole _ ⟨X,trivial,⟨Iso.refl _⟩⟩

end Triangulated

end ToricPower

end

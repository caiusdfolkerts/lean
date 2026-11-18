module

public import ToricPower.InverseSerreAmbientFullyFaithful
public import ToricPower.FullyFaithfulThickImage

/-!
# Classical generation from an actual unbounded inverse-Serre pairing

The geometric left-orthogonality test is imposed on all unbounded
objects. The pairing converts it to right detection by the actual
representing object. Compact extraction and full-faithful thick-image
reflection then prove classical generation in the literal bounded
source category. No generation statement about the whole diagram
category is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.SerrePairing

universe r u v u' v' w
variable (k : Type r) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (i T : C ⥤ D)
variable (pairing : ∀ (G : C) (E : D),
  (E ⟶ i.obj G) ≃ₗ[k] Module.Dual k (T.obj G ⟶ E))

include pairing in
/-- Left detection uses every shift of every unbounded ambient object. -/
theorem rightGenerator_of_inverseSerre
    (G : C)
    (leftDetector : ∀ Y : D,
      (∀ (n : ℤ) (f : Y⟦n⟧ ⟶ i.obj G), f = 0) → IsZero Y) :
    CompactExtraction.IsRightGenerator (T.obj G) := by
  intro Y vanished
  apply leftDetector Y
  intro n f
  apply (pairing G (Y⟦n⟧)).injective
  apply LinearMap.ext
  intro g
  have zero : g = 0 := by
    let e := shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)
    have shifted : g⟦(-n)⟧' = 0 := by
      apply (cancel_mono (e.hom.app Y)).mp
      simpa only [zero_comp] using
        vanished (-n) (g⟦(-n)⟧' ≫ e.hom.app Y)
    apply (shiftFunctor D (-n)).map_injective
    simpa only [CategoryTheory.Functor.map_zero] using shifted
  simp only [zero, map_zero, LinearMap.zero_apply]

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [IsIdempotentComplete C]
  [IsTriangulated D] [HasCoproducts.{w} D] [LocallySmall.{w} D]
  [i.Additive] [i.Linear k] [i.Full] [i.Faithful]
  [T.CommShift ℤ] [T.IsTriangulated]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- All categorical hypotheses refer to the actual source and ambient
categories. In particular, the conclusion is generation by the original
object `G`, and compactness is proved for its ambient representing
functor rather than assumed from a numerical detection criterion. -/
theorem classicalGenerator_of_inverseSerre
    (sourceNaturality : ∀ (G : C) {E F : D} (a : E ⟶ F)
      (f : F ⟶ i.obj G) (g : T.obj G ⟶ E),
      pairing G E (a ≫ f) g = pairing G F f (g ≫ a))
    (targetNaturality : ∀ {G H : C} (a : G ⟶ H) (E : D)
      (f : E ⟶ i.obj G) (g : T.obj H ⟶ E),
      pairing H E (f ≫ i.map a) g = pairing G E f (T.map a ≫ g))
    (compact : ∀ X : C, CompactExtraction.CoproductCompact.{u',v',w} (T.obj X))
    (G : C)
    (leftDetector : ∀ Y : D,
      (∀ (n : ℤ) (f : Y⟦n⟧ ⟶ i.obj G), f = 0) → IsZero Y) :
    (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator := by
  let fullyFaithful := ambientRepresentingFunctorFullyFaithful k i T pairing
    sourceNaturality targetNaturality
  letI : T.Full := fullyFaithful.full
  letI : T.Faithful := fullyFaithful.faithful
  exact classicalGenerator_of_compact_rightGenerator_image T compact G
    (rightGenerator_of_inverseSerre k i T pairing G leftDetector)

end ToricPower.SerrePairing

end

module

public import ToricPower.CellularConeResolution
public import ToricPower.CellularVectorKProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# K-projectivity of the finite cellular cone replacement

The cone construction acts on arbitrary unbounded complexes.  Its terms are
K-projective because the actual vector cover is K-projective and the left
orthogonal of the acyclic homotopy category is triangulated.  The final
comparison between the two iterated augmentations is an actual homotopy,
obtained from the faithful localization of maps out of K-projectives.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

open scoped ZeroObject

namespace ToricPower

universe u v w

section Generic

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Mapping cones of actual K-projective complexes are K-projective.
The argument uses the actual distinguished mapping-cone triangle. -/
theorem mappingCone_isKProjective {K L : CochainComplex A ℤ}
    (f : K ⟶ L) [K.IsKProjective] [L.IsKProjective] :
    (mappingCone f).IsKProjective := by
  rw [CochainComplex.isKProjective_iff_leftOrthogonal]
  exact (HomotopyCategory.subcategoryAcyclic A).leftOrthogonal.ext_of_isTriangulatedClosed₃
    (mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)
    (CochainComplex.IsKProjective.leftOrthogonal K)
    (CochainComplex.IsKProjective.leftOrthogonal L)

/-- The zero complex is K-projective without a boundedness convention. -/
theorem zeroComplex_isKProjective :
    (0 : CochainComplex A ℤ).IsKProjective where
  nonempty_homotopy_zero f _ :=
    ⟨Homotopy.ofEq ((isZero_zero (CochainComplex A ℤ)).eq_of_src f 0)⟩

variable [HasDerivedCategory A]

/-- Equality after localization of two maps out of an actual K-projective
complex gives an actual chain homotopy. -/
def homotopyOfQMapEq {K L : CochainComplex A ℤ} [K.IsKProjective]
    {f g : K ⟶ L} (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient A (.up ℤ)).obj L)).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app L)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

end Generic

namespace Cellular

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- Every stage of the actual finite cone construction is K-projective.
There is no boundedness hypothesis on the input complex. -/
theorem finiteConeResolution_isKProjective (m : ℕ)
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    CochainComplex.IsKProjective ((finiteConeResolution k m).functor.obj X) := by
  induction m generalizing X with
  | zero => exact zeroComplex_isKProjective
  | succ m ih =>
    change (mappingCone ((complexResolutionArrow k (finiteConeResolution k m)).app X)).IsKProjective
    letI : CochainComplex.IsKProjective
        ((diagramSyzygyComplexFunctor k ⋙ (finiteConeResolution k m).functor).obj X) :=
      ih ((diagramSyzygyComplexFunctor k).obj X)
    letI : CochainComplex.IsKProjective ((diagramCoverComplexFunctor k).obj X) :=
      diagramCoverComplex_isKProjective k X
    exact mappingCone_isKProjective _

variable [HasDerivedCategory (C ⥤ ModuleCat.{u} k)]

/-- The two maps from the twice-resolved complex to the resolved complex
are genuinely homotopic.  Naturality makes their composites with the
augmentation equal; the augmentation is a quasi-isomorphism and the
source is K-projective. -/
def finiteConeResolution_augmentationHomotopy (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X))
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    Homotopy
      ((finiteConeResolution k m).functor.map
        ((finiteConeResolution k m).augmentation.app X))
      ((finiteConeResolution k m).augmentation.app
        ((finiteConeResolution k m).functor.obj X)) := by
  let R : ComplexResolutionStage k (C := C) := finiteConeResolution k m
  letI := hε X
  letI := finiteConeResolution_isKProjective k m (R.functor.obj X)
  apply homotopyOfQMapEq
  apply (cancel_mono (DerivedCategory.Q.map (R.augmentation.app X))).1
  simp only [← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map
    (R.augmentation.naturality (R.augmentation.app X))

/-- Every additive realization identifies the two actual augmentation
maps in its target derived category.  This is the coherence needed for
the universal left-derived comparison, rather than an assumed coherence. -/
theorem finiteConeResolution_augmentationCoherence
    {A : Type w} [Category.{u} A] [Abelian A] [HasDerivedCategory A]
    (H : (C ⥤ ModuleCat.{u} k) ⥤ A) [H.Additive] (m : ℕ)
    (hε : ∀ X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ,
      QuasiIso ((finiteConeResolution k m).augmentation.app X))
    (X : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ) :
    DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map
        ((finiteConeResolution k m).functor.map
          ((finiteConeResolution k m).augmentation.app X))) =
      DerivedCategory.Q.map ((H.mapHomologicalComplex (.up ℤ)).map
        ((finiteConeResolution k m).augmentation.app
          ((finiteConeResolution k m).functor.obj X))) :=
  DerivedCategory.Q_map_eq_of_homotopy A
    (H.mapHomotopy (finiteConeResolution_augmentationHomotopy k m hε X))

end Cellular

end ToricPower

end

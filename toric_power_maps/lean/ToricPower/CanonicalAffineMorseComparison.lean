module

public import ToricPower.CanonicalAffineCoresolutionPresentation
public import ToricPower.ArrangementMorseMappedComposition

/-! # Morse transport through the actual affine replacement comparison

The same original Hom functor occurs on both sides. Its whole complex
comparison is induced by the identity of the genuine affine replacement,
with the scheme, opens, and coefficient diagram still abstract.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

section AbstractComplex

variable {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]
  {J : Type} [Category.{0} J]

/-- The original Hom and Morse functors preserve the acyclicity
comparison induced by an isomorphism of their input complexes. -/
theorem universalLocalMorse_hom_acyclic_iff_of_complexIso
    (P : Jᵒᵖ ⥤ C) (p : UniversalIncidenceObject A ⥤ J)
    {K L : CochainComplex C ℤ} (e : K ≅ L) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic ↔
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p).mapHomologicalComplex (.up ℤ)).obj L)).Acyclic := by
  let H := Cellular.homDiagram ℂ P ⋙
    (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p
  let comparison := (universalLocalMorse A ℂ c region).mapIso
    ((H.mapHomologicalComplex (.up ℤ)).mapIso e)
  constructor
  · intro acyclic q
    exact HomologicalComplex.ExactAt.of_iso (acyclic q) comparison
  · intro acyclic q
    exact HomologicalComplex.ExactAt.of_iso (acyclic q) comparison.symm

end AbstractComplex

variable
  (X : Scheme) [Linear ℂ (QCoh X)]
  {J : Type} [Category.{0} J]
  {I : Type*} (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]

/-- The whole original Hom complex has the same Morse vanishing after
the fixed affine replacement presentation and the original replacement. -/
theorem universalLocalMorse_canonicalAffineHom_acyclic_iff
    (P : Jᵒᵖ ⥤ QCoh X) (p : UniversalIncidenceObject A ⥤ J)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p).mapHomologicalComplex (.up ℤ)).obj
        ((canonicalAffineCoresolution opens l).obj K))).Acyclic ↔
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p).mapHomologicalComplex (.up ℤ)).obj
        ((affineConeCoresolution opens l).obj K))).Acyclic :=
  universalLocalMorse_hom_acyclic_iff_of_complexIso A c region P p
    ((canonicalAffineCoresolutionIso opens l).app K)

/-- The complete coefficient family is transported before any concrete
geometric replacement is evaluated. -/
theorem universalLocalMorse_canonicalAffineHom_all_acyclic_iff
    (P : Jᵒᵖ ⥤ QCoh X) (p : UniversalIncidenceObject A ⥤ J) (l : List I) :
    (∀ K : CochainComplex (QCoh X) ℤ,
      ((universalLocalMorse A ℂ c region).obj
        (((Cellular.homDiagram ℂ P ⋙
          (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p
          ).mapHomologicalComplex (.up ℤ)).obj
          ((canonicalAffineCoresolution opens l).obj K))).Acyclic) ↔
    (∀ K : CochainComplex (QCoh X) ℤ,
      ((universalLocalMorse A ℂ c region).obj
        (((Cellular.homDiagram ℂ P ⋙
          (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj p
          ).mapHomologicalComplex (.up ℤ)).obj
          ((affineConeCoresolution opens l).obj K))).Acyclic) :=
  forall_congr' (fun K => universalLocalMorse_canonicalAffineHom_acyclic_iff
    A c region X opens P p l K)

end ToricPower.IntegralArrangement

end

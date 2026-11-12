module

public import ToricPower.ArrangementMorseHomIso

/-! # Composing the literal cochain pullback in a Morse model

This equality is proved with abstract labels and an abstract coefficient
complex. It retains the original Hom diagram, the actual projection and
all differentials. No coefficient boundedness is used.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]
  {J : Type} [Category.{0} J]
  (Q : Jᵒᵖ ⥤ C) (projection : UniversalIncidenceObject A ⥤ J)

/-- Mapping a composite coefficient functor and mapping its two factors
give the identical actual Morse acyclicity predicate. -/
theorem universalLocalMorse_mappedComposition_acyclic_iff
    (K : CochainComplex C ℤ) :
    ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ Q ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj projection
        ).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic ↔
    ((universalLocalMorse A ℂ c region).obj
      ((((Functor.whiskeringLeft (UniversalIncidenceObject A) J (ModuleCat ℂ)).obj
        projection).mapHomologicalComplex (.up ℤ)).obj
        (((Cellular.homDiagram ℂ Q).mapHomologicalComplex (.up ℤ)).obj K))).Acyclic :=
  Iff.rfl

end ToricPower.IntegralArrangement
end

module

public import Mathlib.CategoryTheory.Whiskering

/-! # Composition of reconstruction factors before geometric specialization -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

variable {A B C D E : Type*} [Category* A] [Category* B]
  [Category* C] [Category* D] [Category* E]

/-- Compose the ordinary source factors while every functor is still
abstract; all associativities are the original categorical ones. -/
def composeReconstructionSourceFactors
    (Q₁ : A ⥤ C) (Q₂ : B ⥤ D) (R : C ⥤ D) (L : D ⥤ E)
    (replacement : A ⥤ A) (H : A ⥤ B) (F : B ⥤ E)
    (source : Q₁ ⋙ R ≅ replacement ⋙ H ⋙ Q₂)
    (realization : Q₂ ⋙ L ≅ F) :
    Q₁ ⋙ (R ⋙ L) ≅ replacement ⋙ H ⋙ F :=
  Functor.isoWhiskerRight source L ≪≫
    Functor.isoWhiskerLeft (replacement ⋙ H) realization

/-- The actual coaugmentation and the target factor determine the
factor on the actual replacement. -/
def composeReconstructionTargetFactors
    (Q : A ⥤ C) (T : C ⥤ E) (replacement : A ⥤ A) (G : A ⥤ E)
    (coaugmentation : Q ≅ replacement ⋙ Q) (target : Q ⋙ T ≅ G) :
    Q ⋙ T ≅ replacement ⋙ G :=
  Functor.isoWhiskerRight coaugmentation T ≪≫
    Functor.isoWhiskerLeft replacement target

end ToricPower

end

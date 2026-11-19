module

public import ToricPower.FiniteFunctorTotalComparison
public import ToricPower.FiniteFunctorTotalSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Recovering the original resolved evaluation from a cellular total

The actual top-augmentation square compares the genuine finite total
with ordinary realization. Two-out-of-three then proves that the
original resolved evaluation is a quasi-isomorphism. Neither input
complex has a degree bound.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive]
  (H : A ⥤ B) [H.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient H n)

/-- The original natural top map followed by the canonical single-row
identification; all horizontal and vertical signs remain fixed. -/
def topComparison : functor Φ width ⟶
    H.mapHomologicalComplex (.up ℤ) ⋙
      shiftFunctor (CochainComplex B ℤ) (-(n : ℤ)) :=
  comparison τ width ≫ (singleTotalNatIso H n retained).hom

def topEvaluation {L : CochainComplex A ℤ} {Y : CochainComplex B ℤ}
    (evaluation : (H.mapHomologicalComplex (.up ℤ)).obj L ⟶ Y) :
    total Φ width L ⟶ Y⟦-(n : ℤ)⟧ :=
  (topComparison Φ H n width retained τ).app L ≫ evaluation⟦-(n : ℤ)⟧'

/-- This equation retains the actual resolution map and the actual
evaluation map, rather than choosing a homology identification. -/
@[reassoc]
theorem topEvaluation_resolution_square
    {P L : CochainComplex A ℤ} (resolution : P ⟶ L)
    {Y : CochainComplex B ℤ}
    (evaluation : (H.mapHomologicalComplex (.up ℤ)).obj L ⟶ Y) :
    (functor Φ width).map resolution ≫ topEvaluation Φ H n width retained τ evaluation =
      (topComparison Φ H n width retained τ).app P ≫
        ((H.mapHomologicalComplex (.up ℤ)).map resolution ≫ evaluation)⟦-(n : ℤ)⟧' := by
  unfold topEvaluation
  rw [← Category.assoc, (topComparison Φ H n width retained τ).naturality resolution]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

/-- The complete cellular calculation proves a quasi-isomorphism of
the original ordinary evaluation after the original resolution. -/
theorem resolvedEvaluation_quasiIso
    {P L : CochainComplex A ℤ} (resolution : P ⟶ L)
    {Y : CochainComplex B ℤ}
    (evaluation : (H.mapHomologicalComplex (.up ℤ)).obj L ⟶ Y)
    [QuasiIso ((functor Φ width).map resolution)]
    [QuasiIso (coefficientMap τ width P)]
    [QuasiIso (topEvaluation Φ H n width retained τ evaluation)] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map resolution ≫ evaluation) := by
  haveI first : QuasiIso ((topComparison Φ H n width retained τ).app P) := by
    change QuasiIso (coefficientMap τ width P ≫ (singleTotalIso H n P retained).hom)
    infer_instance
  haveI composite : QuasiIso
      ((topComparison Φ H n width retained τ).app P ≫
        ((H.mapHomologicalComplex (.up ℤ)).map resolution ≫ evaluation)⟦-(n : ℤ)⟧') := by
    rw [← topEvaluation_resolution_square]
    infer_instance
  have shifted := quasiIso_of_comp_left
    ((topComparison Φ H n width retained τ).app P)
    (((H.mapHomologicalComplex (.up ℤ)).map resolution ≫ evaluation)⟦-(n : ℤ)⟧')
  exact (CochainComplex.quasiIso_shift_iff _ (-(n : ℤ))).mp shifted

end ToricPower.FunctorTotal

end

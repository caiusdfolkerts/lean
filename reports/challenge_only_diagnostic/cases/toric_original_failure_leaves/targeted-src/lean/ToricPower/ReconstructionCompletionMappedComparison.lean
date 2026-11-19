module

public import ToricPower.ReconstructionCompletionModuleExtension
public import ToricPower.ReconstructionCompletionTopPrecompose

/-! # The original top comparison after mapping a complex

The natural transformation and its equivalence transport are checked
with all categories and functors abstract, before affine sheaves enter.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

variable {A C B : Type*} [Category* A] [Preadditive A]
  [Category* C] [Preadditive C] [Category* B] [Abelian B]
  [HasFiniteBiproducts B]
  (H : A ⥤ C) [H.Additive]
  (Φ : C ⥤ CochainComplex B ℕ) [Φ.Additive]
  (T : C ⥤ B) [T.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient T n)

/-- The same original comparison, as a whole natural transformation
on mapped input complexes. -/
def topComparisonAfterMap :=
  Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ))
    (topComparison Φ T n width retained τ)

theorem topComparisonAfterMap_quasiIso_iff (K : CochainComplex A ℤ) :
    QuasiIso ((topComparisonAfterMap H Φ T n width retained τ).app K) ↔
      QuasiIso ((topComparison Φ T n width retained τ).app
        ((H.mapHomologicalComplex (.up ℤ)).obj K)) := Iff.rfl

theorem topComparisonAfterMap_precompose_quasiIso_iff (K : CochainComplex A ℤ) :
    QuasiIso ((topComparison (H ⋙ Φ) (H ⋙ T) n width retained
      (Functor.whiskerLeft H τ)).app K) ↔
      QuasiIso ((topComparisonAfterMap H Φ T n width retained τ).app K) := Iff.rfl

variable {D : Type*} [Category* D] [Preadditive D]
  (E : D ≌ A) [E.functor.Additive] [E.inverse.Additive]

/-- The same natural comparison descends through an actual additive
equivalence of coefficient categories. -/
theorem topComparisonAfterMap_quasiIso_of_equivalence
    (localQuasiIso : ∀ M : CochainComplex D ℤ,
      QuasiIso ((topComparisonAfterMap (E.functor ⋙ H) Φ T n width retained τ).app M))
    (K : CochainComplex A ℤ) :
    QuasiIso ((topComparisonAfterMap H Φ T n width retained τ).app K) := by
  let M := (E.inverse.mapHomologicalComplex (.up ℤ)).obj K
  let e : (E.functor.mapHomologicalComplex (.up ℤ)).obj M ≅ K :=
    (NatIso.mapHomologicalComplex E.counitIso (.up ℤ)).app K
  letI : QuasiIso ((topComparison Φ T n width retained τ).app
      (((E.functor ⋙ H).mapHomologicalComplex (.up ℤ)).obj M)) :=
    (topComparisonAfterMap_quasiIso_iff (E.functor ⋙ H) Φ T n width retained τ M).mp
      (localQuasiIso M)
  let comparison := (H.mapHomologicalComplex (.up ℤ)).mapIso e.symm ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E.functor ⋙ H)) (.up ℤ)).app M
  apply (topComparisonAfterMap_quasiIso_iff H Φ T n width retained τ K).mpr
  exact ToricPower.reconstructionNatTrans_quasiIso_of_iso
    (topComparison Φ T n width retained τ) comparison

end ToricPower.FunctorTotal

end

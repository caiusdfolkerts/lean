module

public import ToricPower.ArrangementMorseCoproducts
public import ToricPower.NaturalComplexCoproductComparison
public import ToricPower.CellularLocalMorseVanishing

/-! # Actual local Morse vanishing survives every coefficient sum

Both sides of the particular section comparison preserve coproducts.
Vanishing therefore extends from the individual full coefficient
complexes to their unrestricted categorical sum.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k]
  {C H : Type u} [Category.{u} C] [Category.{u} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} k) :=
  HasDerivedCategory.standard _

theorem comparison_quasiIso_of_localMorse_acyclic
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (vanishes : ((localMorseComplexFunctor k j c arrows).obj K).Acyclic) :
    QuasiIso ((localSectionComparison k j c arrows).app K) := by
  let φ := (localSectionComparison k j c arrows).app K
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₁_iff_isIso₂
    (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ))
    (DerivedCategory.mappingCocone_triangle_distinguished φ)).mp
      (derivedComplex_isZero_of_acyclic _ vanishes)

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

theorem universalLocalMorse_coproduct_acyclic {I : Type}
    (family : I → CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat k) ℤ)
    (vanishes : ∀ i, ((universalLocalMorse A k c region).obj (family i)).Acyclic) :
    ((universalLocalMorse A k c region).obj (∐ family)).Acyclic := by
  let j := universalRegionInclusion A c region
  let arrows := universalRegionInitialArrows A c region
  letI : PreservesColimitsOfShape (Discrete I) (Cellular.localSectionComplexFunctor k j) :=
    universalLocalSection_preservesCoproducts A k c region I
  letI (i : I) : QuasiIso ((Cellular.localSectionComparison k j c arrows).app (family i)) :=
    Cellular.comparison_quasiIso_of_localMorse_acyclic k j c arrows (family i) (vanishes i)
  letI := naturalComparison_coproduct_quasiIso
    (Cellular.localSectionComparison k j c arrows) family
  exact Cellular.localMorse_acyclic_of_comparison_quasiIso k j c arrows (∐ family)

end ToricPower.IntegralArrangement

end

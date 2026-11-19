module

public import ToricPower.ArrangementMorseModuleExact
public import ToricPower.ModuleComplexFreeVanishing

/-! # Dimension shifting for the actual affine local Morse functor -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

/-- The actual affine coefficient functor followed by the genuine
single-diagram local Morse calculation. -/
def universalLocalMorseSingleFunctor
    (R : Type) [Ring R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k)) :
    ModuleCat.{0} R ⥤ CochainComplex (ModuleCat k) ℤ :=
  H ⋙ singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0 ⋙
    universalLocalMorse A k c region

instance universalLocalMorseSingleFunctor_preservesZeroMorphisms
    (R : Type) [Ring R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    [H.PreservesZeroMorphisms] :
    (universalLocalMorseSingleFunctor A k c region R H).PreservesZeroMorphisms := by
  unfold universalLocalMorseSingleFunctor
  infer_instance

theorem universalLocalMorseSingleFunctor_map_shortExact
    (R : Type) [Ring R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    [H.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map H).ShortExact)
    (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact) :
    (S.map (universalLocalMorseSingleFunctor A k c region R H)).ShortExact := by
  unfold universalLocalMorseSingleFunctor
  rw [ShortComplex.map_comp,ShortComplex.map_comp]
  exact Cellular.localMorseComplexFunctor_map_shortExact k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region)
    ((S.map H).map (singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0))
    ((exact S hS).map_of_exact _)

theorem universalLocalMorseSingleFunctor_isZero_X_above
    (R : Type) [Ring R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    (M : ModuleCat.{0} R) (q : ℤ) (high : (n : ℤ)+1 < q) :
    IsZero (((universalLocalMorseSingleFunctor A k c region R H).obj M).X q) :=
  universalLocalMorse_single_isZero_X_above A k c region (H.obj M) q high

/-- The complete local Morse calculation for all affine modules is
reduced to the literal unrestricted free-module calculation. -/
theorem universalLocalMorse_affineModules_acyclic_of_free
    (R : Type) [Ring R]
    (H : ModuleCat.{0} R ⥤ (UniversalIncidenceObject A ⥤ ModuleCat k))
    [H.PreservesZeroMorphisms]
    (exact : ∀ S : ShortComplex (ModuleCat.{0} R),
      S.ShortExact → (S.map H).ShortExact)
    (free : ∀ I : Type, ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (H.obj (ModuleCat.of R (I →₀ R))))).Acyclic)
    (M : ModuleCat.{0} R) :
    ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj (H.obj M))).Acyclic := by
  exact moduleComplexFunctor_acyclic_of_boundedTerms_free R k
    (universalLocalMorseSingleFunctor A k c region R H)
    (universalLocalMorseSingleFunctor_map_shortExact A k c region R H exact)
    ((n : ℤ)+1)
    (universalLocalMorseSingleFunctor_isZero_X_above A k c region R H)
    free M


end ToricPower.IntegralArrangement

end

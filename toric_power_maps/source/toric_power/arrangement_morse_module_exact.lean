module

public import ToricPower.ArrangementMorseBounds
public import ToricPower.ComplexCoconeShortExact
public import ToricPower.LinearHomComplexExact
public import ToricPower.LinearHomComplexBounds
public import ToricPower.BoundedExactFreeVanishing

/-! # Exact coefficient sequences and bounded local Morse calculation

The genuine local Morse functor preserves every short exact sequence of
single coefficient diagrams. Its upper degree bound comes from the
actual finite face resolution. Thus vanishing on unrestricted free
affine modules extends to every affine module by finite dimension
shifting, without a finite-generation hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.Cellular

variable (k : Type) [Field k] {C H : Type} [Category.{0} C] [Category.{0} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

instance localSectionComplexFunctor_preservesZeroMorphisms :
    (localSectionComplexFunctor k j).PreservesZeroMorphisms := by
  unfold localSectionComplexFunctor projectiveCoefficientComplexFunctor
  infer_instance

instance localMorseComplexFunctor_preservesZeroMorphisms :
    (localMorseComplexFunctor k j c arrows).PreservesZeroMorphisms := by
  unfold localMorseComplexFunctor
  infer_instance

theorem localMorseComplexFunctor_map_shortExact
    (S : ShortComplex (CochainComplex (C ⥤ ModuleCat k) ℤ)) (hS : S.ShortExact) :
    (S.map (localMorseComplexFunctor k j c arrows)).ShortExact := by
  apply ComplexCone.coconeFunctor_map_shortExact
  · exact hS.map_of_exact _
  · let P := localSectionResolution k (H := H)
    letI (i : ℤ) : Projective ((projectiveCochain P).X i) := by
      unfold projectiveCochain
      infer_instance
    exact linearHomComplex_map_shortExact k (projectiveCochain P)
      (S.map ((localDiagramRestriction k j).mapHomologicalComplex (.up ℤ)))
      (hS.map_of_exact _)

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

instance universalLocalMorse_preservesZeroMorphisms :
    (universalLocalMorse A k c region).PreservesZeroMorphisms :=
  Cellular.localMorseComplexFunctor_preservesZeroMorphisms k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region)

theorem universalLocalMorse_single_isZero_X_above
    (F : UniversalIncidenceObject A ⥤ ModuleCat k) (q : ℤ) (high : (n : ℤ)+1 < q) :
    IsZero (((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj F)).X q) := by
  let j := universalRegionInclusion A c region
  let K := (singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj F
  let P := Cellular.localSectionResolution k (H := UniversalRegionStar A c region)
  let target : CochainComplex (UniversalRegionStar A c region ⥤ ModuleCat k) ℤ :=
    ((Cellular.localDiagramRestriction k j).mapHomologicalComplex (.up ℤ)).obj K
  let stalk : CochainComplex (ModuleCat k) ℤ :=
    (((evaluation (UniversalIncidenceObject A) (ModuleCat k)).obj c).mapHomologicalComplex
    (.up ℤ)).obj K
  letI : (projectiveCochain P).IsStrictlyGE (-(n : ℤ)) :=
    universalRegionSectionCochain_isStrictlyGE A k c region
  letI : target.IsStrictlyLE 0 := by dsimp [target,K]; infer_instance
  letI : stalk.IsStrictlyLE 0 := by dsimp [stalk,K]; infer_instance
  let φ := (Cellular.localSectionComparison k j c
    (universalRegionInitialArrows A c region)).app K
  change IsZero (((mappingCone φ)⟦(-1 : ℤ)⟧).X q)
  apply IsZero.of_iso _ ((mappingCone φ).shiftFunctorObjXIso (-1) q (q + -1) rfl)
  rw [mappingCone.isZero_X_iff]
  constructor
  · exact stalk.isZero_of_isStrictlyLE 0 (q + -1 + 1) (by omega)
  · exact linearHomComplex_isZero_X_above k (projectiveCochain P) target
      (-(n : ℤ)) 0 (q + -1) (by omega)

end ToricPower.IntegralArrangement

end

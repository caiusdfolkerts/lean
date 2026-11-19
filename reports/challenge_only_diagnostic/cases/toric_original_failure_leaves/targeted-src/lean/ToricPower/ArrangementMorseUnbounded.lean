module

public import ToricPower.ProjectiveSectionUnbounded
public import ToricPower.ArrangementMorseBounds
public import ToricPower.ArrangementMorseSumVanishing

/-! # The actual local Morse comparison on unbounded coefficients

Vanishing on the single objects in every degree gives exact ordinary
coefficient rows and an isomorphism of the original section maps.
The genuine finite projective region resolution then assembles these
rows on every unbounded complex. This retains the literal local section
comparison and its mapping fiber.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.Cellular

variable (k : Type) [Field k]
  {C H : Type} [Category.{0} C] [Category.{0} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

/-- The canonical scalar section comparison is the original local
comparison on a single coefficient, through the specified indexing isos. -/
theorem scalarSection_quasiIso_of_localMorse_single_acyclic
    (F : C ⥤ ModuleCat k)
    (vanishes : ((localMorseComplexFunctor k j c arrows).obj
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj F)).Acyclic) :
    QuasiIso (scalarProjectiveSectionMap k
      (localSectionResolution k (H := H))
        ((initialCoefficientSectionNatTrans k j c arrows).app F)) := by
  letI := comparison_quasiIso_of_localMorse_acyclic k j c arrows
    ((singleFunctor (C ⥤ ModuleCat k) 0).obj F) vanishes
  let P := localSectionResolution k (H := H)
  let E := (evaluation C (ModuleCat k)).obj c
  let S := localDiagramRestriction k j
  let a := initialCoefficientSectionNatTrans k j c arrows
  let e := (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app F
  haveI : QuasiIso (e.hom ≫ scalarProjectiveSectionMap k P (a.app F)) := by
    change QuasiIso ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).hom.app F ≫
      scalarProjectiveSectionMap k P (a.app F))
    rw [← projectiveSingleSection_comparison k P S F E a]
    change QuasiIso ((localSectionComparison k j c arrows).app
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj F) ≫
        (projectiveCoefficientSingleIso k S P F).hom)
    infer_instance
  exact quasiIso_of_comp_left e.hom (scalarProjectiveSectionMap k P (a.app F))

/-- A bounded actual region resolution makes single-term Morse
vanishing sufficient for the original comparison on an arbitrary
unbounded coefficient complex. -/
theorem localMorse_acyclic_of_singleTerms
    (bound : ℕ)
    (terminates : ∀ m : ℕ, bound < m →
      IsZero ((localSectionResolution k (H := H)).complex.X m))
    (K : CochainComplex (C ⥤ ModuleCat k) ℤ)
    (vanishes : ∀ q : ℤ, ((localMorseComplexFunctor k j c arrows).obj
      ((singleFunctor (C ⥤ ModuleCat k) 0).obj (K.X q))).Acyclic) :
    ((localMorseComplexFunctor k j c arrows).obj K).Acyclic := by
  haveI : QuasiIso ((localSectionComparison k j c arrows).app K) :=
    projectiveSectionComparison_quasiIso_of_singleComparisons k
      (localDiagramRestriction k j) (localSectionResolution k (H := H))
      ((evaluation C (ModuleCat k)).obj c)
      (initialCoefficientSectionNatTrans k j c arrows) bound terminates K
      (fun q => scalarSection_quasiIso_of_localMorse_single_acyclic
        k j c arrows (K.X q) (vanishes q))
  exact localMorse_acyclic_of_comparison_quasiIso k j c arrows K

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))

/-- The actual universal local Morse complex on all integer degrees;
there is no bound on the target or on its coefficient dimensions. -/
theorem universalLocalMorse_acyclic_of_singleTerms
    (K : CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat k) ℤ)
    (vanishes : ∀ q : ℤ, ((universalLocalMorse A k c region).obj
      ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj (K.X q))).Acyclic) :
    ((universalLocalMorse A k c region).obj K).Acyclic :=
  Cellular.localMorse_acyclic_of_singleTerms k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region) n
    (universalRegionSectionResolution_term_isZero A k c region) K vanishes

end ToricPower.IntegralArrangement

end

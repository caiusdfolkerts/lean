module

public import ToricPower.ArrangementMorseUnbounded
public import ToricPower.AffineCoresolutionSectionComparison
public import ToricPower.AffineBoundedSourceAssembly

/-! # Local Morse vanishing on the genuine unbounded affine model

The ordinary section map and the finite projective augmentation are
treated separately. The actual affine calculation gives the first map
as an isomorphism and the second map as an exact-row augmentation. Their
original composite is therefore a quasi-isomorphism on the finite
affine coresolution of every unbounded quasicoherent complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.Cellular

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  (k : Type) [Field k]
  {C H : Type} [Category.{0} C] [Category.{0} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)
  (F : QCoh X ⥤ C ⥤ ModuleCat k) [F.Additive]

/-- Exact affine coefficient calculations imply vanishing of the
literal local Morse fiber on the actual unbounded affine replacement. -/
theorem localMorse_affineCoresolution_acyclic
    (bound : ℕ)
    (terminates : ∀ m : ℕ, bound < m →
      IsZero ((localSectionResolution k (H := H)).complex.X m))
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((localMorseComplexFunctor k j c arrows).obj
        ((singleFunctor (C ⥤ ModuleCat k) 0).obj
          (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M)))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((localMorseComplexFunctor k j c arrows).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution opens l).obj K))).Acyclic := by
  let S := localDiagramRestriction k j
  let P := localSectionResolution k (H := H)
  let a := initialCoefficientSectionNatTrans k j c arrows
  have singles (i : I) (M : QCoh (opens i).toScheme) :
      QuasiIso (scalarProjectiveSectionMap k P
        (a.app (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M)))) :=
    scalarSection_quasiIso_of_localMorse_single_acyclic k j c arrows _ (localVanishing i M)
  haveI : QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F a)
      (.up ℤ)).app ((affineConeCoresolution opens l).obj K)) := by
    apply affineCoresolution_mappedSection_quasiIso opens (Functor.whiskerLeft F a)
    intro i M
    haveI := singles i M
    exact scalarProjectiveSectionMap_section_isIso k P
      (a.app (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M)))
  haveI : QuasiIso ((projectiveCoefficientComplexUnit k (F ⋙ S) P).app
      ((affineConeCoresolution opens l).obj K)) := by
    apply affineCoresolution_projectiveCoefficientUnit_quasiIso
      opens (F ⋙ S) k P bound terminates
    intro i M q
    haveI := singles i M
    exact scalarProjectiveSectionMap_positive_exact k P
      (a.app (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M))) q
  haveI : QuasiIso ((localSectionComparison k j c arrows).app
      ((F.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution opens l).obj K))) := by
    change QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F a) (.up ℤ)).app
      ((affineConeCoresolution opens l).obj K) ≫
        (projectiveCoefficientComplexUnit k (F ⋙ S) P).app
          ((affineConeCoresolution opens l).obj K))
    infer_instance
  exact localMorse_acyclic_of_comparison_quasiIso k j c arrows _

end ToricPower.Cellular

namespace ToricPower.IntegralArrangement

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  (F : QCoh X ⥤ UniversalIncidenceObject A ⥤ ModuleCat k) [F.Additive]

/-- The universal geometric face-region calculation on the original
finite affine model, including arbitrary unbounded input complexes. -/
theorem universalLocalMorse_affineCoresolution_acyclic
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A k c region).obj
        ((singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
          (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M)))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A k c region).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution opens l).obj K))).Acyclic :=
  Cellular.localMorse_affineCoresolution_acyclic opens k
    (universalRegionInclusion A c region) c (universalRegionInitialArrows A c region) F n
    (universalRegionSectionResolution_term_isZero A k c region) localVanishing l K

end ToricPower.IntegralArrangement

end

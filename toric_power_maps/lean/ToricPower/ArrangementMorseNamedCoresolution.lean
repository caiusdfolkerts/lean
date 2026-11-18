module

public import ToricPower.ArrangementMorseCoresolution
public import ToricPower.ArrangementMorseFunctorIso

/-! # Affine Morse assembly through named actual coefficient functors

The local comparison is an isomorphism of whole functors. It is
evaluated only in this abstract theorem, so the actual geometry does
not have to normalize a large specialized pushforward object.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {X : Scheme.{0}} {I : Type*}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]
  {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  (F : QCoh X ⥤ UniversalIncidenceObject A ⥤ ModuleCat k) [F.Additive]

theorem universalLocalMorse_named_affine_single_acyclic
    (localModels : ∀ i : I, QCoh (opens i).toScheme ⥤
      UniversalIncidenceObject A ⥤ ModuleCat k)
    (comparison : ∀ i : I, localModels i ≅
      quasicoherentAffinePushforward (opens i).ι ⋙ F)
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A k c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
          ((localModels i).obj M))).Acyclic)
    (i : I) (M : QCoh (opens i).toScheme) :
    ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
        (F.obj ((quasicoherentAffinePushforward (opens i).ι).obj M)))).Acyclic :=
  property_of_composite_obj (quasicoherentAffinePushforward (opens i).ι) F
    (fun E => ((universalLocalMorse A k c region).obj
      ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj E)).Acyclic) M
    (universalLocalMorse_single_acyclic_of_functorIso A k c region
      (localModels i) (quasicoherentAffinePushforward (opens i).ι ⋙ F)
      (comparison i) (localVanishing i) M)

theorem universalLocalMorse_affineCoresolution_acyclic_of_named
    (localModels : ∀ i : I, QCoh (opens i).toScheme ⥤
      UniversalIncidenceObject A ⥤ ModuleCat k)
    (comparison : ∀ i : I, localModels i ≅
      quasicoherentAffinePushforward (opens i).ι ⋙ F)
    (localVanishing : ∀ (i : I) (M : QCoh (opens i).toScheme),
      ((universalLocalMorse A k c region).obj
        ((CochainComplex.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat k) 0).obj
          ((localModels i).obj M))).Acyclic)
    (l : List I) (K : CochainComplex (QCoh X) ℤ) :
    ((universalLocalMorse A k c region).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj ((affineConeCoresolution opens l).obj K))).Acyclic :=
  universalLocalMorse_affineCoresolution_acyclic opens A k c region F
    (universalLocalMorse_named_affine_single_acyclic opens A k c region F
      localModels comparison localVanishing) l K

end ToricPower.IntegralArrangement

end

module

public import ToricPower.SerrePairingDerivedNaturality
public import ToricPower.SerrePairingTargetNaturality

/-!
# Target naturality in actual derived Hom spaces

The signed pairing is compatible with every chain map between bounded
injective models. Its inverse-Nakayama factor is the literal mapped
chain map, ready for the canonical right-derived-unit comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v w
variable (k : Type u) [Field k]
variable {A : Type v} [Category.{u} A] [Abelian A] [Linear k A]

theorem finiteCochainSerreClassEquiv_target_naturality
    (T : A ⥤ A) [T.Additive] (J K : CochainComplex A ℤ)
    (pairingJ : ∀ q, CodomainPairing k T (J.X q))
    (pairingK : ∀ q, CodomainPairing k T (K.X q))
    (dJ : ∀ p q, Compatible k (pairingJ p) (pairingJ q) (J.d p q))
    (dK : ∀ p q, Compatible k (pairingK p) (pairingK q) (K.d p q))
    (h : J ⟶ K)
    (compatible : ∀ q, Compatible k (pairingJ q) (pairingK q) (h.f q))
    (supportJ : Finset ℤ) (outsideJ : ∀ q, q ∉ supportJ → IsZero (J.X q))
    (supportK : Finset ℤ) (outsideK : ∀ q, q ∉ supportK → IsZero (K.X q))
    (E : CochainComplex A ℤ) (x : CohomologyClass E J 0)
    (y : CohomologyClass (mappedCochainComplex T K) E 0) :
    finiteCochainSerreClassEquiv k T K pairingK E dK supportK outsideK
        (homClassPostcomp k E h 0 x) y =
      finiteCochainSerreClassEquiv k T J pairingJ E dJ supportJ outsideJ x
        (homClassPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E 0 y) := by
  have hx : (HomComplex.homologyLinearEquiv k E K 0).symm
      (homClassPostcomp k E h 0 x) =
        HomologicalComplex.homologyMap (linearHomComplexMap k E h) 0
          ((HomComplex.homologyLinearEquiv k E J 0).symm x) := by
    apply (HomComplex.homologyLinearEquiv k E K 0).injective
    rw [LinearEquiv.apply_symm_apply, homologyLinearEquiv_postcomp,
      LinearEquiv.apply_symm_apply]
  have hy : (HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).symm
      (homClassPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E 0 y) =
        HomologicalComplex.homologyMap
          (linearHomComplexPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E) 0
          ((HomComplex.homologyLinearEquiv k (mappedCochainComplex T K) E 0).symm y) := by
    apply (HomComplex.homologyLinearEquiv k (mappedCochainComplex T J) E 0).injective
    rw [LinearEquiv.apply_symm_apply, homologyLinearEquiv_precomp,
      LinearEquiv.apply_symm_apply]
  rw [finiteCochainSerreClassEquiv_apply, finiteCochainSerreClassEquiv_apply, hx, hy]
  exact congrArg
    (fun f : (linearHomComplex k E J).homology 0 ⟶
        (scalarDual k).obj (Opposite.op
          ((linearHomComplex k (mappedCochainComplex T K) E).homology 0)) =>
      (show (linearHomComplex k (mappedCochainComplex T K) E).homology 0 ⟶
          ModuleCat.of k k from
        f ((HomComplex.homologyLinearEquiv k E J 0).symm x))
          ((HomComplex.homologyLinearEquiv k (mappedCochainComplex T K) E 0).symm y))
    (finiteCochainSerreHomologyIso_target_naturality k T J K pairingJ pairingK dJ dK h
      compatible supportJ outsideJ supportK outsideK E)

variable [HasDerivedCategory.{w} A]

theorem homClassDerivedZeroEquivOfKInjective_postcomp
    {E J K : CochainComplex A ℤ} [J.IsKInjective] [K.IsKInjective] (h : J ⟶ K)
    (z : CohomologyClass E J 0) :
    homClassDerivedZeroEquivOfKInjective k E K (homClassPostcomp k E h 0 z) =
      homClassDerivedZeroEquivOfKInjective k E J z ≫ DerivedCategory.Q.map h := by
  rw [homClassDerivedZeroEquivOfKInjective_eq,
    homClassDerivedLinearEquivOfKInjective_postcomp,
    homClassDerivedZeroEquivOfKInjective_eq, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, (shiftFunctorZero (CochainComplex A ℤ) ℤ).hom.naturality,
    CategoryTheory.Functor.map_comp]
  rfl

theorem homClassDerivedZeroEquivOfKProjective_precomp
    {P Q E : CochainComplex A ℤ} [P.IsKProjective] [Q.IsKProjective] (h : P ⟶ Q)
    (z : CohomologyClass Q E 0) :
    homClassDerivedZeroEquivOfKProjective k P E (homClassPrecomp k h E 0 z) =
      DerivedCategory.Q.map h ≫ homClassDerivedZeroEquivOfKProjective k Q E z := by
  rw [homClassDerivedZeroEquivOfKProjective_eq,
    homClassDerivedLinearEquivOfKProjective_precomp,
    homClassDerivedZeroEquivOfKProjective_eq, Category.assoc]

theorem finiteDerivedSerreEquiv_target_chain_naturality
    (T : A ⥤ A) [T.Additive] (J K : CochainComplex A ℤ)
    (pairingJ : ∀ q, CodomainPairing k T (J.X q))
    (pairingK : ∀ q, CodomainPairing k T (K.X q))
    (dJ : ∀ p q, Compatible k (pairingJ p) (pairingJ q) (J.d p q))
    (dK : ∀ p q, Compatible k (pairingK p) (pairingK q) (K.d p q))
    (h : J ⟶ K)
    (compatible : ∀ q, Compatible k (pairingJ q) (pairingK q) (h.f q))
    (supportJ : Finset ℤ) (outsideJ : ∀ q, q ∉ supportJ → IsZero (J.X q))
    (supportK : Finset ℤ) (outsideK : ∀ q, q ∉ supportK → IsZero (K.X q))
    [J.IsKInjective] [K.IsKInjective]
    [(mappedCochainComplex T J).IsKProjective]
    [(mappedCochainComplex T K).IsKProjective]
    (E : CochainComplex A ℤ)
    (f : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj J)
    (g : DerivedCategory.Q.obj (mappedCochainComplex T K) ⟶ DerivedCategory.Q.obj E) :
    finiteDerivedSerreEquiv k T K pairingK E dK supportK outsideK
        (f ≫ DerivedCategory.Q.map h) g =
      finiteDerivedSerreEquiv k T J pairingJ E dJ supportJ outsideJ f
        (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map h) ≫ g) := by
  have hf : (homClassDerivedZeroEquivOfKInjective k E K).symm
      (f ≫ DerivedCategory.Q.map h) =
        homClassPostcomp k E h 0 ((homClassDerivedZeroEquivOfKInjective k E J).symm f) := by
    apply (homClassDerivedZeroEquivOfKInjective k E K).injective
    rw [LinearEquiv.apply_symm_apply, homClassDerivedZeroEquivOfKInjective_postcomp,
      LinearEquiv.apply_symm_apply]
  have hg : (homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) E).symm
      (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map h) ≫ g) =
        homClassPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E 0
          ((homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T K) E).symm g) := by
    apply (homClassDerivedZeroEquivOfKProjective k (mappedCochainComplex T J) E).injective
    rw [LinearEquiv.apply_symm_apply, homClassDerivedZeroEquivOfKProjective_precomp,
      LinearEquiv.apply_symm_apply]
  rw [finiteDerivedSerreEquiv_apply, finiteDerivedSerreEquiv_apply, hf, hg]
  exact finiteCochainSerreClassEquiv_target_naturality k T J K pairingJ pairingK dJ dK h
    compatible supportJ outsideJ supportK outsideK E _ _

end ToricPower.SerrePairing

end

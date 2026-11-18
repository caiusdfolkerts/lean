module

public import ToricPower.SingleRetractGeneratorTransfer

/-! ## Source module `ToricPower.CoherentDerivedTransfer`
Original SHA256: 9737634c93985279172d16e95df2ab099997646b426e48084277db83985dd4e0.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource13

/-!
# Generator transfer for the literal coherent derived category

This file specializes the categorical split-unit theorem to the exact finite
pushforward functor on coherent sheaves. All categories, direct-image functors,
and degree-zero embeddings are the literal constructions from
`ToricPower.CoherentDerived`.

The natural splitting is an explicit hypothesis. For toric power maps its
geometric construction uses the projection formula and the residue-zero
retraction of the pushed-forward structure sheaf. No exactness assumption on
pullback is necessary: bounded complexes are lifted termwise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u

local instance coherentTransferStandardDerivedCategory (X : Scheme.{u})
    [IsLocallyNoetherian X] : HasDerivedCategory.{u + 1} (Coh X) :=
  HasDerivedCategory.standard (Coh X)

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsFinite f]

/-- Actual coherent sheaf splittings with the same summand isomorphism
classes give the same classical generation criterion in the literal bounded
derived category. Repetitions of a summand have no effect. -/
theorem coherentSameSummands_generates_iff
    {I J : Type*} [Finite I] [Finite J] [Nonempty I] [Nonempty J]
    (A : I → Coh X) (B : J → Coh X) {M N : Coh X}
    (eM : M ≅ ⨁ A) (eN : N ≅ ⨁ B)
    (hAB : ∀ i, ∃ j, Nonempty (A i ≅ B j))
    (hBA : ∀ j, ∃ i, Nonempty (B j ≅ A i)) :
    generatesDbCoh (coherentSingle X M) ↔ generatesDbCoh (coherentSingle X N) := by
  exact same_summands_map_generates_iff
    (TauCeti.DerivedCategory.Bounded.singleFunctor (Coh X) 0) A B eM eN hAB hBA

/-- The genuine finite derived pushforward preserves generators whenever
every target is a retract of an object in its image. -/
theorem finiteDerivedPushforward_generates_of_retracts
    (hF : ∀ L : DbCoh Y, ∃ K : DbCoh X,
      Nonempty (Retract L ((finiteDerivedPushforward f).obj K)))
    (G : DbCoh X) (hG : generatesDbCoh G) :
    generatesDbCoh ((finiteDerivedPushforward f).obj G) :=
  obj_classicalGenerator_of_retracts (finiteDerivedPushforward f) G hG hF

/-- An actual natural splitting on exact coherent functors gives generator
transfer on bounded coherent derived categories. -/
theorem finiteDerivedPushforward_generates_of_splitUnit
    (U : Coh Y ⥤ Coh X) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (η : 𝟭 (Coh Y) ⟶ U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f)
    (π : U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f ⟶ 𝟭 (Coh Y))
    (hηπ : η ≫ π = 𝟙 (𝟭 (Coh Y)))
    (G : DbCoh X) (hG : generatesDbCoh G) :
    generatesDbCoh ((finiteDerivedPushforward f).obj G) := by
  exact boundedDerived_generator_of_additiveSplitUnit
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f) U η π hηπ G hG

/-- Exact finite pushforward needs only an additive split lift on coherent
sheaves; that lift is not assumed to act on the derived category. -/
theorem finiteDerivedPushforward_generates_of_additiveSplitUnit
    (U : Coh Y ⥤ Coh X) [U.Additive]
    (η : 𝟭 (Coh Y) ⟶ U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f)
    (π : U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f ⟶ 𝟭 (Coh Y))
    (hηπ : η ≫ π = 𝟙 (𝟭 (Coh Y)))
    (G : DbCoh X) (hG : generatesDbCoh G) :
    generatesDbCoh ((finiteDerivedPushforward f).obj G) := by
  exact boundedDerived_generator_of_additiveSplitUnit
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f) U η π hηπ G hG

/-- The degree-zero formulation of the same result is about the ordinary
coherent direct image, identified with its finite derived direct image. -/
theorem coherentPushforward_generates_of_splitUnit
    (U : Coh Y ⥤ Coh X) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (η : 𝟭 (Coh Y) ⟶ U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f)
    (π : U ⋙ TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f ⟶ 𝟭 (Coh Y))
    (hηπ : η ≫ π = 𝟙 (𝟭 (Coh Y)))
    (M : Coh X) (hM : generatesDbCoh (coherentSingle X M)) :
    generatesDbCoh (coherentSingle Y
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M)) := by
  exact (classicalGenerator_iff_of_iso (finiteDerivedPushforwardSingleIso f M)).mp
    (finiteDerivedPushforward_generates_of_splitUnit f U η π hηπ _ hM)

/-- A splitting of the actual coherent pullback--pushforward unit suffices.
It is not necessary to extend that splitting to arbitrary module sheaves. -/
theorem coherentPushforward_generates_of_unitSplit
    (ρ : TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f ⋙
      TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f ⟶ 𝟭 (Coh Y))
    (hρ : (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullbackPushforwardAdjunction f).unit ≫
      ρ = 𝟙 (𝟭 (Coh Y)))
    (M : Coh X) (hM : generatesDbCoh (coherentSingle X M)) :
    generatesDbCoh (coherentSingle Y
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M)) := by
  apply (classicalGenerator_iff_of_iso (finiteDerivedPushforwardSingleIso f M)).mp
  exact finiteDerivedPushforward_generates_of_additiveSplitUnit f
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullback f)
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pullbackPushforwardAdjunction f).unit
    ρ hρ (coherentSingle X M) hM

/-- A natural splitting of the literal scheme-module adjunction unit gives
generation transfer for ordinary coherent pushforward. Applying pullback
termwise to bounded representatives avoids any flatness hypothesis. -/
theorem coherentPushforward_generates_of_moduleUnitSplit
    (ρ : Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f ⟶ 𝟭 Y.Modules)
    (hρ : (Scheme.Modules.pullbackPushforwardAdjunction f).unit ≫ ρ = 𝟙 (𝟭 Y.Modules))
    (M : Coh X) (hM : generatesDbCoh (coherentSingle X M)) :
    generatesDbCoh (coherentSingle Y
      ((TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f).obj M)) := by
  exact coherentPushforward_generates_of_unitSplit f
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.unitProjection f ρ)
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.unitProjection_retract f ρ hρ)
    M hM

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource13

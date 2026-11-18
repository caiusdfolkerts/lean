module

public import ToricPower.ComplexFunctorDerived
public import ToricPower.FiniteCellularTotalDerivedComparison

/-!
# The finite-total comparison for a specified concrete complex functor

The given ordinary functor is retained throughout localization. An
actual natural isomorphism to the finite signed total transports the
proved comparison without unfolding the geometric functor in the
localization construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

universe v t
variable (k : Type) [Field k] {C : Type} [Category.{0} C]
  {B : Type v} [Category.{0} B] [Abelian B] [HasFiniteBiproducts B]
  [HasDerivedCategory (C ⥤ ModuleCat.{0} k)] [HasDerivedCategory B]
  (Φ : (C ⥤ ModuleCat.{0} k) ⥤ CochainComplex B ℕ) [Φ.Additive]
  (H : (C ⥤ ModuleCat.{0} k) ⥤ B) [H.Additive]
  (n width : ℕ) (retained : n < width)
  (τ : Φ ⟶ singleCoefficient H n)
  {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
  [∀ i, (detectors i).Additive]
  [∀ i, PreservesFiniteLimits (detectors i)]
  [∀ i, PreservesFiniteColimits (detectors i)]
  (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
  (epi : ∀ M, Epi (τ.app M))
  (onProjectives : ∀ (M : C ⥤ ModuleCat.{0} k), Projective M → ∀ i,
    QuasiIso (((detectors i).mapHomologicalComplex (.up ℕ)).map (τ.app M)))
  (lastZero : ∀ M, IsZero ((Φ.obj M).X width))
  (F : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ ⥤ CochainComplex B ℤ)
  (preserves : ∀ {K L : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso (F.map f))
  (comparison : F ≅ functor Φ width)
  (m : ℕ)
  (resolution : ∀ K : CochainComplex (C ⥤ ModuleCat.{0} k) ℤ,
    QuasiIso ((Cellular.finiteConeResolution k m).augmentation.app K))

/-- The genuine unbounded derived comparison, with the concrete
ordinary functor sealed before localization. -/
def sealedDerivedTotalLeftDerivedIso :
    complexFunctorDerived F preserves ≅
      Cellular.finiteConeRealizationStageDerived k H m ⋙
        shiftFunctor (DerivedCategory B) (-(n : ℤ)) :=
  complexFunctorDerivedIso F (functor Φ width) preserves
    (complexFunctor_preservesQuasiIso_of_iso F (functor Φ width) preserves comparison)
    comparison ≪≫
  derivedTotalLeftDerivedIso k Φ H n width retained τ detectors detect epi onProjectives
    lastZero (complexFunctor_preservesQuasiIso_of_iso F (functor Φ width) preserves comparison)
    m resolution

end ToricPower.FunctorTotal

end

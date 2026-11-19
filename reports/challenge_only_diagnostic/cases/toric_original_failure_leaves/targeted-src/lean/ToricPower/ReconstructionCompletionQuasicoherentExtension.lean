module

public import ToricPower.ReconstructionCompletionModuleExtension
public import ToricPower.QuasicoherentCategory
public import Mathlib.Data.Complex.Basic

/-! # The module reconstruction comparison in the original sheaf category

The whole coefficient functors remain abstract while the inherited
quasicoherent and scalar category structures are fixed.  This preserves
the exact original comparison when affine geometric functors are supplied.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower.FunctorTotal

variable (R k : Type) [CommRing R] [Field k] (X : Scheme.{0})
  [HasFiniteBiproducts (QCoh X)]
  (Φ : ModuleCat.{0} R ⥤ CochainComplex (QCoh X) ℕ) [Φ.Additive]
  (H : ModuleCat.{0} R ⥤ QCoh X) [H.Additive]
  (n : ℕ) (τ : Φ ⟶ singleCoefficient H n)
  {I : Type*} (detectors : I → QCoh X ⥤ ModuleCat.{0} k)
  [∀ i, (detectors i).Additive]
  [∀ i, PreservesFiniteLimits (detectors i)]
  [∀ i, PreservesFiniteColimits (detectors i)]
  (detect : ∀ M : QCoh X, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
  (exactΦ : ∀ S : ShortComplex (ModuleCat.{0} R), S.ShortExact → (S.map Φ).ShortExact)
  (exactH : ∀ S : ShortComplex (ModuleCat.{0} R), S.ShortExact → (S.map H).ShortExact)
  (preservesΦ : ∀ (i : I) (J : Type),
    PreservesColimit (Discrete.functor (fun _ : J => ModuleCat.of R R))
      (Φ ⋙ (detectors i).mapHomologicalComplex (.up ℕ)))
  (preservesH : ∀ (i : I) (J : Type),
    PreservesColimit (Discrete.functor (fun _ : J => ModuleCat.of R R)) (H ⋙ detectors i))
  (above : ∀ (M : ModuleCat.{0} R) (q : ℕ), n < q → IsZero ((Φ.obj M).X q))
  (rankOne : QuasiIso (τ.app (ModuleCat.of R R)))

include detect exactΦ exactH preservesΦ preservesH above rankOne in
/-- The actual unbounded module comparison in the inherited
quasicoherent category, before affine sheaf functors are substituted. -/
theorem reconstructionQuasicoherentModule_topComparison_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (ModuleCat.{0} R) ℤ) :
    QuasiIso ((topComparison Φ H n width retained τ).app K) :=
  reconstructionModule_topComparison_quasiIso R k Φ H n τ detectors detect
    exactΦ exactH preservesΦ preservesH above rankOne width retained K

end ToricPower.FunctorTotal

end

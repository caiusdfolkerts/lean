module

public import ToricPower.NegativeFunctorTotalExact

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z t

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive] (width : ℕ)
  {k : Type} [CommRing k]

variable [∀ q : ℕ, PreservesFiniteLimits (degree Φ q)]
  [∀ q : ℕ, PreservesFiniteColimits (degree Φ q)]

/-- The exact-detector theorem stated directly for the explicit total map.
This interface avoids unfolding a geometric coefficient functor when
specializing the generic total-functor theorem. -/
theorem map_quasiIso_of_exact_detector_family
    {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
    [∀ i, (detectors i).Additive]
    [∀ i, PreservesFiniteLimits (detectors i)]
    [∀ i, PreservesFiniteColimits (detectors i)]
    (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (map Φ width f) :=
  map_quasiIso_of_exact_detectors Φ width detectors detect f

end ToricPower.NegativeFunctorTotal
end

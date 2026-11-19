module

public import ToricPower.NegativeFunctorTotalMapExact
public import ToricPower.AffineSectionsDetection

/-!
# Exact finite dual totals on a scheme with an affine open cover

This scheme-level interface assembles the exact affine section detectors
before any particular geometric coefficient functor is substituted.
The input and output maps are the original maps of arbitrary unbounded
complexes of quasicoherent sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme.{0}) [X.Over (Spec (.of k))]
  [HasFiniteBiproducts (QCoh X)]
  (Φ : QCoh X ⥤ ChainComplex (QCoh X) ℕ) [Φ.Additive]
  [∀ q : ℕ, PreservesFiniteLimits (NegativeFunctorTotal.degree Φ q)]
  [∀ q : ℕ, PreservesFiniteColimits (NegativeFunctorTotal.degree Φ q)]

include k in
/-- Exact affine sections detect quasi-isomorphisms of the literal finite
negative total, with no boundedness requirement on its input. -/
theorem quasicoherent_negativeTotal_map_quasiIso
    {I : Type*} (U : I → X.Opens) (covering : TopologicalSpace.IsOpenCover U)
    (affine : ∀ i, IsAffineOpen (U i)) (width : ℕ)
    {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (NegativeFunctorTotal.map Φ width f) := by
  let sections (i : I) := quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X (U i)
  letI (i : I) : PreservesFiniteLimits (sections i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).1
  letI (i : I) : PreservesFiniteColimits (sections i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).2
  apply NegativeFunctorTotal.map_quasiIso_of_exact_detector_family Φ width sections
  intro M zeroSections
  exact quasicoherent_isZero_of_affineSections k X U covering affine M zeroSections

end ToricPower
end

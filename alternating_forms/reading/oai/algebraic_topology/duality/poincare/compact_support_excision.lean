import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
import OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective
import Mathlib.Topology.Category.TopCat.Opens

/-! # Compact Support Excision -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision

noncomputable section

/-!
# Rational cochain excision around compact supports

The maps below are the actual pullbacks of relative singular cochains along
inclusions of pairs. Compact supports in an open subspace are mapped to their
actual compact images in the ambient space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Additive rational duality carries every actual integral-chain
quasi-isomorphism to a cochain quasi-isomorphism. -/
theorem rationalChainDualMap_quasiIso
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) [QuasiIso f] :
    QuasiIso
      (((preadditiveYoneda.obj
          ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ))).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)).map f.op)) := by
  let : Injective ((ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ)) :=
    Cohomology.Singular.IntegralCoefficientInjective.injective_restrictScalars_rat
  infer_instance

/-- The native relative rational cochain pullback is a quasi-isomorphism
whenever the native integral relative chain map is a quasi-isomorphism. -/
theorem relativeRationalCochainsMap_quasiIso_of_integral
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) [QuasiIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h)] :
    QuasiIso (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) := by
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let g := RelativeCochainDual.rationalCochainsForget.map
    (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h)
  have : QuasiIso (RelativeCochainDual.rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h)) :=
    rationalChainDualMap_quasiIso _
  have : QuasiIso (g ≫ (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom) := by
    change QuasiIso (RelativeCochainDual.rationalCochainsForget.map
      (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) ≫
        (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom)
    rw [RelativeCochainDual.relativeCochainIntegralDualIso_naturality]
    infer_instance
  have : QuasiIso g := quasiIso_of_comp_right g (RelativeCochainDual.relativeCochainIntegralDualIso X A).hom
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) F).mp this

/-- Pullback along the actual pair inclusion `(U,U \ K) → (X,X \ K)`. -/
def compactSupportExcisionCochainMap (X : TopCat.{0}) (U K : Set X) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X Kᶜ ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- The fixed-support comparison restricts the underlying ordinary cochain. -/
@[reassoc (attr := simp)]
theorem compactSupportExcisionCochainMap_inclusion (X : TopCat.{0}) (U K : Set X) :
    compactSupportExcisionCochainMap X U K ≫
        Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' Kᶜ) =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X Kᶜ ≫
        Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ)
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)


end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision

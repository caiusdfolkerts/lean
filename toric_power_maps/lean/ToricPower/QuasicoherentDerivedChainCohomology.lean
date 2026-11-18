module

public import ToricPower.QuasicoherentDerivedCech
public import ToricPower.MappedChainAugmentationInteger

/-!
# Genuine derived cohomology from a full scalar chart-chain augmentation

The supplied map is between the original chart-section chain diagrams.
Canonical extension and single-complex comparisons feed it into the
checked full Čech calculation of actual right-derived global sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower

variable (k : Type) [Field k] (X : Scheme.{0}) [X.Over (Spec (.of k))]
  [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]
  {B : Type} [SemilatticeInf B] [Finite B] (opens : B ⥤ X.Opens)
  (chartsInf : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)
  (cover : iSup opens.obj = ⊤)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (FiniteCech.tupleMeet t))
  (affine : ∀ b, IsAffineOpen (opens.obj b))
  [HasDerivedCategory.{1} (QCoh X)]
  [HasDerivedCategory.{1} (Bᵒᵖ ⥤ ModuleCat.{0} k)]
  [HasDerivedCategory.{1} (ModuleCat.{0} k)]

local notation "S" => FiniteCech.quasicoherentMeetSections k X opens
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤

/-- The full chart augmentation computes the ordinary cohomology of its
actual sheaf target, with no global module-sheaf augmentation hypothesis. -/
def quasicoherentDerivedSectionsCohomologyOfChainAugmentation
    (K : ChainComplex (QCoh X) ℕ) (C : CochainComplex.Plus (QCoh X))
    (sourceIso : C.obj ≅ K.extend ComplexShape.embeddingDownNat) (T : QCoh X)
    (augmentation : ((FiniteCech.quasicoherentMeetSections k X opens).mapHomologicalComplex
      (.down ℕ)).obj K ⟶
        (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{0} k)).obj
          ((FiniteCech.quasicoherentMeetSections k X opens).obj T))
    [QuasiIso augmentation] (degree : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) (degree : ℤ)).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj C)) ≃+
    TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology T.obj degree := by
  exact quasicoherentDerivedSectionsSingleCohomologyOfChartQuasiIso
    k X opens chartsInf cover meetEq affine C T
    (integerMappedChainAugmentationOfModel
      (FiniteCech.quasicoherentMeetSections k X opens) K T augmentation C.obj sourceIso) degree

include chartsInf cover meetEq affine in
/-- A nonzero ordinary cohomology class gives a nonzero class of the
original bounded-below dual model in exactly the same degree. -/
theorem quasicoherentDerivedSectionsCohomologyOfChainAugmentation_nonzero
    (K : ChainComplex (QCoh X) ℕ) (C : CochainComplex.Plus (QCoh X))
    (sourceIso : C.obj ≅ K.extend ComplexShape.embeddingDownNat) (T : QCoh X)
    (augmentation : ((FiniteCech.quasicoherentMeetSections k X opens).mapHomologicalComplex
      (.down ℕ)).obj K ⟶
        (ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{0} k)).obj
          ((FiniteCech.quasicoherentMeetSections k X opens).obj T))
    [QuasiIso augmentation] (degree : ℕ)
    (nonzero : Nontrivial (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology T.obj degree)) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} k) (degree : ℤ)).obj
      ((Γ).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj C))) := by
  intro zero
  have trivial := (quasicoherentDerivedSectionsCohomologyOfChainAugmentation
    k X opens chartsInf cover meetEq affine K C sourceIso T augmentation degree).toEquiv.subsingleton_congr.mp
      (ModuleCat.isZero_iff_subsingleton.mp zero)
  exact (not_subsingleton_iff_nontrivial.mpr nonzero) trivial

end ToricPower
end

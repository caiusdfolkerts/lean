module

public import ToricPower.CechSingular.IncidenceHomologyComparison

@[expose] public noncomputable section

open ToricPower.CechIncidenceChains ToricPower.CechAcyclicCarrier
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative

/-! ## Exact generic source: AcyclicCarrierAssembly -/
section Source_AcyclicCarrierAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ConvexNerveIncidenceHomologyComparison
open ToricPower.NegativeSupportCech
open ToricPower.NegativeSupportRelative
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveAcyclicCarrierAssembly

section ActualFaceCarriers

variable {Ray : Type*} {Chart : Type}
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

theorem faceCarrierChainInclusion_mono (face : Finset Chart) (degree : ℕ) :
    Mono ((faceCarrierChainInclusion incidence negative face).f degree) := by
  let inclusion := faceCarrierSimplicialInclusion incidence negative face
  have componentMono (simplex : SimplexCategoryᵒᵖ) : Mono (inclusion.app simplex) := by
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro first second equality
    apply Subtype.ext
    have same := congrArg Subtype.val equality
    change first.val = second.val at same
    exact same
  let : Mono inclusion := NatTrans.mono_of_mono_app inclusion
  exact inferInstanceAs (Mono ((SSet.chainComplexMap (SSetPair.of inclusion).hom
    (AddCommGrpCat.of ℤ)).f degree))

theorem faceCarrierChainInclusion_augmentation (face : Finset Chart) :
    (faceCarrierChainInclusion incidence negative face).f 0 ≫ incidenceChainAugmentation incidence negative =
      incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face) := by
  apply SSet.chainComplex_hom_ext
  intro tuple
  change incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) 0 tuple ≫
    ((faceCarrierChainInclusion incidence negative face).f 0 ≫ incidenceChainAugmentation incidence negative) =
    incidenceChainInclusion incidence (faceCarrierNegative incidence negative face) 0 tuple ≫
      incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face)
  rw [← Category.assoc, faceCarrierChainInclusion_generator,
    incidenceChainAugmentation_generator, incidenceChainAugmentation_generator]

theorem faceCarrierChains_augmentedExact (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) :
    (ShortComplex.mk
      ((incidenceChains incidence (faceCarrierNegative incidence negative face)).d 1 0)
      (incidenceChainAugmentation incidence (faceCarrierNegative incidence negative face))
      (incidenceChainAugmentation_zero incidence (faceCarrierNegative incidence negative face))).Exact := by
  obtain ⟨anchor, onFace⟩ := present.1
  exact incidenceConeChains_augmentedExact incidence (faceCarrierNegative incidence negative face) anchor
    (faceCarrier_isCone incidence negative face present anchor onFace)

theorem faceCarrierChains_exactAt_positive (face : Finset Chart)
    (present : face ∈ negativeChartComplex incidence negative) (degree : ℕ) :
    (incidenceChains incidence (faceCarrierNegative incidence negative face)).ExactAt (degree + 1) := by
  obtain ⟨anchor, onFace⟩ := present.1
  exact incidenceConeChains_exactAt_positive incidence (faceCarrierNegative incidence negative face) anchor
    (faceCarrier_isCone incidence negative face present anchor onFace) degree

noncomputable def reverseFaceCarrier
    (simplicial : SSet.{0})
    (shape : ∀ degree, simplicial _⦋degree⦌ → Finset Chart)
    (shape_face : ∀ degree deleted simplex,
      shape (degree + 1) simplex ⊆ shape degree
        (simplicial.δ deleted simplex))
    (shape_present : ∀ degree simplex, shape degree simplex ∈ negativeChartComplex incidence negative) :
    IntegralAcyclicCarrier simplicial
      (incidenceChains incidence negative) (incidenceChainAugmentation incidence negative) where
  complex degree simplex := incidenceChains incidence
    (faceCarrierNegative incidence negative (shape degree simplex))
  inclusion degree simplex := faceCarrierChainInclusion incidence negative (shape degree simplex)
  inclusion_mono degree simplex component :=
    faceCarrierChainInclusion_mono incidence negative (shape degree simplex) component
  faceMap degree deleted simplex := faceCarrierChainRefinement incidence negative
    (shape (degree + 1) simplex) (shape degree (simplicial.δ deleted simplex))
    (shape_face degree deleted simplex)
  faceMap_inclusion degree deleted simplex :=
    faceCarrierChainRefinement_inclusion incidence negative _ _ (shape_face degree deleted simplex)
  augmentation_zero degree simplex := by
    rw [faceCarrierChainInclusion_augmentation, incidenceChainAugmentation_zero]
  exact_zero degree simplex := by
    simpa only [faceCarrierChainInclusion_augmentation] using
      faceCarrierChains_augmentedExact incidence negative (shape degree simplex) (shape_present degree simplex)
  exact_positive degree simplex component :=
    faceCarrierChains_exactAt_positive incidence negative (shape degree simplex) (shape_present degree simplex) component

end ActualFaceCarriers

end BondalThomsen.ConvexNerveAcyclicCarrierAssembly

end Source_AcyclicCarrierAssembly

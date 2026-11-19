module

public import ToricPower.CechSingularComparison
public import ToricPower.CechCanonicalAugmentation

/-!
# Reduced cohomology of the actual geometric realization

The target cochains are Hom of the ordinary integral singular chains into
the coefficient group. The augmentation is dual to the ordinary integral
singular augmentation. Thus degree minus one, degree zero and all higher
degrees retain their usual augmented meanings, also for an empty space.

Both augmentation identities of the concrete incidence–singular equivalence
are proved from its actual affine map and its actual inverse homotopy.
Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open ToricPower.CechIncidenceChains ToricPower.CechCanonicalAugmentation
open ToricPower.NegativeSupportRelative ToricPower.CechSingularComparison
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence
open scoped Classical

namespace ToricPower.CechReducedSingular

/-- Chain-homotopic maps have the same actual degree-zero augmentation. -/
theorem homotopicMaps_augmentation {source target : ChainComplex AddCommGrpCat ℕ}
    {first second : source ⟶ target} (homotopy : Homotopy first second)
    {coefficient : AddCommGrpCat} (augmentation : target.X 0 ⟶ coefficient)
    (closed : target.d 1 0 ≫ augmentation = 0) :
    first.f 0 ≫ augmentation = second.f 0 ≫ augmentation := by
  have identity := congrArg (fun mapping => mapping ≫ augmentation) (homotopy.comm 0)
  simpa only [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex,
    zero_add, add_zero, add_comp, Category.assoc, closed, comp_zero] using identity

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

@[reassoc]
theorem incidenceSingularChainHomotopyEquiv_hom_augmentation :
    (incidenceSingularChainHomotopyEquiv incidence negative).hom.f 0 ≫
      singularChainAugmentation (incidenceRealization incidence negative) =
        incidenceChainAugmentation incidence negative :=
  affineSingularChainMap_augmentation incidence negative

@[reassoc]
theorem incidenceSingularChainHomotopyEquiv_inv_augmentation :
    (incidenceSingularChainHomotopyEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation incidence negative =
        singularChainAugmentation (incidenceRealization incidence negative) := by
  have identity := homotopicMaps_augmentation
    (incidenceSingularChainHomotopyEquiv incidence negative).homotopyInvHomId
    (singularChainAugmentation (incidenceRealization incidence negative))
    (singularChainAugmentation_zero (incidenceRealization incidence negative))
  simpa only [HomologicalComplex.comp_f, Category.assoc,
    incidenceSingularChainHomotopyEquiv_hom_augmentation,
    HomologicalComplex.id_f, Category.id_comp] using identity

section AugmentedDual

variable (𝕜 : Type) [Field 𝕜]

/-- The ordinary coefficient identification Hom(ℤ,k), using the actual
coproduct presentation of the integral augmentation object. -/
def augmentationScalarMap : AddCommGrpCat.of 𝕜 ⟶
    (scalarCoefficientDual 𝕜).obj (Opposite.op incidenceAugmentationObject) :=
  AddCommGrpCat.ofHom
    { toFun := augmentationScalar 𝕜
      map_zero' := by
        apply Sigma.hom_ext
        intro point
        rw [augmentationScalar, Sigma.ι_comp_desc, comp_zero]
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro integer
        change integer • (0 : 𝕜) = 0
        exact zsmul_zero integer
      map_add' := by
        intro first second
        apply Sigma.hom_ext
        intro point
        rw [augmentationScalar, Sigma.ι_comp_desc, comp_add]
        rw [augmentationScalar, Sigma.ι_comp_desc, augmentationScalar, Sigma.ι_comp_desc]
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro integer
        change integer • (first + second) = integer • first + integer • second
        exact zsmul_add first second integer }

/-- The actual dual of an integral augmentation; every coefficient is a
constant cochain. -/
def augmentedDualConstant (chains : ChainComplex AddCommGrpCat ℕ)
    (augmentation : chains.X 0 ⟶ incidenceAugmentationObject) :
    AddCommGrpCat.of 𝕜 ⟶ (dualChainComplex 𝕜 chains).X 0 :=
  augmentationScalarMap 𝕜 ≫ (scalarCoefficientDual 𝕜).map augmentation.op

theorem augmentedDualConstant_apply (chains : ChainComplex AddCommGrpCat ℕ)
    (augmentation : chains.X 0 ⟶ incidenceAugmentationObject) (scalar : 𝕜) :
    augmentedDualConstant 𝕜 chains augmentation scalar =
      augmentation ≫ augmentationScalar 𝕜 scalar := rfl

theorem augmentedDualConstant_d (chains : ChainComplex AddCommGrpCat ℕ)
    (augmentation : chains.X 0 ⟶ incidenceAugmentationObject)
    (closed : chains.d 1 0 ≫ augmentation = 0) :
    augmentedDualConstant 𝕜 chains augmentation ≫ (dualChainComplex 𝕜 chains).d 0 1 = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  change chains.d 1 0 ≫ augmentation ≫ augmentationScalar 𝕜 scalar = 0
  rw [← Category.assoc, closed, zero_comp]

/-- Functoriality of actual constant cochains under an augmented chain map. -/
theorem augmentedDualConstant_naturality {source target : ChainComplex AddCommGrpCat ℕ}
    (sourceAugmentation : source.X 0 ⟶ incidenceAugmentationObject)
    (targetAugmentation : target.X 0 ⟶ incidenceAugmentationObject)
    (mapping : source ⟶ target)
    (augmented : mapping.f 0 ≫ targetAugmentation = sourceAugmentation) :
    augmentedDualConstant 𝕜 target targetAugmentation ≫ (dualChainMap 𝕜 mapping).f 0 =
      augmentedDualConstant 𝕜 source sourceAugmentation := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  change mapping.f 0 ≫ targetAugmentation ≫ augmentationScalar 𝕜 scalar =
    sourceAugmentation ≫ augmentationScalar 𝕜 scalar
  rw [← Category.assoc, augmented]

/-- The integral-dual constant is exactly the literal constant tuple
cochain under the genuine incidence comparison. -/
theorem incidence_augmentedDualConstant :
    augmentedDualConstant 𝕜 (incidenceChains incidence negative)
      (incidenceChainAugmentation incidence negative) ≫
        (incidenceDualIso 𝕜 incidence negative).hom.f 0 =
      negativeConstantCochain 𝕜 incidence negative := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro scalar
  change incidenceDualEvaluation 𝕜 incidence negative 0
    (incidenceChainAugmentation incidence negative ≫ augmentationScalar 𝕜 scalar) =
      (fun _tuple => scalar)
  rw [← incidenceDualExtension_constant, incidenceDualEvaluation_extension]

end AugmentedDual

section ReducedCohomology

variable (𝕜 : Type) [Field 𝕜]

/-- The cycle class of a specified actual constant cochain. -/
def cochainConstantAugmentation (cochains : CochainComplex AddCommGrpCat ℕ)
    (constant : AddCommGrpCat.of 𝕜 ⟶ cochains.X 0)
    (closed : constant ≫ cochains.d 0 1 = 0) : AddCommGrpCat.of 𝕜 ⟶ cochains.homology 0 :=
  cochains.liftCycles constant 1 (by simp) closed ≫ cochains.homologyπ 0

theorem cochainConstantAugmentation_naturality
    {source target : CochainComplex AddCommGrpCat ℕ}
    (sourceConstant : AddCommGrpCat.of 𝕜 ⟶ source.X 0)
    (targetConstant : AddCommGrpCat.of 𝕜 ⟶ target.X 0)
    (sourceClosed : sourceConstant ≫ source.d 0 1 = 0)
    (targetClosed : targetConstant ≫ target.d 0 1 = 0)
    (mapping : source ⟶ target) (constant : sourceConstant ≫ mapping.f 0 = targetConstant) :
    cochainConstantAugmentation 𝕜 source sourceConstant sourceClosed ≫
      HomologicalComplex.homologyMap mapping 0 =
        cochainConstantAugmentation 𝕜 target targetConstant targetClosed := by
  have cycles : source.liftCycles sourceConstant 1 (by simp) sourceClosed ≫
      HomologicalComplex.cyclesMap mapping 0 =
        target.liftCycles targetConstant 1 (by simp) targetClosed := by
    apply (cancel_mono (target.iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    exact constant
  unfold cochainConstantAugmentation
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, cycles]

/-- The actual constant singular cochain augmentation. -/
def singularConstantAugmentation (Space : Type) [TopologicalSpace Space] :
    AddCommGrpCat.of 𝕜 ⟶ (dualChainComplex 𝕜 (integralSingularChains Space)).homology 0 :=
  cochainConstantAugmentation 𝕜 (dualChainComplex 𝕜 (integralSingularChains Space))
    (augmentedDualConstant 𝕜 (integralSingularChains Space) (singularChainAugmentation Space))
    (augmentedDualConstant_d 𝕜 (integralSingularChains Space)
      (singularChainAugmentation Space) (singularChainAugmentation_zero Space))

/-- Ordinary reduced singular cohomology with coefficient group k,
indexed by `p` for degree `p-1`. The cochains are literally Hom of standard
integral singular chains into k, and the augmentation is the standard one. -/
def reducedSingularCohomology (Space : Type) [TopologicalSpace Space] : ℕ → AddCommGrpCat
  | 0 => kernel (singularConstantAugmentation 𝕜 Space)
  | 1 => cokernel (singularConstantAugmentation 𝕜 Space)
  | degree + 2 => (dualChainComplex 𝕜 (integralSingularChains Space)).homology (degree + 1)

/-- The actual singular comparison dualized and transported from the
actual incidence cochains. -/
def incidenceSingularCochainHomotopyEquiv :
    HomotopyEquiv (negativeComplex 𝕜 incidence negative)
      (dualChainComplex 𝕜 (integralSingularChains (incidenceRealization incidence negative))) :=
  (HomotopyEquiv.ofIso (incidenceDualIso 𝕜 incidence negative).symm).trans
    (dualChainHomotopyEquiv 𝕜 (incidenceSingularChainHomotopyEquiv incidence negative))

theorem incidenceSingularCochainHomotopyEquiv_constant :
    negativeConstantCochain 𝕜 incidence negative ≫
      (incidenceSingularCochainHomotopyEquiv incidence negative 𝕜).hom.f 0 =
        augmentedDualConstant 𝕜 (integralSingularChains (incidenceRealization incidence negative))
          (singularChainAugmentation (incidenceRealization incidence negative)) := by
  have constantInverse : negativeConstantCochain 𝕜 incidence negative ≫
      (incidenceDualIso 𝕜 incidence negative).inv.f 0 =
        augmentedDualConstant 𝕜 (incidenceChains incidence negative)
          (incidenceChainAugmentation incidence negative) := by
    rw [← incidence_augmentedDualConstant, Category.assoc,
      ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id]
  change negativeConstantCochain 𝕜 incidence negative ≫
    ((incidenceDualIso 𝕜 incidence negative).inv.f 0 ≫
      (dualChainMap 𝕜 (incidenceSingularChainHomotopyEquiv incidence negative).inv).f 0) = _
  rw [← Category.assoc, constantInverse]
  exact augmentedDualConstant_naturality 𝕜
    (singularChainAugmentation (incidenceRealization incidence negative))
    (incidenceChainAugmentation incidence negative)
    (incidenceSingularChainHomotopyEquiv incidence negative).inv
    (incidenceSingularChainHomotopyEquiv_inv_augmentation incidence negative)

theorem incidenceSingularCochainHomotopyEquiv_augmentation :
    canonicalNegativeAugmentation 𝕜 incidence negative ≫
      ((incidenceSingularCochainHomotopyEquiv incidence negative 𝕜).toHomologyIso 0).hom =
        singularConstantAugmentation 𝕜 (incidenceRealization incidence negative) :=
  cochainConstantAugmentation_naturality 𝕜
    (negativeConstantCochain 𝕜 incidence negative)
    (augmentedDualConstant 𝕜 (integralSingularChains (incidenceRealization incidence negative))
      (singularChainAugmentation (incidenceRealization incidence negative)))
    (negativeConstantCochain_d 𝕜 incidence negative)
    (augmentedDualConstant_d 𝕜 (integralSingularChains (incidenceRealization incidence negative))
      (singularChainAugmentation (incidenceRealization incidence negative))
      (singularChainAugmentation_zero (incidenceRealization incidence negative)))
    (incidenceSingularCochainHomotopyEquiv incidence negative 𝕜).hom
    (incidenceSingularCochainHomotopyEquiv_constant incidence negative 𝕜)

/-- Every reduced degree of the actual incidence tuple cochains agrees
with the ordinary reduced singular cohomology of its geometric realization.
The proof contains both homotopies and the actual augmentation square. -/
def incidenceReducedSingularIso (degree : ℕ) :
    canonicalNegativeReducedShifted 𝕜 incidence negative degree ≅
      reducedSingularCohomology 𝕜 (incidenceRealization incidence negative) degree := by
  let equivalences := (incidenceSingularCochainHomotopyEquiv incidence negative 𝕜).toHomologyIso
  rcases degree with _ | (_ | degree)
  · exact kernel.mapIso _ _ (Iso.refl _) (equivalences 0)
      (by simpa only [Iso.refl_hom, Category.id_comp] using
        incidenceSingularCochainHomotopyEquiv_augmentation incidence negative 𝕜)
  · exact cokernel.mapIso _ _ (Iso.refl _) (equivalences 0)
      (by simpa only [Iso.refl_hom, Category.id_comp] using
        incidenceSingularCochainHomotopyEquiv_augmentation incidence negative 𝕜)
  · exact equivalences (degree + 1)

end ReducedCohomology

end ToricPower.CechReducedSingular

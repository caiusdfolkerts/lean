module

public import ToricPower.CechReducedSingular

/-!
# Vanishing for contractible incidence realizations

The contraction hypothesis concerns the actual topological realization.
It induces an augmentation-preserving integral chain homotopy equivalence,
so every ordinary reduced singular cohomology group vanishes, including
the augmented degrees minus one and zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative
open ToricPower.CechIncidenceChains ToricPower.CechCanonicalAugmentation
open ToricPower.CechReducedSingular ToricPower.CechSingularComparison
open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceSingularChainEquivalence

namespace ToricPower.CechContractibleVanishing

attribute [local instance] Classical.decEq

/-- The one-point incidence relation. -/
def pointIncidence (_ray _chart : Unit) : Prop := True

theorem pointIncidence_isCone :
    @PreAbstractSimplicialComplex.IsCone Unit (Classical.decEq Unit)
      (negativeChartComplex pointIncidence (fun _ => True)) () := by
  letI : DecidableEq Unit := Classical.decEq Unit
  exact {
    apex_mem := ⟨Finset.singleton_nonempty _, (), trivial, fun _ _ => trivial⟩
    insert_mem := fun _ _ => ⟨Finset.insert_nonempty _ _, (), trivial, fun _ _ => trivial⟩ }

/-- The one-point augmented integral incidence contraction. -/
def pointIncidenceAugmentationEquiv :
    HomotopyEquiv (incidenceChains pointIncidence (fun _ => True))
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  incidenceConeChainHomotopyEquiv pointIncidence (fun _ => True) () pointIncidence_isCone

theorem pointIncidenceAugmentationEquiv_hom :
    pointIncidenceAugmentationEquiv.hom.f 0 =
      incidenceChainAugmentation pointIncidence (fun _ => True) := rfl

variable {Ray : Type*} {Chart : Type} [Finite Chart]
variable (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
variable [ContractibleSpace (incidenceRealization incidence negative)]

/-- The literal incidence augmentation is a chain homotopy equivalence
when the actual realization is contractible. -/
def contractibleIncidenceAugmentationEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      ((ChainComplex.single₀ AddCommGrpCat.{0}).obj incidenceAugmentationObject) :=
  (incidenceSingularChainHomotopyEquiv incidence negative).trans
    (contractibleSingularChainAugmentationHomotopyEquiv
      (incidenceRealization incidence negative))

theorem contractibleIncidenceAugmentationEquiv_hom :
    (contractibleIncidenceAugmentationEquiv incidence negative).hom.f 0 =
      incidenceChainAugmentation incidence negative := by
  change (incidenceSingularChainHomotopyEquiv incidence negative).hom.f 0 ≫
    (contractibleSingularChainAugmentationHomotopyEquiv
      (incidenceRealization incidence negative)).hom.f 0 = _
  rw [contractibleSingularChainAugmentationHomotopyEquiv_hom]
  exact incidenceSingularChainHomotopyEquiv_hom_augmentation incidence negative

theorem contractibleIncidenceAugmentationEquiv_inv :
    (contractibleIncidenceAugmentationEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation incidence negative = 𝟙 incidenceAugmentationObject := by
  have identity := homotopicMaps_augmentation
    (contractibleIncidenceAugmentationEquiv incidence negative).homotopyInvHomId
    (𝟙 incidenceAugmentationObject) (by simp)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at identity
  rw [contractibleIncidenceAugmentationEquiv_hom] at identity
  change (((contractibleIncidenceAugmentationEquiv incidence negative).inv.f 0 :
      incidenceAugmentationObject ⟶ (incidenceChains incidence negative).X 0) ≫
      incidenceChainAugmentation incidence negative) ≫ 𝟙 incidenceAugmentationObject =
        𝟙 incidenceAugmentationObject ≫ 𝟙 incidenceAugmentationObject at identity
  simpa only [Category.comp_id] using identity

/-- Comparison with the point preserves the genuine augmentation in the
contravariant direction needed for coefficient cochains. -/
def contractibleIncidencePointEquiv :
    HomotopyEquiv (incidenceChains incidence negative)
      (incidenceChains pointIncidence (fun _ => True)) :=
  (contractibleIncidenceAugmentationEquiv incidence negative).trans
    pointIncidenceAugmentationEquiv.symm

theorem contractibleIncidencePointEquiv_inv_augmentation :
    (contractibleIncidencePointEquiv incidence negative).inv.f 0 ≫
      incidenceChainAugmentation incidence negative =
        incidenceChainAugmentation pointIncidence (fun _ => True) := by
  change (pointIncidenceAugmentationEquiv.hom.f 0 ≫
    (contractibleIncidenceAugmentationEquiv incidence negative).inv.f 0) ≫ _ = _
  rw [Category.assoc, contractibleIncidenceAugmentationEquiv_inv]
  change (pointIncidenceAugmentationEquiv.hom.f 0 :
    (incidenceChains pointIncidence (fun _ => True)).X 0 ⟶ incidenceAugmentationObject) ≫
      𝟙 incidenceAugmentationObject = _
  exact (Category.comp_id _).trans pointIncidenceAugmentationEquiv_hom

variable (𝕜 : Type) [Field 𝕜]

theorem pointRelativeDegree_isZero (degree : ℕ) :
    IsZero (relativeDegree 𝕜 pointIncidence (fun _ => True) degree) := by
  letI : Subsingleton (relativeDegree 𝕜 pointIncidence (fun _ => True) degree) := by
    refine ⟨fun first second => ?_⟩
    apply relativeDegreeInclusion_injective 𝕜 pointIncidence (fun _ => True) degree
    funext tuple
    rw [relativeDegreeInclusion_apply, relativeDegreeInclusion_apply]
    have forbidden : tupleForbidden pointIncidence (fun _ => True) degree tuple :=
      ⟨(), trivial, fun _ => trivial⟩
    exact ((Pi.π (relativeCoefficient 𝕜 pointIncidence (fun _ => True) degree) tuple first).property forbidden).trans
      ((Pi.π (relativeCoefficient 𝕜 pointIncidence (fun _ => True) degree) tuple second).property forbidden).symm
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem pointReduced_isZero (degree : ℕ) :
    IsZero (canonicalNegativeReducedShifted 𝕜 pointIncidence (fun _ => True) degree) := by
  have vanishes := (HomologicalComplex.ExactAt.of_isZero
    (show IsZero ((relativeComplex 𝕜 pointIncidence (fun _ => True)).X degree) from
      pointRelativeDegree_isZero 𝕜 degree)).isZero_homology
  exact vanishes.of_iso
    (relativeHomologyCanonicalReducedIso 𝕜 pointIncidence (fun _ => True) () degree).symm

/-- Every reduced singular cohomology group of the actual contractible
incidence realization is zero. The natural index `degree` means degree
`degree - 1`, so the statement includes the two augmentation groups. -/
theorem reducedSingularCohomology_isZero (degree : ℕ) :
    IsZero (reducedSingularCohomology 𝕜 (incidenceRealization incidence negative) degree) := by
  have sourceZero := (pointReduced_isZero 𝕜 degree).of_iso
    (canonicalReducedIsoOfAugmentedChainHomotopyEquiv 𝕜 incidence negative
      pointIncidence (fun _ => True) (contractibleIncidencePointEquiv incidence negative)
      (contractibleIncidencePointEquiv_inv_augmentation incidence negative) degree)
  exact sourceZero.of_iso (incidenceReducedSingularIso incidence negative 𝕜 degree).symm

theorem reducedSingularCohomology_subsingleton (degree : ℕ) :
    Subsingleton (reducedSingularCohomology 𝕜
      (incidenceRealization incidence negative) degree) :=
  AddCommGrpCat.subsingleton_of_isZero
    (reducedSingularCohomology_isZero incidence negative 𝕜 degree)

end ToricPower.CechContractibleVanishing

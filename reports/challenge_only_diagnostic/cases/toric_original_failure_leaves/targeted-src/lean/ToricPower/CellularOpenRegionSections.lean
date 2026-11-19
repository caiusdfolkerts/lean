module

public import ToricPower.CellularConstantSections
public import ToricPower.CellularConstantSectionWitness
public import ToricPower.CellularReindexSections
public import ToricPower.CellularOpenClosedCoefficients
public import ToricPower.ProjectiveSectionKernel

/-! # Actual sections of an open coefficient region from its two nerves

The retained cut is upward closed and the closed complement is downward
closed. The two orders are interchanged only by the explicit subtype
order isomorphism. Contractibility refers throughout to the actual
incidence realizations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open BondalThomsen.ConvexNerveReducedCochainAcyclicity

namespace ToricPower.Cellular

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B] [Finite B]
  (P Q : B → Prop) (upward : Monotone P) (downward : Antitone Q)

abbrev closedPredicateOnCut : {b : B // P b} → Prop := fun b => Q b.val

include downward in
theorem closedPredicateOnCut_downward : Antitone (closedPredicateOnCut P Q) :=
  fun _ _ h => downward h

local instance : HasDerivedCategory.{1} ({b : B // P b} ⥤ ModuleCat k) :=
  HasDerivedCategory.standard _

theorem closedCutProjectiveSection_quasiIso_of_resolution
    (resolution : ProjectiveResolution (constantDiagram k {b : B // P b}))
    (J : InjectiveResolution (constantDiagram k {b : {b : B // Q b} // P b.val}))
    [QuasiIso (mappedSingleAugmentation
      (constantSections k {b : {b : B // Q b} // P b.val})
      (constantScalarMap k {b : {b : B // Q b} // P b.val}) J.ι)] :
    QuasiIso (scalarProjectiveSectionMap k resolution
      (closedScalarMap k (closedPredicateOnCut P Q)
        (closedPredicateOnCut_downward P Q downward))) := by
  let e := retainedIntersectionOrderIso P Q
  let J' := reindexedConstantResolution k e J
  have : QuasiIso (mappedSingleAugmentation
      (constantSections k {b : {b : B // P b} // Q b.val})
      (constantScalarMap k {b : {b : B // P b} // Q b.val}) J'.ι) :=
    reindexedConstantSections_quasiIso k e J
  exact closedProjectiveSectionMap_quasiIso_of_resolution k
    (closedPredicateOnCut P Q) (closedPredicateOnCut_downward P Q downward) resolution J'

include upward in
/-- The closed-complement calculation uses its genuine closed face
poset, rather than all faces whose closures meet that complement. -/
theorem closedCutProjectiveSection_quasiIso
    (resolution : ProjectiveResolution (constantDiagram k {b : B // P b}))
    (contractible : ContractibleSpace (incidenceRealization
      (fun b c : {b : B // Q b} => b ≤ c) (fun b => P b.val))) :
    QuasiIso (scalarProjectiveSectionMap k resolution
      (closedScalarMap k (closedPredicateOnCut P Q)
        (closedPredicateOnCut_downward P Q downward))) := by
  let : SemilatticeInf {b : B // Q b} :=
    Subtype.semilatticeInf (fun _ _ hx _ => downward inf_le_left hx)
  have := contractible
  have retained_upward : Monotone (fun b : {b : B // Q b} => P b.val) :=
    fun _ _ h => upward h
  obtain ⟨J,acyclicSections⟩ := FiniteCech.exists_constantSectionResolution k
    (fun b : {b : B // Q b} => P b.val) retained_upward
  have := acyclicSections
  exact closedCutProjectiveSection_quasiIso_of_resolution k P Q downward resolution J

include upward in
/-- Contractibility of the whole cut and its actual closed complement
kills the complete projective section complex of the genuine open
scalar diagram. -/
theorem openCutProjectiveSection_acyclic
    (resolution : ProjectiveResolution (constantDiagram k {b : B // P b}))
    (wholeContractible : ContractibleSpace (incidenceRealization
      (fun b c : B => b ≤ c) P))
    (closedContractible : ContractibleSpace (incidenceRealization
      (fun b c : {b : B // Q b} => b ≤ c) (fun b => P b.val))) :
    ((projectiveCoefficientComplexFunctor k (𝟭 ({b : B // P b} ⥤ ModuleCat k)) resolution).obj
      ((CochainComplex.singleFunctor ({b : B // P b} ⥤ ModuleCat k) 0).obj
        (openScalarDiagram k (closedPredicateOnCut P Q)
          (closedPredicateOnCut_downward P Q downward)))).Acyclic := by
  letI := wholeContractible
  haveI : QuasiIso (scalarProjectiveSectionMap k resolution
      (constantScalarMap k {b : B // P b})) :=
    FiniteCech.constantProjectiveSectionMap_quasiIso k P upward resolution
  haveI := closedCutProjectiveSection_quasiIso k P Q upward downward resolution closedContractible
  apply projectiveSectionKernel_acyclic k resolution
    (openClosedCoefficientSequence k (closedPredicateOnCut P Q)
      (closedPredicateOnCut_downward P Q downward))
    (openClosedCoefficientSequence_shortExact k (closedPredicateOnCut P Q)
      (closedPredicateOnCut_downward P Q downward))
    (constantScalarMap k {b : B // P b})
    (closedScalarMap k (closedPredicateOnCut P Q) (closedPredicateOnCut_downward P Q downward))
  rfl

end ToricPower.Cellular

end

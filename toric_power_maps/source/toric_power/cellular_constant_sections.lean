module

public import ToricPower.CellularCechAugmentation
public import ToricPower.ProjectiveSectionsFromResolution

/-! # Genuine constant derived sections on a contractible retained face nerve -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B]
  (P : B → Prop) (upward : Monotone P)

local instance : HasDerivedCategory.{1} ({b : B // P b} ⥤ ModuleCat k) :=
  HasDerivedCategory.standard _

variable [Finite B]
  [ContractibleSpace (BondalThomsen.ConvexNerveReducedCochainAcyclicity.incidenceRealization
    (fun b c : B => b ≤ c) P)]

include upward in
/-- Every genuine projective resolution computes the canonical scalar
section map on the full retained diagram. -/
theorem constantProjectiveSectionMap_quasiIso
    (Q : ProjectiveResolution (constantFieldDiagram k P)) :
    QuasiIso (scalarProjectiveSectionMap k Q (retainedScalarSections k P)) := by
  haveI : QuasiIso (mappedSingleAugmentation (retainedSections k P)
      (retainedScalarSections k P) (constantCotupleInjectiveResolution k P upward).ι) :=
    cotupleSectionAugmentation_quasiIso k P upward
  exact scalarProjectiveSectionMap_quasiIso_of_resolution k Q
    (retainedScalarSections k P) (constantCotupleInjectiveResolution k P upward)

end ToricPower.FiniteCech

end

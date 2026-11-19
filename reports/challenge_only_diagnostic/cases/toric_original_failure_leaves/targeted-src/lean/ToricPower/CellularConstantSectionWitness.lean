module

public import ToricPower.CellularConstantSections
public import ToricPower.CellularConstantMap

/-! # An actual acyclic constant-section resolution

The witness is the checked cotuple injective resolution. Keeping its
existence behind a theorem boundary lets later order-reindexing arguments
use the genuine resolution without normalizing its full construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.FiniteCech

variable (k : Type) [Field k] {B : Type} [SemilatticeInf B] [Finite B]
  (P : B → Prop) (upward : Monotone P)
  [ContractibleSpace (BondalThomsen.ConvexNerveReducedCochainAcyclicity.incidenceRealization
    (fun b c : B => b ≤ c) P)]

include upward in
theorem exists_constantSectionResolution :
    ∃ J : InjectiveResolution (Cellular.constantDiagram k {b : B // P b}),
      QuasiIso (mappedSingleAugmentation (Cellular.constantSections k {b : B // P b})
        (Cellular.constantScalarMap k {b : B // P b}) J.ι) := by
  refine ⟨constantCotupleInjectiveResolution k P upward,?_⟩
  exact cotupleSectionAugmentation_quasiIso k P upward

end ToricPower.FiniteCech

end

module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_graph_alignment " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record000_alignment_⟪0⟫ : Interval (alignedCheck record000 SharedSmallCellPool.entry) ⟪1⟫ ⟪2⟫ :=
  interval_of_check _ ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_graph_leaf " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record000_leaf_⟪0⟫ : Interval record000.leafTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check _ ⟪0⟫ ⟪2⟫ (by decide +kernel)"### args

elab "cert_graph_leaf_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record000_leaf_checked_⟪0⟫ :
    RawLeafCertificate.check record000.data.quota (record000_rawLeaves ⟪0⟫)
      (record000_certificates ⟪0⟫) = true := by
  change RawLeafCertificate.check record000.data.quota (record000_rawLeaves ⟪0⟫)
    (.matching Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪2⟫) = true
  exact matching_checked record000.data.quota (record000_rawLeaves ⟪0⟫) Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪2⟫
    Nonrational.InducedTerminalMatches.M⟪1⟫.r⟪2⟫_checked (by decide +kernel)"### args

elab "cert_graph_local " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record000_local_⟪0⟫ : Interval (localCheck record000) ⟪1⟫ ⟪2⟫ :=
  interval_of_check _ ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_graph_nodes " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem record000_nodes_⟪0⟫ (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) ⟪0⟫ ⟪1⟫ :=
  interval_of_check _ ⟪0⟫ ⟪2⟫ (by decide_kernel_context)"### args


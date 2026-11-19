module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_candidates_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidates_checked_⟪0⟫ : FiniteChecks.Interval candidateTest ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check candidateTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_candidates_checked_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidates_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval candidateTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append candidateTest ⟪2⟫ ⟪4⟫ ⟪3⟫ candidates_checked_join_⟪0⟫_⟪5⟫ candidates_checked_join_⟪5⟫_⟪1⟫"### args

elab "cert_candidates_checked_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidates_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval candidateTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append candidateTest ⟪2⟫ ⟪4⟫ ⟪3⟫ candidates_checked_⟪0⟫ candidates_checked_⟪5⟫"### args

elab "cert_compatibility_data " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem compatibility_data_⟪0⟫ : FiniteChecks.Interval compatibilityTest ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check compatibilityTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_compatibility_data_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem compatibility_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval compatibilityTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append compatibilityTest ⟪2⟫ ⟪4⟫ ⟪3⟫ compatibility_data_join_⟪0⟫_⟪5⟫ compatibility_data_join_⟪5⟫_⟪1⟫"### args

elab "cert_compatibility_data_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem compatibility_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval compatibilityTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append compatibilityTest ⟪2⟫ ⟪4⟫ ⟪3⟫ compatibility_data_⟪0⟫ compatibility_data_⟪5⟫"### args

elab "cert_nodes_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_checked_⟪0⟫ : FiniteChecks.Interval nodeTest ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check nodeTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_nodes_checked_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append nodeTest ⟪2⟫ ⟪4⟫ ⟪3⟫ nodes_checked_⟪0⟫ nodes_checked_⟪5⟫"### args

elab "cert_nodes_checked_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append nodeTest ⟪2⟫ ⟪4⟫ ⟪3⟫ nodes_part⟪5⟫_join_⟪0⟫_⟪6⟫ nodes_checked_join_⟪6⟫_⟪1⟫"### args

elab "cert_nodes_checked_join_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append nodeTest ⟪2⟫ ⟪4⟫ ⟪3⟫ nodes_part⟪5⟫_join_⟪0⟫_⟪6⟫ nodes_part⟪7⟫_join_⟪6⟫_⟪1⟫"### args

elab "cert_nodes_checked_join_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_checked_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append nodeTest ⟪2⟫ ⟪4⟫ ⟪3⟫ nodes_checked_join_⟪0⟫_⟪5⟫ nodes_checked_join_⟪5⟫_⟪1⟫"### args

elab "cert_nodes_part " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_part⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_of_check nodeTest ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_nodes_part_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_part⟪0⟫_join_⟪1⟫_⟪2⟫ : FiniteChecks.Interval nodeTest ⟪3⟫ ⟪4⟫ :=
  FiniteChecks.interval_append nodeTest ⟪3⟫ ⟪5⟫ ⟪4⟫ nodes_part⟪0⟫_join_⟪1⟫_⟪6⟫ nodes_part⟪0⟫_join_⟪6⟫_⟪2⟫"### args

elab "cert_nodes_part_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_part⟪0⟫_join_⟪1⟫_⟪2⟫ : FiniteChecks.Interval nodeTest ⟪3⟫ ⟪4⟫ :=
  FiniteChecks.interval_append nodeTest ⟪3⟫ ⟪5⟫ ⟪4⟫ nodes_part⟪0⟫_⟪1⟫ nodes_part⟪0⟫_⟪6⟫"### args

elab "cert_nodes_part_join_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodes_part044_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval nodeTest ⟪0⟫ ⟪1⟫ :=
  FiniteChecks.interval_append nodeTest ⟪0⟫ ⟪2⟫ ⟪1⟫ nodes_part044_⟪0⟫ nodes_part044_join_⟪2⟫_⟪1⟫"### args

elab "cert_rawNodePart " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def rawNodePart⟪0⟫ : ConcreteGrowth.Table Nat :=
  integerTable% 0 ⟪1⟫"### args

elab "cert_ridge_data " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridge_data_⟪0⟫ : FiniteChecks.Interval ridgeDataTest ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check ridgeDataTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_ridge_data_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridge_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval ridgeDataTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append ridgeDataTest ⟪2⟫ ⟪4⟫ ⟪3⟫ ridge_data_⟪0⟫ ridge_data_⟪5⟫"### args

elab "cert_ridge_data_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridge_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval ridgeDataTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append ridgeDataTest ⟪2⟫ ⟪4⟫ ⟪3⟫ ridge_data_join_⟪0⟫_⟪5⟫ ridge_data_join_⟪5⟫_⟪1⟫"### args

elab "cert_terminal_data " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem terminal_data_⟪0⟫ : FiniteChecks.Interval terminalTest ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check terminalTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_terminal_data_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem terminal_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval terminalTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append terminalTest ⟪2⟫ ⟪4⟫ ⟪3⟫ terminal_data_join_⟪0⟫_⟪5⟫ terminal_data_join_⟪5⟫_⟪1⟫"### args

elab "cert_terminal_data_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem terminal_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval terminalTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append terminalTest ⟪2⟫ ⟪4⟫ ⟪3⟫ terminal_data_⟪0⟫ terminal_data_⟪5⟫"### args

elab "cert_terminal_data_join_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem terminal_data_join_⟪0⟫_⟪1⟫ : FiniteChecks.Interval terminalTest ⟪2⟫ ⟪3⟫ :=
  FiniteChecks.interval_append terminalTest ⟪2⟫ ⟪4⟫ ⟪3⟫ terminal_data_⟪0⟫ terminal_data_join_⟪5⟫_⟪1⟫"### args


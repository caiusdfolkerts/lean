module
import all theorem94
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`theorem13, `theorem94, `theorem12, `theorem11]
  for name in #[`FourPapers.Universal.barycentricIntegralTensorEquiv_tmul, `FourPapers.Universal.barycentricRestrictionIdeal_mem_iff, `FourPapers.Universal.exists_coherent_parameter_comparison, `FourPapers.Universal.exists_graded_coherent_parameter_comparison, `FourPapers.Universal.faceIntegralTensorEquiv_tmul, `FourPapers.Universal.faceRestrictionIdeal_mem_iff, `FourPapers.Universal.lowerIdealBarycentricQuotientEquiv, `FourPapers.Universal.lowerIdealFaceQuotientEquiv, `FourPapers.Universal.lowerIdealFaceRestriction_generator_inside, `FourPapers.Universal.lowerIdealFaceRestriction_generator_outside, `FourPapers.Universal.lowerIdealFaceRestriction_ker, `FourPapers.Universal.originalRelativeComparison, `FourPapers.Universal.primeCycleActiveFlag_not_fixed, `FourPapers.Universal.primeCycleActiveRanks_fine, `FourPapers.Universal.primeCycle_fixed_subset_all_moved, `FourPapers.Universal.theoremOneParameterModuleEquiv, `FourPapers.Universal.theorem_1_1, `FourPapers.Universal.universalCoherentComparison_baseChange, `FourPapers.Universal.universalCoherentComparison_spec, `FourPapers.Universal.universalOriginalParameterComparison, `FourPapers.Universal.universalOriginalParameterComparison_associatedGrade, `FourPapers.Universal.universalOriginalParameterComparison_baseChange, `FourPapers.Universal.universalOriginalParameterComparison_degree, `FourPapers.Universal.universalOriginalParameterComparison_leading, `FourPapers.Universal.universalOriginalParameterComparison_lowerIdealKernel, `FourPapers.Universal.universalOriginalParameterComparison_restrictionKernel, `FourPapers.Universal.universalOriginalParameterComparison_tensorBaseChange, `FourPapers.Universal.universalOriginalParameterComparison_usualAssociatedGrade, `FourPapers.Universal.universalOriginalParameterComparison_usualDegree, `FourPapers.Universal.universalOriginalParameterComparison_usualWeight, `FourPapers.Universal.universalOriginalRelativeParameterComparison, `FourPapers.Universal.usualBarycentricWeightLevel_eq, `FourPapers.Universal.usualFaceWeightLevel_eq] do
    unless (env.find? name).isSome do
      throwError "Missing advertised declaration: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := env.header.moduleNames[idx.toNat]? | continue
    unless localModules.contains owner do continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial project declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    count := count + 1
  if count == 0 then throwError "No local declarations were checked"
  logInfo m!"Checked axiom dependencies of {count} local declarations."

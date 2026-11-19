module
prelude
import GraphInputsRow31Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0823
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 7373125058560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record000_result⟩)
 (.leaf ⟨(31, 7432844148736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 7478347563008), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 7481971507200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record003_result⟩)
 (.leaf ⟨(31, 7516192932096), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 7516998074880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record005_result⟩)
 (.leaf ⟨(31, 7533666238464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 7550829330432), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 7551357812736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record008_result⟩)
 (.leaf ⟨(31, 7560285421824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25776 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25776 25786 :=
  block_of_table results 25776 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0823

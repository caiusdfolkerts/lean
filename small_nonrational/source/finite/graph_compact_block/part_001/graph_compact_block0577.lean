module
prelude
import GraphInputsRow29Part00143Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0577
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24276632633600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record000_result⟩)
 (.leaf ⟨(29, 24276644143104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24293610389760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record002_result⟩)
 (.leaf ⟨(29, 24299050172672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24299587043328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record004_result⟩)
 (.leaf ⟨(29, 24299595366400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24303747792896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record006_result⟩)
 (.leaf ⟨(29, 24303756115968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22551 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 22551 22559 :=
  block_of_table results 22551 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0577

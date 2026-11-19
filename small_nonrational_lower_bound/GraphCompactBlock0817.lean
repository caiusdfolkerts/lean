module
prelude
import GraphInputsRow31Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0817
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 6857053765632), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record000_result⟩)
 (.leaf ⟨(31, 6885235761408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 6890610237440), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 6898523316288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record003_result⟩)
 (.leaf ⟨(31, 6919594967808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 6919875985408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record005_result⟩)
 (.leaf ⟨(31, 6928587555456), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 6932882522688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 6962948374528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record008_result⟩)
 (.leaf ⟨(31, 6986175348736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25738 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 25738 25748 :=
  block_of_table results 25738 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0817

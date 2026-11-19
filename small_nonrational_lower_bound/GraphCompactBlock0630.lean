module
prelude
import GraphInputsRow29Part00196Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0630
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 28627244711936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196.record000_result⟩)
 (.leaf ⟨(29, 28627368444160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28627372670976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28627376832512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196.record003_result⟩)
 (.leaf ⟨(29, 28627636879488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22977 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22977 22982 :=
  block_of_table results 22977 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0630

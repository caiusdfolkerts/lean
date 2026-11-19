module
prelude
import GraphInputsRow29Part00096Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0530
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 16711793311744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 16720379052032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record001_result⟩)
 (.leaf ⟨(29, 16721114038272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 16769851359488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record003_result⟩)
 (.leaf ⟨(29, 16769863389184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 16769995509760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record005_result⟩)
 (.leaf ⟨(29, 16770253996160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21850 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 21850 21857 :=
  block_of_table results 21850 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0530

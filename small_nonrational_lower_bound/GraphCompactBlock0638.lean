module
prelude
import GraphInputsRow29Part00204Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0638
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 28971702059136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 28973867221120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record001_result⟩)
 (.leaf ⟨(29, 28974051000320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 28974137737216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record003_result⟩)
 (.leaf ⟨(29, 28975997010048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 28976399516160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record005_result⟩)
 (.leaf ⟨(29, 29038475509760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00204.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23028 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23028 23035 :=
  block_of_table results 23028 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0638

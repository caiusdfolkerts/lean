module
prelude
import GraphInputsRow29Part00248Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0682
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 32042133750336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record000_result⟩)
 (.leaf ⟨(29, 32042200859168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32043208032256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record002_result⟩)
 (.leaf ⟨(29, 32060999794688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 32075369415232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record004_result⟩)
 (.leaf ⟨(29, 32076495585280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 32076963397888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record006_result⟩)
 (.leaf ⟨(29, 32078179598336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23361 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 23361 23369 :=
  block_of_table results 23361 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0682

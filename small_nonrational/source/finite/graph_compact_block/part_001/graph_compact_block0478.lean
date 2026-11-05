module
prelude
import GraphInputsRow29Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0478
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 7821953335296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 7890538594304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record001_result⟩)
 (.leaf ⟨(29, 7989924757504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 8019387613184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 8027964965504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record004_result⟩)
 (.leaf ⟨(29, 8041454141696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21089 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21089 21095 :=
  block_of_table results 21089 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0478

module
prelude
import GraphInputsRow29Part00079Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0513
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 13125973999616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 13126225627136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record001_result⟩)
 (.leaf ⟨(29, 13134010124544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 13134303592448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 13134546995200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record004_result⟩)
 (.leaf ⟨(29, 13134563639808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21581 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21581 21587 :=
  block_of_table results 21581 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0513

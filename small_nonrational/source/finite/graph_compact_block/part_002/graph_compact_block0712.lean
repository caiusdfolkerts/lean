module
prelude
import GraphInputsRow29Part00278Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0712
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34128884023552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record000_result⟩)
 (.leaf ⟨(29, 34129554964992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34132105236736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record002_result⟩)
 (.leaf ⟨(29, 34144990138432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23482 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23482 23486 :=
  block_of_table results 23482 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0712

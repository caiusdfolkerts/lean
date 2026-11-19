module
prelude
import GraphInputsRow29Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0487
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 10301890101248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 10302154342400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record001_result⟩)
 (.leaf ⟨(29, 10349399048192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 10396574449664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record003_result⟩)
 (.leaf ⟨(29, 10448890036480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 10448894198016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record005_result⟩)
 (.leaf ⟨(29, 10448894263296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00053.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21283 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 21283 21290 :=
  block_of_table results 21283 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0487

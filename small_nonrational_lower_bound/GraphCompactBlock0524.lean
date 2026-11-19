module
prelude
import GraphInputsRow29Part00090Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0524
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 15842005778688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record000_result⟩)
 (.leaf ⟨(29, 15842282569728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 15842389852160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record002_result⟩)
 (.leaf ⟨(29, 15842542649344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 15842546810880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record004_result⟩)
 (.leaf ⟨(29, 15842658254848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 15851247895040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record006_result⟩)
 (.leaf ⟨(29, 15859166888064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00090.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21773 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 21773 21781 :=
  block_of_table results 21773 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0524

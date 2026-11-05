module
prelude
import GraphInputsRow29Part00239Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0673
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 31544458674432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 31568009765120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record001_result⟩)
 (.leaf ⟨(29, 31568077848576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 31579023933440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record003_result⟩)
 (.leaf ⟨(29, 31587882237952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 31596203737088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record005_result⟩)
 (.leaf ⟨(29, 31596732219392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23321 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23321 23328 :=
  block_of_table results 23321 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0673

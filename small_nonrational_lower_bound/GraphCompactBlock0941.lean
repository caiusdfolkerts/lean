module
prelude
import GraphInputsRow31Part00153Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0941
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 30865322147840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record000_result⟩)
 (.leaf ⟨(31, 30865817141504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 30866354012160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record002_result⟩)
 (.leaf ⟨(31, 30866362335232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 30873366855936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record004_result⟩)
 (.leaf ⟨(31, 30873903726592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 30874105028608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record006_result⟩)
 (.leaf ⟨(31, 30874407043328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00153.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26640 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26640 26648 :=
  block_of_table results 26640 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0941

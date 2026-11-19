module
prelude
import GraphInputsRow31Part00120Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0908
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 27017224454144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 27025616175104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record001_result⟩)
 (.leaf ⟨(31, 27025814355968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 27032558797056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record003_result⟩)
 (.leaf ⟨(31, 27033329999872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 27049989243648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record005_result⟩)
 (.leaf ⟨(31, 27080054546688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00120.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26485 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26485 26492 :=
  block_of_table results 26485 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0908

module
prelude
import GraphInputsRow31Part00164Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0952
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 32075371511808), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 32077105856512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record001_result⟩)
 (.leaf ⟨(31, 32161858093312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 32173634682880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record003_result⟩)
 (.leaf ⟨(31, 32186519535616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 32220844802048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record005_result⟩)
 (.leaf ⟨(31, 32255204532224), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00164.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26721 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 26721 26728 :=
  block_of_table results 26721 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0952

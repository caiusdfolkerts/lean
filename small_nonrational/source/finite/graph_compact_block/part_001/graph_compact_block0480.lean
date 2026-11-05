module
prelude
import GraphInputsRow29Part00046Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0480
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 8247973560320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record000_result⟩)
 (.leaf ⟨(29, 8248094623760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 8250926305536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record002_result⟩)
 (.leaf ⟨(29, 8250926370816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 8251190546688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record004_result⟩)
 (.leaf ⟨(29, 8251190611968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 8251198410768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record006_result⟩)
 (.leaf ⟨(29, 8251215185936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21120 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 21120 21128 :=
  block_of_table results 21120 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0480

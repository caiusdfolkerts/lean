module
prelude
import GraphInputsRow31Part00105Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0893
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 24276901068800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105.record000_result⟩)
 (.leaf ⟨(31, 24298777641216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 24299054366720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 24312337661952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105.record003_result⟩)
 (.leaf ⟨(31, 24345754746880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26379 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26379 26384 :=
  block_of_table results 26379 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0893

module
prelude
import GraphInputsRow31Part00049Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0837
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 10183770644736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record000_result⟩)
 (.leaf ⟨(31, 10218129851136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 10218410868736), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record002_result⟩)
 (.leaf ⟨(31, 10227124568064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 10231417406016), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record004_result⟩)
 (.leaf ⟨(31, 10261483257856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 10489794985984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 10490059227136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record007_result⟩)
 (.leaf ⟨(31, 10490067550208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25888 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 25888 25897 :=
  block_of_table results 25888 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0837

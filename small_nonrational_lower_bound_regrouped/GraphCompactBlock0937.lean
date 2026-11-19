module
prelude
import GraphInputsRow31Part00149Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0937
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 30824309195520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 30824590213120), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record001_result⟩)
 (.leaf ⟨(31, 30825266028800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 30825274417152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 30825785856032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record004_result⟩)
 (.leaf ⟨(31, 30826389570304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00149.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26617 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26617 26623 :=
  block_of_table results 26617 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0937

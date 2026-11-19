module
prelude
import GraphInputsRow29Part00174Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0608
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25789131276288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174.record000_result⟩)
 (.leaf ⟨(29, 25843929776384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25844202405888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 25844466647040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174.record003_result⟩)
 (.leaf ⟨(29, 25844474970112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22785 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22785 22790 :=
  block_of_table results 22785 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0608

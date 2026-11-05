module
prelude
import GraphInputsRow31Part00106Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0894
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 24417695432704), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106.record000_result⟩)
 (.leaf ⟨(31, 24421253316608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 24473277833280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 24512185761792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106.record003_result⟩)
 (.leaf ⟨(31, 24573932208128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26384 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26384 26389 :=
  block_of_table results 26384 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0894

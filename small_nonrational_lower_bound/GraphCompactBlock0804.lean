module
prelude
import GraphInputsRow31Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0804
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 3930700972032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016.record000_result⟩)
 (.leaf ⟨(31, 3942815662336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 4059020984576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 4067334226176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016.record003_result⟩)
 (.leaf ⟨(31, 4075924128000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25598 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 25598 25603 :=
  block_of_table results 25598 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0804

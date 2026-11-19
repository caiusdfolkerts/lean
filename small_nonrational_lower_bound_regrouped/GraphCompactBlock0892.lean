module
prelude
import GraphInputsRow31Part00104Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0892
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 24190392475712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 24190623686720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record001_result⟩)
 (.leaf ⟨(31, 24194793373952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 24199490978048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 24208080912512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record004_result⟩)
 (.leaf ⟨(31, 24229189844992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26373 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26373 26379 :=
  block_of_table results 26373 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0892

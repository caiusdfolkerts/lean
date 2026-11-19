module
prelude
import GraphInputsRow31Part00156Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0944
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(31, 30977862664192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 30978259025920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record001_result⟩)
 (.leaf ⟨(31, 30980405460992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(31, 30983963344896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record003_result⟩)
 (.branch 5
 (.leaf ⟨(31, 31018322034688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record004_result⟩)
 (.leaf ⟨(31, 31067680571648), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26662 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 26662 26668 :=
  block_of_table results 26662 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0944

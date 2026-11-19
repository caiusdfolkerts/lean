module
prelude
import GraphInputsRow31Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0810
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 5279324372992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record000_result⟩)
 (.leaf ⟨(31, 5279332696064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 5317240881408), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record002_result⟩)
 (.leaf ⟨(31, 5317974819360), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 5317975932928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record004_result⟩)
 (.leaf ⟨(31, 5413944754176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 5516394766400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 5572262952960), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record007_result⟩)
 (.leaf ⟨(31, 5572452745472), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25668 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 25668 25677 :=
  block_of_table results 25668 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0810

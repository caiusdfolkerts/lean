module
prelude
import GraphInputsRow31Part00169Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0957
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 33298210357248), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169.record000_result⟩)
 (.leaf ⟨(31, 33307471380996), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 34086003441920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169.record002_result⟩)
 (.leaf ⟨(31, 34120432418816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26753 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 26753 26757 :=
  block_of_table results 26753 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0957

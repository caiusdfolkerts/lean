module
prelude
import GraphInputsRow29Part00219Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0653
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 29757840850944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00219.record000_result⟩)
 (.leaf ⟨(29, 29760432640128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00219.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29761506116224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00219.record002_result⟩)
 (.leaf ⟨(29, 29765534810112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00219.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23128 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23128 23132 :=
  block_of_table results 23128 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0653

module
prelude
import GraphInputsRow29Part00191Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0625
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 27756897239040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00191.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 27767127150624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00191.record001_result⟩)
 (.leaf ⟨(29, 27802602635264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00191.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22946 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 22946 22949 :=
  block_of_table results 22946 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0625

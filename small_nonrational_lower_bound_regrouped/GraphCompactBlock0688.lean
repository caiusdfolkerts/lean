module
prelude
import GraphInputsRow29Part00254Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0688
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32505457606912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254.record000_result⟩)
 (.leaf ⟨(29, 32514051735552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32514588540928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 32515091922944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254.record003_result⟩)
 (.leaf ⟨(29, 32522637475840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23388 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23388 23393 :=
  block_of_table results 23388 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0688

module
prelude
import GraphInputsRow29Part00160Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0594
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 25178373357568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00160.record000_result⟩)
 (.leaf ⟨(29, 25190004228096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00160.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25190276792320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00160.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 25190788759552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00160.record003_result⟩)
 (.leaf ⟨(29, 25194297098240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00160.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22683 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22683 22688 :=
  block_of_table results 22683 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0594

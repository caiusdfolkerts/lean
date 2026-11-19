module
prelude
import GraphInputsRow31Part00114Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0902
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 25977178619904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00114.record000_result⟩)
 (.leaf ⟨(31, 25994358423552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00114.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 25994886905856), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00114.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 25997478985728), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00114.record003_result⟩)
 (.leaf ⟨(31, 26114613379072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00114.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26443 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26443 26448 :=
  block_of_table results 26443 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0902

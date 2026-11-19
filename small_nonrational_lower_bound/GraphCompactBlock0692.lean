module
prelude
import GraphInputsRow29Part00258Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0692
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32717719207936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00258.record000_result⟩)
 (.leaf ⟨(29, 32723390496768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00258.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32729128239104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00258.record002_result⟩)
 (.leaf ⟨(29, 32730201456640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00258.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23406 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23406 23410 :=
  block_of_table results 23406 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0692

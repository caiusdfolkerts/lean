module
prelude
import GraphInputsRow29Part00186Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0620
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 27128693293056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186.record000_result⟩)
 (.leaf ⟨(29, 27130373144576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 27130645708800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 27130909949952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186.record003_result⟩)
 (.leaf ⟨(29, 27217505554464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22914 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22914 22919 :=
  block_of_table results 22914 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0620

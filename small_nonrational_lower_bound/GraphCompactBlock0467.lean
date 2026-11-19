module
prelude
import GraphInputsRow29Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0467
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7156835291392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record000_result⟩)
 (.leaf ⟨(29, 7156901351680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7157062926336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 7157065007104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record003_result⟩)
 (.leaf ⟨(29, 7158246674448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 7165421031680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record005_result⟩)
 (.leaf ⟨(29, 7185770283264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 7185774510080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 7185778086144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record008_result⟩)
 (.leaf ⟨(29, 7186298177552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20967 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 20967 20977 :=
  block_of_table results 20967 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0467

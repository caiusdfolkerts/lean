module
prelude
import GraphInputsRow29Part00211Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0645
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 29277198762112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 29277204516864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record001_result⟩)
 (.leaf ⟨(29, 29281744847376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 29283288617216), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record003_result⟩)
 (.leaf ⟨(29, 29283643822080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 29284362093312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record005_result⟩)
 (.leaf ⟨(29, 29284498472960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23082 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23082 23089 :=
  block_of_table results 23082 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0645

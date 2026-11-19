module
prelude
import GraphInputsRow29Part00283Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0717
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 34498452652032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_result⟩)
 (.leaf ⟨(29, 34500398694400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 34531537193024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 34531554115584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_result⟩)
 (.leaf ⟨(29, 34531688316928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23501 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23501 23506 :=
  block_of_table results 23501 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0717

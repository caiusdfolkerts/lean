module
prelude
import GraphInputsRow29Part00124Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0558
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 21007368716288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record000_result⟩)
 (.leaf ⟨(29, 21015946068608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 21076077772800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 21076086095872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record003_result⟩)
 (.leaf ⟨(29, 21118423433472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 21119160565760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 21257072410624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record006_result⟩)
 (.leaf ⟨(29, 21350955614208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 21367598612480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 21374041096448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record009_result⟩)
 (.leaf ⟨(29, 21378338193408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22279 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22279 22290 :=
  block_of_table results 22279 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0558

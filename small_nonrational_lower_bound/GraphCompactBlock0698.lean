module
prelude
import GraphInputsRow29Part00264Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0698
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 32933827051520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record000_result⟩)
 (.leaf ⟨(29, 32935956840448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32986578297088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record002_result⟩)
 (.leaf ⟨(29, 32986582491264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 32988672852224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record004_result⟩)
 (.leaf ⟨(29, 32989174579328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 32995315564800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 32995324993536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record007_result⟩)
 (.leaf ⟨(29, 33022410244224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00264.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23426 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23426 23435 :=
  block_of_table results 23426 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0698

module
prelude
import GraphInputsRow29Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0471
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 7435204956160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 7478343369344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record001_result⟩)
 (.leaf ⟨(29, 7518138925056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 7525072437248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 7533641206016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record004_result⟩)
 (.leaf ⟨(29, 7533657850624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 7533938868224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 7534178271232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record007_result⟩)
 (.leaf ⟨(29, 7542768173056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 7550552670464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record009_result⟩)
 (.leaf ⟨(29, 7551357813248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 7551374589952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record011_result⟩)
 (.leaf ⟨(29, 7560302199040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21023 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 21023 21036 :=
  block_of_table results 21023 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0471

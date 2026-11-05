module
prelude
import GraphInputsRow29Part00284Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0718
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 34535832160256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34634666873088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record001_result⟩)
 (.leaf ⟨(29, 34634667458560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 34634675261440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 34635170189328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record004_result⟩)
 (.leaf ⟨(29, 34635707351296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 34635725701376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 34635744608256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record007_result⟩)
 (.leaf ⟨(29, 34635752931328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 34635759255808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 34635975819264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record010_result⟩)
 (.leaf ⟨(29, 34635984142336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23506 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 23506 23518 :=
  block_of_table results 23506 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0718

module
prelude
import GraphInputsRow29Part00032Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0466
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 7003883700224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 7048242954496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record001_result⟩)
 (.leaf ⟨(29, 7050864164864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 7080339603712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record003_result⟩)
 (.leaf ⟨(29, 7098039566336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 7150227194112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record005_result⟩)
 (.leaf ⟨(29, 7150227259392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 7150355153152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record007_result⟩)
 (.leaf ⟨(29, 7150359314688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 7150359379968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record009_result⟩)
 (.leaf ⟨(29, 7150462046464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 7154085924880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record011_result⟩)
 (.leaf ⟨(29, 7156703170816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 7156794458368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record013_result⟩)
 (.leaf ⟨(29, 7156800765952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20952 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 20952 20967 :=
  block_of_table results 20952 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0466

module
prelude
import GraphInputsRow29Part00177Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0611
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 25916906602752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record000_result⟩)
 (.leaf ⟨(29, 25924439933184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25924980965376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 25925228171264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record003_result⟩)
 (.leaf ⟨(29, 25925496504576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 25926301647360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record005_result⟩)
 (.leaf ⟨(29, 25928755380224), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 25933012668672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 25963354128384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record008_result⟩)
 (.leaf ⟨(29, 25980811411456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22807 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 22807 22817 :=
  block_of_table results 22807 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0611

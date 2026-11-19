module
prelude
import GraphInputsRow29Part00119Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0553
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 20526456176640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 20567121986176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record001_result⟩)
 (.leaf ⟨(29, 20622688682240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 20622957117568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 20634300088448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record004_result⟩)
 (.leaf ⟨(29, 20634304282624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 20687922168064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 20688190636032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record007_result⟩)
 (.leaf ⟨(29, 20688198959104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 20688459038720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record009_result⟩)
 (.leaf ⟨(29, 20688591159296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 20690271010816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record011_result⟩)
 (.leaf ⟨(29, 20690279333888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22222 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22222 22235 :=
  block_of_table results 22222 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0553

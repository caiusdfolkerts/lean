module
prelude
import GraphInputsRow29Part00113Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0547
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 19592068005888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 19610889912576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record001_result⟩)
 (.leaf ⟨(29, 19611625980480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 19611627044864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record003_result⟩)
 (.leaf ⟨(29, 19619561898240), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 19619574188032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record005_result⟩)
 (.leaf ⟨(29, 19623978270976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 19623982532608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record007_result⟩)
 (.leaf ⟨(29, 19624263483392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 19624510882312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record009_result⟩)
 (.leaf ⟨(29, 19632572399616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 19633109204992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record011_result⟩)
 (.leaf ⟨(29, 19637261860864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 19645318889472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record013_result⟩)
 (.leaf ⟨(29, 19645987815424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22149 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 22149 22164 :=
  block_of_table results 22149 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0547

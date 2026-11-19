module
prelude
import GraphInputsRow31Part00094Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0882
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 18710528008256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 18769569652800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record001_result⟩)
 (.leaf ⟨(31, 18778155393088), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 18779477131520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record003_result⟩)
 (.leaf ⟨(31, 18801894686720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 18885654872064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record005_result⟩)
 (.leaf ⟨(31, 18985635561536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(31, 18988856254528), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record007_result⟩)
 (.leaf ⟨(31, 19014503890944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record008_result⟩))
 (.branch 10
 (.leaf ⟨(31, 19023215460928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record009_result⟩)
 (.leaf ⟨(31, 19027512541184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(31, 19057442062336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record011_result⟩)
 (.leaf ⟨(31, 19061871230976), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record012_result⟩))
 (.branch 14
 (.leaf ⟨(31, 19129853559040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record013_result⟩)
 (.leaf ⟨(31, 19281857282048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094.record014_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26279 + i))) 0 15 :=
  interval_of_check _ 0 15 (by decide +kernel)

public theorem complete : Block 26279 26294 :=
  block_of_table results 26279 15 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0882

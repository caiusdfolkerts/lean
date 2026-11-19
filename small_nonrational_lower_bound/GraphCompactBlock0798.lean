module
prelude
import GraphInputsRow31Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0798
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 1972073660416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record000_result⟩)
 (.leaf ⟨(31, 2015149228032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 2015157551104), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record002_result⟩)
 (.leaf ⟨(31, 2018703868160), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 2018773106944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record004_result⟩)
 (.leaf ⟨(31, 2019439936256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 2019444195328), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record006_result⟩)
 (.leaf ⟨(31, 2019452518400), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(31, 2031792226560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record008_result⟩)
 (.leaf ⟨(31, 2040386355200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record009_result⟩))
 (.branch 11
 (.leaf ⟨(31, 2040923160576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record010_result⟩)
 (.leaf ⟨(31, 2053132845056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(31, 2057566158848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record012_result⟩)
 (.leaf ⟨(31, 2058094641152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record013_result⟩))
 (.branch 15
 (.leaf ⟨(31, 2087492583680), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record014_result⟩)
 (.branch 16
 (.leaf ⟨(31, 2088161574912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record015_result⟩)
 (.leaf ⟨(31, 2132589740288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25553 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 25553 25570 :=
  block_of_table results 25553 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0798

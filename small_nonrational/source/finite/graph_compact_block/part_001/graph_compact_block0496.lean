module
prelude
import GraphInputsRow29Part00062Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0496
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 11487496142848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 11554877608192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record001_result⟩)
 (.leaf ⟨(29, 11585410072832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 11585418461184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record003_result⟩)
 (.leaf ⟨(29, 11588113273088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 11589310808064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record005_result⟩)
 (.leaf ⟨(29, 11589579210752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(29, 11589702942976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record007_result⟩)
 (.leaf ⟨(29, 11592922595584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record008_result⟩))
 (.branch 10
 (.leaf ⟨(29, 11592934625280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record009_result⟩)
 (.leaf ⟨(29, 11597900709888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 11598292877440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record011_result⟩)
 (.leaf ⟨(29, 11601512530048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 11605807480960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record013_result⟩)
 (.leaf ⟨(29, 11674526417536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(29, 11684750037248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record015_result⟩)
 (.branch 17
 (.leaf ⟨(29, 11689571389440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record016_result⟩)
 (.leaf ⟨(29, 11693732139008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(29, 11700778598400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record018_result⟩)
 (.leaf ⟨(29, 11701371027584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record019_result⟩))
 (.branch 21
 (.leaf ⟨(29, 11730360992512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record020_result⟩)
 (.leaf ⟨(29, 11738950926976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 11826998313088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record022_result⟩)
 (.leaf ⟨(29, 11830902657024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 11831293264000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record024_result⟩)
 (.leaf ⟨(29, 11931716943872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(29, 11932224749568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record026_result⟩)
 (.leaf ⟨(29, 11960548622592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record027_result⟩))
 (.branch 29
 (.leaf ⟨(29, 11960817090560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record028_result⟩)
 (.leaf ⟨(29, 11960825413632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00062.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21368 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 21368 21398 :=
  block_of_table results 21368 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0496

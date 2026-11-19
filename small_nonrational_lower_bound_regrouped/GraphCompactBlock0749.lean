module
prelude
import GraphInputsRow30Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0749
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 11398912442496), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record000_result⟩)
 (.leaf ⟨(30, 11401129132032), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 11401397534720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record002_result⟩)
 (.leaf ⟨(30, 11448650563584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 11448910643200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record004_result⟩)
 (.leaf ⟨(30, 11452943433728), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 11453203513344), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 11455089868800), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record007_result⟩)
 (.leaf ⟨(30, 11463336951936), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 11471926886400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record009_result⟩)
 (.leaf ⟨(30, 11472063168512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 11487496142848), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record011_result⟩)
 (.leaf ⟨(30, 11554877608192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(30, 11585410072832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record013_result⟩)
 (.leaf ⟨(30, 11585418461184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record014_result⟩))
 (.branch 16
 (.leaf ⟨(30, 11588113273088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 11589310808064), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record016_result⟩)
 (.leaf ⟨(30, 11589579210752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(30, 11592922595584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record018_result⟩)
 (.leaf ⟨(30, 11592934625280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record019_result⟩))
 (.branch 21
 (.leaf ⟨(30, 11597900709888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record020_result⟩)
 (.leaf ⟨(30, 11598292877440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(30, 11601512530048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record022_result⟩)
 (.leaf ⟨(30, 11605807480960), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record023_result⟩))
 (.branch 25
 (.leaf ⟨(30, 11674526417536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record024_result⟩)
 (.branch 26
 (.leaf ⟨(30, 11684750037248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record025_result⟩)
 (.leaf ⟨(30, 11689571389440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record026_result⟩)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf ⟨(30, 11693732139008), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record027_result⟩)
 (.leaf ⟨(30, 11700778598400), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record028_result⟩))
 (.branch 30
 (.leaf ⟨(30, 11701371027584), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record029_result⟩)
 (.leaf ⟨(30, 11730360992512), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(30, 11738950926976), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record031_result⟩)
 (.leaf ⟨(30, 11826998313088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record032_result⟩))
 (.branch 34
 (.leaf ⟨(30, 11830902657024), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record033_result⟩)
 (.branch 35
 (.leaf ⟨(30, 11831293264000), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record034_result⟩)
 (.leaf ⟨(30, 11931716943872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00021.record035_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24196 + i))) 0 36 :=
  interval_of_check _ 0 36 (by decide +kernel)

public theorem complete : Block 24196 24232 :=
  block_of_table results 24196 36 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0749

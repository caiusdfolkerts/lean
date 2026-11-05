module
prelude
import GraphInputsRow23Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0103
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 30943897722944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 30969467830272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record001_result⟩)
 (.leaf ⟨(23, 31014027034880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 31014765207552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 31065793105952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record004_result⟩)
 (.leaf ⟨(23, 31065842651168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 31072344088832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 31099390558208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record007_result⟩)
 (.leaf ⟨(23, 31244345671680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 31337717702784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 31346316574976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record010_result⟩)
 (.leaf ⟨(23, 31346328084480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 31414535913728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 31414808543232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record013_result⟩)
 (.leaf ⟨(23, 31415072784384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 31415081107456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 31415270965248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record016_result⟩)
 (.leaf ⟨(23, 31430605308160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 31431376510976), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 31441580785920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record019_result⟩)
 (.leaf ⟨(23, 31448308449280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 31448316772352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record021_result⟩)
 (.leaf ⟨(23, 31450174914560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 31450711719936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record023_result⟩)
 (.leaf ⟨(23, 31465001779200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record024_result⟩))))))
 (.branch 38
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 31465736765440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 31482672848896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record026_result⟩)
 (.leaf ⟨(23, 31483729420288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 31491843195136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 31492177723392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record029_result⟩)
 (.leaf ⟨(23, 31495029817600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 31495801020416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 31510166044928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record032_result⟩)
 (.leaf ⟨(23, 31519296978944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record033_result⟩)))
 (.branch 36
 (.branch 35
 (.leaf ⟨(23, 31520840548352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record034_result⟩)
 (.leaf ⟨(23, 31527345913856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record035_result⟩))
 (.branch 37
 (.leaf ⟨(23, 31527618478080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record036_result⟩)
 (.leaf ⟨(23, 31529426288640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record037_result⟩)))))
 (.branch 44
 (.branch 41
 (.branch 39
 (.leaf ⟨(23, 31530160226816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record038_result⟩)
 (.branch 40
 (.leaf ⟨(23, 31530161274880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record039_result⟩)
 (.leaf ⟨(23, 31544458674432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(23, 31568077848576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record041_result⟩)
 (.branch 43
 (.leaf ⟨(23, 31579023933440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record042_result⟩)
 (.leaf ⟨(23, 31587882237952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record043_result⟩))))
 (.branch 47
 (.branch 45
 (.leaf ⟨(23, 31596203737088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record044_result⟩)
 (.branch 46
 (.leaf ⟨(23, 31596732219392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record045_result⟩)
 (.leaf ⟨(23, 31602444861440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(23, 31605053718528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record047_result⟩)
 (.leaf ⟨(23, 31611253166112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record048_result⟩))
 (.branch 50
 (.leaf ⟨(23, 31750614974720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record049_result⟩)
 (.leaf ⟨(23, 31785043951616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00025.record050_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7536 + i))) 0 51 :=
  interval_of_check _ 0 51 (by decide +kernel)

public theorem complete : Block 7536 7587 :=
  block_of_table results 7536 51 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0103

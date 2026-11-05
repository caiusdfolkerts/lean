module
prelude
import GraphInputsRow26Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0363
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 24520021803008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record000_result⟩)
 (.leaf ⟨(26, 24520071348224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 24521111404544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 24521243361920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record003_result⟩)
 (.leaf ⟨(26, 24567299211520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 24567373367424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 24567769729152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record006_result⟩)
 (.leaf ⟨(26, 24569503156352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 24569651986432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 24571583531136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record009_result⟩)
 (.leaf ⟨(26, 24576091291648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 24576138690816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 24578353005312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record012_result⟩)
 (.leaf ⟨(26, 24584462141568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 24590835385472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 24590839579648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record015_result⟩)
 (.leaf ⟨(26, 24591103689220), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 24605001580544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 24605197615360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record018_result⟩)
 (.leaf ⟨(26, 24605404184576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 24607286378496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 24608221233152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record021_result⟩)
 (.leaf ⟨(26, 24608326565888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 24608590807040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record023_result⟩)
 (.leaf ⟨(26, 24611841392704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 24616639676672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 24616707883008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record026_result⟩)
 (.leaf ⟨(26, 24616716206080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(26, 24616815296512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 24617176547328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record029_result⟩)
 (.leaf ⟨(26, 24621303210048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(26, 24628620689408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 24629524578368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record032_result⟩)
 (.leaf ⟨(26, 24629592735744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(26, 24629658796032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 24629660876800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record035_result⟩)
 (.leaf ⟨(26, 24638237245440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(26, 24638243487744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 24638367219968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record038_result⟩)
 (.leaf ⟨(26, 24638375608320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(26, 24638482825472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 24638493034496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record041_result⟩)
 (.leaf ⟨(26, 24638885478464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(26, 24640428998912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 24640441288704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record044_result⟩)
 (.leaf ⟨(26, 24640515801088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00047.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16501 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 16501 16547 :=
  block_of_table results 16501 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0363

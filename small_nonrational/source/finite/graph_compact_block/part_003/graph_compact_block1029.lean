module
prelude
import GraphInputsSix0Part00064Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1029
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 36
 (.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 24502941024512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record000_result⟩)
 (.leaf ⟨(32, 24502965635200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 24504204066816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record002_result⟩)
 (.leaf ⟨(32, 24508494790912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 24508560851200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record004_result⟩)
 (.leaf ⟨(32, 24512789807104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 24512798130176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 24513258471424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record007_result⟩)
 (.leaf ⟨(32, 24513326612480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 24515844245632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record009_result⟩)
 (.leaf ⟨(32, 24518229753857), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 24519031029760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record011_result⟩)
 (.leaf ⟨(32, 24520021803008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(32, 24520071348224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record013_result⟩)
 (.leaf ⟨(32, 24521111404544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record014_result⟩))
 (.branch 16
 (.leaf ⟨(32, 24521243361920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 24567299211520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record016_result⟩)
 (.leaf ⟨(32, 24567307307136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(32, 24567373367424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record018_result⟩)
 (.leaf ⟨(32, 24567769729152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record019_result⟩))
 (.branch 21
 (.leaf ⟨(32, 24569503156352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record020_result⟩)
 (.leaf ⟨(32, 24569651986432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(32, 24571583531136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record022_result⟩)
 (.leaf ⟨(32, 24576089145600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record023_result⟩))
 (.branch 25
 (.leaf ⟨(32, 24576091291648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record024_result⟩)
 (.branch 26
 (.leaf ⟨(32, 24576138690816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record025_result⟩)
 (.leaf ⟨(32, 24578353005312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record026_result⟩)))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf ⟨(32, 24584462141568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record027_result⟩)
 (.leaf ⟨(32, 24590835385472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record028_result⟩))
 (.branch 30
 (.leaf ⟨(32, 24590839579648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record029_result⟩)
 (.leaf ⟨(32, 24591103689220), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(32, 24604997353728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record031_result⟩)
 (.leaf ⟨(32, 24605001580544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record032_result⟩))
 (.branch 34
 (.leaf ⟨(32, 24605007822848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record033_result⟩)
 (.branch 35
 (.leaf ⟨(32, 24605131555072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record034_result⟩)
 (.leaf ⟨(32, 24605139943424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record035_result⟩)))))))
 (.branch 54
 (.branch 45
 (.branch 40
 (.branch 38
 (.branch 37
 (.leaf ⟨(32, 24605197615360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record036_result⟩)
 (.leaf ⟨(32, 24605404184576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record037_result⟩))
 (.branch 39
 (.leaf ⟨(32, 24605600268352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record038_result⟩)
 (.leaf ⟨(32, 24607286378496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record039_result⟩)))
 (.branch 42
 (.branch 41
 (.leaf ⟨(32, 24608221233152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record040_result⟩)
 (.leaf ⟨(32, 24608318177536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record041_result⟩))
 (.branch 43
 (.leaf ⟨(32, 24608326565888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record042_result⟩)
 (.branch 44
 (.leaf ⟨(32, 24608590807040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record043_result⟩)
 (.leaf ⟨(32, 24608820961344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record044_result⟩)))))
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf ⟨(32, 24611841392704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record045_result⟩)
 (.leaf ⟨(32, 24612981710912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record046_result⟩))
 (.branch 48
 (.leaf ⟨(32, 24616639676672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record047_result⟩)
 (.leaf ⟨(32, 24616707883008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(32, 24616716206080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record049_result⟩)
 (.leaf ⟨(32, 24616815296512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record050_result⟩))
 (.branch 52
 (.leaf ⟨(32, 24617176547328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record051_result⟩)
 (.branch 53
 (.leaf ⟨(32, 24620162891840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record052_result⟩)
 (.leaf ⟨(32, 24621303210048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record053_result⟩))))))
 (.branch 63
 (.branch 58
 (.branch 56
 (.branch 55
 (.leaf ⟨(32, 24628484390976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record054_result⟩)
 (.leaf ⟨(32, 24628618608640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record055_result⟩))
 (.branch 57
 (.leaf ⟨(32, 24628620689408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record056_result⟩)
 (.leaf ⟨(32, 24629524578368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record057_result⟩)))
 (.branch 60
 (.branch 59
 (.leaf ⟨(32, 24629592735744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record058_result⟩)
 (.leaf ⟨(32, 24629658796032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record059_result⟩))
 (.branch 61
 (.leaf ⟨(32, 24629660876800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record060_result⟩)
 (.branch 62
 (.leaf ⟨(32, 24638233018624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record061_result⟩)
 (.leaf ⟨(32, 24638237245440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record062_result⟩)))))
 (.branch 67
 (.branch 65
 (.branch 64
 (.leaf ⟨(32, 24638243487744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record063_result⟩)
 (.leaf ⟨(32, 24638367219968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record064_result⟩))
 (.branch 66
 (.leaf ⟨(32, 24638375608320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record065_result⟩)
 (.leaf ⟨(32, 24638482825472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record066_result⟩)))
 (.branch 69
 (.branch 68
 (.leaf ⟨(32, 24638493034496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record067_result⟩)
 (.leaf ⟨(32, 24638885478464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record068_result⟩))
 (.branch 70
 (.leaf ⟨(32, 24640383680512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record069_result⟩)
 (.branch 71
 (.leaf ⟨(32, 24640428998912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record070_result⟩)
 (.leaf ⟨(32, 24640441288704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00064.record071_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33120 + i))) 0 72 :=
  interval_of_check _ 0 72 (by decide +kernel)

public theorem complete : Block 33120 33192 :=
  block_of_table results 33120 72 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1029

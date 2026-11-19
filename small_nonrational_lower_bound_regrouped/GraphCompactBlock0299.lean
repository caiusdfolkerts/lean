module
prelude
import GraphInputsRow25Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0299
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 12000698564608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 12000810008576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record001_result⟩)
 (.leaf ⟨(25, 12004433756416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(25, 12005238899200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record003_result⟩)
 (.leaf ⟨(25, 12008747466880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record004_result⟩))
 (.branch 6
 (.leaf ⟨(25, 12009131507712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record005_result⟩)
 (.leaf ⟨(25, 12013023690880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(25, 12017318641792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record007_result⟩)
 (.leaf ⟨(25, 12021613625344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record008_result⟩))
 (.branch 10
 (.leaf ⟨(25, 12021882028032), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record009_result⟩)
 (.leaf ⟨(25, 12098258080000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(25, 12100338454784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record011_result⟩)
 (.leaf ⟨(25, 12133574119680), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record012_result⟩))
 (.branch 14
 (.leaf ⟨(25, 12134771654656), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record013_result⟩)
 (.leaf ⟨(25, 12135031668992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(25, 12135040057344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 12139064524800), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record016_result⟩)
 (.leaf ⟨(25, 12139332927488), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(25, 12142544191744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record018_result⟩)
 (.leaf ⟨(25, 12142556221440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record019_result⟩))
 (.branch 21
 (.leaf ⟨(25, 12147650265088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record020_result⟩)
 (.leaf ⟨(25, 12147654426624), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(25, 12147914473600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record022_result⟩)
 (.leaf ⟨(25, 12151134126208), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record023_result⟩))
 (.branch 25
 (.leaf ⟨(25, 12151268327552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record024_result⟩)
 (.leaf ⟨(25, 12165786374400), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(25, 12167932809472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record026_result⟩)
 (.leaf ⟨(25, 12173625556992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record027_result⟩))
 (.branch 29
 (.leaf ⟨(25, 12176848850944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record028_result⟩)
 (.leaf ⟨(25, 12181947056128), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(25, 12245566230528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 12250532315136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record031_result⟩)
 (.leaf ⟨(25, 12250992623744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(25, 12320784777856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record033_result⟩)
 (.leaf ⟨(25, 12376363503616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record034_result⟩))
 (.branch 36
 (.leaf ⟨(25, 12376619909248), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record035_result⟩)
 (.leaf ⟨(25, 12380656373760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(25, 12380914860160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record037_result⟩)
 (.leaf ⟨(25, 12382802808832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record038_result⟩))
 (.branch 40
 (.leaf ⟨(25, 12447958204672), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record039_result⟩)
 (.leaf ⟨(25, 12448495075328), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(25, 12465138073600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record041_result⟩)
 (.leaf ⟨(25, 12465274355712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record042_result⟩))
 (.branch 44
 (.leaf ⟨(25, 12546270855168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record043_result⟩)
 (.leaf ⟨(25, 12554600448000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record044_result⟩)))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf ⟨(25, 12577830633728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record045_result⟩)
 (.branch 47
 (.leaf ⟨(25, 12577966981120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record046_result⟩)
 (.leaf ⟨(25, 12577975304192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(25, 12578107424768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record048_result⟩)
 (.leaf ⟨(25, 12578214707200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record049_result⟩))
 (.branch 51
 (.leaf ⟨(25, 12578367504384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record050_result⟩)
 (.leaf ⟨(25, 12578371665920), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record051_result⟩))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf ⟨(25, 12578483109888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record052_result⟩)
 (.leaf ⟨(25, 12584810971136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record053_result⟩))
 (.branch 55
 (.leaf ⟨(25, 12586812702720), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record054_result⟩)
 (.leaf ⟨(25, 12592861954176), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record055_result⟩)))
 (.branch 58
 (.branch 57
 (.leaf ⟨(25, 12593045733376), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record056_result⟩)
 (.leaf ⟨(25, 12594991743104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record057_result⟩))
 (.branch 59
 (.leaf ⟨(25, 12645748969728), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record058_result⟩)
 (.leaf ⟨(25, 12648968622336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00009.record059_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12821 + i))) 0 60 :=
  interval_of_check _ 0 60 (by decide +kernel)

public theorem complete : Block 12821 12881 :=
  block_of_table results 12821 60 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0299

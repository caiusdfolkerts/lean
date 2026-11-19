module
prelude
import GraphInputsRow23Part00006Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0084
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 11700778598400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 11701371027584), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record001_result⟩)
 (.leaf ⟨(23, 11830902657024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 11931716943872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 11932224749568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record004_result⟩)
 (.leaf ⟨(23, 11960548622592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 11960817090560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 11960825413632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record007_result⟩)
 (.leaf ⟨(23, 11961085493248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 11961217613824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 11963937652736), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record010_result⟩)
 (.leaf ⟨(23, 11963945975808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 11966921867520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 11967198658560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record013_result⟩)
 (.leaf ⟨(23, 11967458738176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 11975511801984), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 11982993375360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record016_result⟩)
 (.leaf ⟨(23, 11984101736448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 11984238018560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 11996133130240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record019_result⟩)
 (.leaf ⟨(23, 11996141453312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 11996401532928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record021_result⟩)
 (.leaf ⟨(23, 11996649259008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 12000157532416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record023_result⟩)
 (.leaf ⟨(23, 12000434323456), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 12000541605888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 12000694403072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record026_result⟩)
 (.leaf ⟨(23, 12000698564608), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 12000810008576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 12005238899200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record029_result⟩)
 (.leaf ⟨(23, 12009131507712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 12021613625344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 12021882028032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record032_result⟩)
 (.leaf ⟨(23, 12098258080000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 12133574119680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 12134771654656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record035_result⟩)
 (.leaf ⟨(23, 12135040057344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 12135163789568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 12139064524800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record038_result⟩)
 (.leaf ⟨(23, 12139324539136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 12139332927488), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 12142556221440), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record041_result⟩)
 (.leaf ⟨(23, 12147646038272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 12147650265088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 12147654426624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record044_result⟩)
 (.leaf ⟨(23, 12165786374400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 12170607726592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record046_result⟩)
 (.leaf ⟨(23, 12173357154304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 12173423214592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record048_result⟩)
 (.leaf ⟨(23, 12173617168640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 12173625556992), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 12174768476160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record051_result⟩)
 (.leaf ⟨(23, 12176848850944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 12181806547200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 12181814935552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record054_result⟩)
 (.leaf ⟨(23, 12181938667776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 12181942894592), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 12181947056128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record057_result⟩)
 (.leaf ⟨(23, 12182013116416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 12239192985600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 12243485855744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record060_result⟩)
 (.leaf ⟨(23, 12245566230528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 12250523926784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 12250528153600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record063_result⟩)
 (.leaf ⟨(23, 12250532315136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 12250992623744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 12252065841280), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record066_result⟩)
 (.leaf ⟨(23, 12280118968320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 12319109185792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 12376351473920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record069_result⟩)
 (.leaf ⟨(23, 12376363503616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 12380656373760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record071_result⟩)
 (.leaf ⟨(23, 12382802808832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 12387967074304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record073_result⟩)
 (.leaf ⟨(23, 12447958204672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 12448495075328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 12456548139136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record076_result⟩)
 (.leaf ⟨(23, 12465138073600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 12465274355712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 12512519061504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record079_result⟩)
 (.leaf ⟨(23, 12545754726400), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 12546270855168), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 12554600448000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record082_result⟩)
 (.leaf ⟨(23, 12577830633728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 12577966981120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 12577975304192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record085_result⟩)
 (.leaf ⟨(23, 12578107424768), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 12578214707200), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 12578367504384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record088_result⟩)
 (.leaf ⟨(23, 12578371665920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 12578483109888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 12582912000512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record091_result⟩)
 (.leaf ⟨(23, 12584455831552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 12584810971136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 12586812702720), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record094_result⟩)
 (.leaf ⟨(23, 12587072750080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 12592861954176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record096_result⟩)
 (.leaf ⟨(23, 12593045733376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 12650067066880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record098_result⟩)
 (.leaf ⟨(23, 12650335469568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00006.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (6138 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 6138 6238 :=
  block_of_table results 6138 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0084

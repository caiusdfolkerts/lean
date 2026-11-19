module
prelude
import GraphInputsRow28Part00003Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0423
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(28, 8542727766016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record000_result⟩)
 (.branch 2
 (.leaf ⟨(28, 8543495782400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record001_result⟩)
 (.leaf ⟨(28, 8615981219840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(28, 8616509702144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record003_result⟩)
 (.branch 5
 (.leaf ⟨(28, 8663225925632), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record004_result⟩)
 (.leaf ⟨(28, 8684566478848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(28, 8727390650368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record006_result⟩)
 (.branch 8
 (.leaf ⟨(28, 8727927455744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record007_result⟩)
 (.leaf ⟨(28, 8736508739584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(28, 8744553547776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record009_result⟩)
 (.branch 11
 (.leaf ⟨(28, 8744578580480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record010_result⟩)
 (.leaf ⟨(28, 8745107062784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(28, 8753680220160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 8910324957184), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record013_result⟩)
 (.leaf ⟨(28, 8952126390528), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(28, 8952399020160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 8979042336768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record016_result⟩)
 (.leaf ⟨(28, 8987628077056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(28, 8988036972544), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 9015942717696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record019_result⟩)
 (.leaf ⟨(28, 9125465456768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 9424571793664), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record021_result⟩)
 (.leaf ⟨(28, 9424580182016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 9475515744256), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record023_result⟩)
 (.leaf ⟨(28, 9493297561600), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(28, 9494601990144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record025_result⟩)
 (.branch 27
 (.leaf ⟨(28, 9496978530560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record026_result⟩)
 (.leaf ⟨(28, 9528523424000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(28, 9539931930624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 9539940253696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record029_result⟩)
 (.leaf ⟨(28, 9578583490560), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(28, 9668789272576), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record031_result⟩)
 (.branch 33
 (.leaf ⟨(28, 9677370851328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record032_result⟩)
 (.leaf ⟨(28, 9716022411264), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(28, 10010104954880), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record034_result⟩)
 (.branch 36
 (.leaf ⟨(28, 10046600126720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record035_result⟩)
 (.leaf ⟨(28, 10051913793536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(28, 10089561849856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record037_result⟩)
 (.branch 39
 (.leaf ⟨(28, 10124044337152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record038_result⟩)
 (.leaf ⟨(28, 10155588648960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(28, 10183770644736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record040_result⟩)
 (.branch 42
 (.leaf ⟨(28, 10218410868736), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record041_result⟩)
 (.leaf ⟨(28, 10227124568064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(28, 10261483257856), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record043_result⟩)
 (.branch 45
 (.leaf ⟨(28, 10489794985984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record044_result⟩)
 (.leaf ⟨(28, 10490059227136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(28, 10490067550208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record046_result⟩)
 (.leaf ⟨(28, 10493411000320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record047_result⟩))
 (.branch 49
 (.leaf ⟨(28, 10601399058432), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record048_result⟩)
 (.leaf ⟨(28, 10639439299072), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(28, 10678102392832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record050_result⟩)
 (.branch 52
 (.leaf ⟨(28, 10815532958208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record051_result⟩)
 (.leaf ⟨(28, 10896625631232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(28, 10904922161152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record053_result⟩)
 (.branch 55
 (.leaf ⟨(28, 10905467224064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record054_result⟩)
 (.leaf ⟨(28, 10913788723200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(28, 10914317205504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record056_result⟩)
 (.branch 58
 (.leaf ⟨(28, 11151615213696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record057_result⟩)
 (.leaf ⟨(28, 11214966030336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(28, 11223555932160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record059_result⟩)
 (.branch 61
 (.leaf ⟨(28, 11246782906368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record060_result⟩)
 (.leaf ⟨(28, 11317654061056), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(28, 11673993805824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record062_result⟩)
 (.branch 64
 (.leaf ⟨(28, 11674530611200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record063_result⟩)
 (.leaf ⟨(28, 11693451706368), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(28, 11730369380352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 11738955120640), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record066_result⟩)
 (.leaf ⟨(28, 11742579064832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 11880017985536), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 11948871647232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record069_result⟩)
 (.leaf ⟨(28, 11959474880768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(28, 11983027994624), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record071_result⟩)
 (.leaf ⟨(28, 11996116353024), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record072_result⟩))
 (.branch 74
 (.leaf ⟨(28, 12004710416384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record073_result⟩)
 (.leaf ⟨(28, 12005238898688), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(28, 12013296156672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record075_result⟩)
 (.branch 77
 (.leaf ⟨(28, 12017456906240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record076_result⟩)
 (.leaf ⟨(28, 12021881896960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(28, 12142275788800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record078_result⟩)
 (.branch 80
 (.leaf ⟨(28, 12174488043520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record079_result⟩)
 (.leaf ⟨(28, 12211405717504), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(28, 12219454652416), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record081_result⟩)
 (.branch 83
 (.leaf ⟨(28, 12219991457792), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record082_result⟩)
 (.leaf ⟨(28, 12279990976512), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(28, 12288039911424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record084_result⟩)
 (.branch 86
 (.leaf ⟨(28, 12288576716800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record085_result⟩)
 (.leaf ⟨(28, 12314283606016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(28, 12320788971520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record087_result⟩)
 (.branch 89
 (.leaf ⟨(28, 12425478832128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record088_result⟩)
 (.leaf ⟨(28, 12440511217920), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(28, 12464064331776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record090_result⟩)
 (.branch 92
 (.leaf ⟨(28, 12577950203904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record091_result⟩)
 (.leaf ⟨(28, 12582383517696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(28, 12582912000000), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record093_result⟩)
 (.branch 95
 (.leaf ⟨(28, 12587072749568), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record094_result⟩)
 (.leaf ⟨(28, 12595130007552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(28, 12654450638848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record096_result⟩)
 (.leaf ⟨(28, 12721978933248), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record097_result⟩))
 (.branch 99
 (.leaf ⟨(28, 12723043762176), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record098_result⟩)
 (.leaf ⟨(28, 12723580567552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00003.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (19604 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 19604 19704 :=
  block_of_table results 19604 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0423

module
prelude
import GraphInputsSix0Part00048Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1013
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 18962886754304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 18962895077376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record001_result⟩)
 (.leaf ⟨(32, 18974262722816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 18985033744512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 19006515872000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record004_result⟩)
 (.leaf ⟨(32, 19014503899200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 19020671631616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 19020671696896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record007_result⟩)
 (.leaf ⟨(32, 19020677922880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 19023695740928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 19038728126720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record010_result⟩)
 (.leaf ⟨(32, 19041947779328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 19059028557824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 19059127648256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record013_result⟩)
 (.leaf ⟨(32, 19071963791616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 19072483854464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 19074110226688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record016_result⟩)
 (.leaf ⟨(32, 19074506588416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 19074564229248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 19076504158464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record019_result⟩)
 (.leaf ⟨(32, 19076512546816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 19076904681728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record021_result⟩)
 (.leaf ⟨(32, 19076915150848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 19080797028608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record023_result⟩)
 (.leaf ⟨(32, 19080805416960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 19081065431296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 19081075900416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record026_result⟩)
 (.leaf ⟨(32, 19081199632640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 19083346067712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 19087046477952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record029_result⟩)
 (.leaf ⟨(32, 19089386930432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 19089391157248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 19089397399552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record032_result⟩)
 (.leaf ⟨(32, 19093411496192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 19093419884544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 19093948203648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record035_result⟩)
 (.leaf ⟨(32, 19096230969408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 19097708429568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 19097976897536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record038_result⟩)
 (.leaf ⟨(32, 19097985220608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 19098379501568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 19098513702912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record041_result⟩)
 (.leaf ⟨(32, 19099788804352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 19099925151744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 19099933474816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record044_result⟩)
 (.leaf ⟨(32, 19100057272320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 19100065595392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record046_result⟩)
 (.leaf ⟨(32, 19100329836544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 19100525936640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record048_result⟩)
 (.leaf ⟨(32, 19145221538048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 19145229926400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 19145489940736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record051_result⟩)
 (.leaf ⟨(32, 19145500409856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 19145624142080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 19149784891648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record054_result⟩)
 (.leaf ⟨(32, 19149793280000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 19151931326720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 19158106390784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record057_result⟩)
 (.leaf ⟨(32, 19158114779136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 19158509043776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 19160655478848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record060_result⟩)
 (.leaf ⟨(32, 19166427889920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 19166964760576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 19168508264704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record063_result⟩)
 (.leaf ⟨(32, 19168642531328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 19168650854400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 19169045135360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record066_result⟩)
 (.leaf ⟨(32, 19169111195648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 19179382046976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 19179390435328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record069_result⟩)
 (.leaf ⟨(32, 19179514167552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 19179522555904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record071_result⟩)
 (.leaf ⟨(32, 19179782570240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 19179786797056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record073_result⟩)
 (.leaf ⟨(32, 19179793039360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 19179982831872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 19184077521152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record076_result⟩)
 (.leaf ⟨(32, 19184085909504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 19184143581440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 19192465080576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record079_result⟩)
 (.leaf ⟨(32, 19192671649792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 19192867733568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 19245255704704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record082_result⟩)
 (.leaf ⟨(32, 19247402139776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 19260280750208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 19280670834816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record085_result⟩)
 (.leaf ⟨(32, 19281597235456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 19281727406208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 19281865638144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record088_result⟩)
 (.leaf ⟨(32, 19281865703424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 19281999839488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 19285890105600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record091_result⟩)
 (.leaf ⟨(32, 19286158508288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 19286158573568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 19286160589056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record094_result⟩)
 (.leaf ⟨(32, 19289381802240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 19294475845888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record096_result⟩)
 (.leaf ⟨(32, 19294480007424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 19294480072704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record098_result⟩)
 (.leaf ⟨(32, 19294482088192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00048.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31550 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31550 31650 :=
  block_of_table results 31550 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1013

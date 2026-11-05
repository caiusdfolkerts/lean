module
prelude
import GraphInputsRow23Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0080
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 4076733530112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 4076741853184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record001_result⟩)
 (.leaf ⟨(23, 4081026400256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 4127755079936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 4136456749312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record004_result⟩)
 (.leaf ⟨(23, 4136725152000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 4136737181696), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 4141831225344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record007_result⟩)
 (.leaf ⟨(23, 4141835386880), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 4145315086464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 4145449287808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record010_result⟩)
 (.leaf ⟨(23, 4287184781312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(23, 4329478324480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(23, 4329482551296), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record013_result⟩)
 (.leaf ⟨(23, 4329490614272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(23, 4329729952000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 4333898958848), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record016_result⟩)
 (.leaf ⟨(23, 4334179909632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(23, 4334188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(23, 4342488825856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record019_result⟩)
 (.leaf ⟨(23, 4343025631232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(23, 4346525810944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record021_result⟩)
 (.leaf ⟨(23, 4346909884416), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record022_result⟩))
 (.branch 24
 (.leaf ⟨(23, 4347062681600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record023_result⟩)
 (.leaf ⟨(23, 4347066843136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(23, 4347178287104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record025_result⟩)
 (.branch 27
 (.leaf ⟨(23, 4355235315712), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record026_result⟩)
 (.leaf ⟨(23, 4355904241664), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(23, 4359391937536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record028_result⟩)
 (.branch 30
 (.leaf ⟨(23, 4359668629504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record029_result⟩)
 (.leaf ⟨(23, 4359928807424), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(23, 4360197111808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record031_result⟩)
 (.branch 33
 (.leaf ⟨(23, 4521136848896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record032_result⟩)
 (.leaf ⟨(23, 4658498142464), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(23, 4787347161344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record034_result⟩)
 (.branch 36
 (.leaf ⟨(23, 5104109453312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record035_result⟩)
 (.leaf ⟨(23, 5123505979392), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(23, 5137345118208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record037_result⟩)
 (.branch 39
 (.leaf ⟨(23, 5138460737792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record038_result⟩)
 (.leaf ⟨(23, 5140140589312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(23, 5140413218816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record040_result⟩)
 (.branch 42
 (.leaf ⟨(23, 5140677459968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record041_result⟩)
 (.leaf ⟨(23, 5140685783040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(23, 5140950024192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record043_result⟩)
 (.branch 45
 (.leaf ⟨(23, 5141893808128), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record044_result⟩)
 (.leaf ⟨(23, 5244972961824), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(23, 5267309756672), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record046_result⟩)
 (.leaf ⟨(23, 5275631255808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record047_result⟩))
 (.branch 49
 (.leaf ⟨(23, 5317987409920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record048_result⟩)
 (.leaf ⟨(23, 5363946520832), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(23, 5397182185728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record050_result⟩)
 (.branch 52
 (.leaf ⟨(23, 5397186412544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record051_result⟩)
 (.leaf ⟨(23, 5397297791232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(23, 5397310081024), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record053_result⟩)
 (.branch 55
 (.leaf ⟨(23, 5550383333632), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record054_result⟩)
 (.leaf ⟨(23, 5812370080000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(23, 5829088526336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record056_result⟩)
 (.branch 58
 (.leaf ⟨(23, 5829549948928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record057_result⟩)
 (.leaf ⟨(23, 5863448256512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(23, 5877826387968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record059_result⟩)
 (.branch 61
 (.leaf ⟨(23, 5882771472384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record060_result⟩)
 (.leaf ⟨(23, 5899406213120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(23, 5899414536192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record062_result⟩)
 (.branch 64
 (.leaf ⟨(23, 5899942887936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record063_result⟩)
 (.leaf ⟨(23, 5899951276032), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(23, 6051116187648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record065_result⟩)
 (.branch 67
 (.leaf ⟨(23, 6086531317760), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record066_result⟩)
 (.leaf ⟨(23, 6342202888192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(23, 6378844323840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record068_result⟩)
 (.branch 70
 (.leaf ⟨(23, 6379368808448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record069_result⟩)
 (.leaf ⟨(23, 6379377131520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(23, 6379905483264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record071_result⟩)
 (.leaf ⟨(23, 6379913871360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record072_result⟩))
 (.branch 74
 (.leaf ⟨(23, 6413204062208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record073_result⟩)
 (.leaf ⟨(23, 6425565003776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(23, 6425837307904), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record075_result⟩)
 (.branch 77
 (.leaf ⟨(23, 6442727901184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record076_result⟩)
 (.leaf ⟨(23, 6443017175040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(23, 6443256578048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record078_result⟩)
 (.branch 80
 (.leaf ⟨(23, 6451854573568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record079_result⟩)
 (.leaf ⟨(23, 6516279083008), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(23, 6524600582144), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record081_result⟩)
 (.branch 83
 (.leaf ⟨(23, 6637012221952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record082_result⟩)
 (.leaf ⟨(23, 6637144342528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(23, 6641305026816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record084_result⟩)
 (.branch 86
 (.leaf ⟨(23, 6711570137088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record085_result⟩)
 (.leaf ⟨(23, 6720160038912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(23, 6727198113792), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record087_result⟩)
 (.branch 89
 (.leaf ⟨(23, 6727206436864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record088_result⟩)
 (.leaf ⟨(23, 6752966836480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(23, 6791622623232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record090_result⟩)
 (.branch 92
 (.leaf ⟨(23, 6791630946304), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record091_result⟩)
 (.leaf ⟨(23, 6823834877952), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(23, 6825520930816), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record093_result⟩)
 (.branch 95
 (.leaf ⟨(23, 6839899062272), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record094_result⟩)
 (.leaf ⟨(23, 6840291197184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(23, 6840295424000), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record096_result⟩)
 (.leaf ⟨(23, 6840419092480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record097_result⟩))
 (.branch 99
 (.leaf ⟨(23, 6854969426176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record098_result⟩)
 (.leaf ⟨(23, 6854981715968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00002.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5760 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 5760 5860 :=
  block_of_table results 5760 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0080

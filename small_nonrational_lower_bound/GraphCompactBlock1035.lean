module
prelude
import GraphInputsSix0Part00070Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1035
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 25844063994112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 25844168921344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record001_result⟩)
 (.leaf ⟨(32, 25844168986624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 25844437389312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 25844474970113), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record004_result⟩)
 (.leaf ⟨(32, 25844563607808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 25847675752512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 25847677325328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record007_result⟩)
 (.leaf ⟨(32, 25847694100496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 25848767840257), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 25855883479056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record010_result⟩)
 (.leaf ⟨(32, 25856015599632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 25856261492800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 25856263065616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record013_result⟩)
 (.leaf ⟨(32, 25856279840784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 25857353580545), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 25878927048704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record016_result⟩)
 (.leaf ⟨(32, 25907536597248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 25912091902208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 25913219678208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record019_result⟩)
 (.leaf ⟨(32, 25913722994944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 25916378056720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record021_result⟩)
 (.leaf ⟨(32, 25916395225089), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 25924699555856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record023_result⟩)
 (.leaf ⟨(32, 25924980965377), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 25925701926912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 25947248066560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record026_result⟩)
 (.leaf ⟨(32, 25963077468416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 25963115118592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 25964427870208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record029_result⟩)
 (.leaf ⟨(32, 25964956352512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 25976121856256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 25976524509248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record032_result⟩)
 (.leaf ⟨(32, 25993284814864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 26113556615424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 26113695027264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record035_result⟩)
 (.leaf ⟨(32, 26117847679232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 26130719574032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 26188600901632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record038_result⟩)
 (.leaf ⟨(32, 26220796379136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 26319576500480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 26319576825856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record041_result⟩)
 (.leaf ⟨(32, 26319584888832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 26320096593928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 26320113238536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record044_result⟩)
 (.leaf ⟨(32, 26391607329152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 26391671308672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record046_result⟩)
 (.leaf ⟨(32, 26391673389440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 26391677550976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record048_result⟩)
 (.leaf ⟨(32, 26392080203968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 26393820864896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 26393952985472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record051_result⟩)
 (.leaf ⟨(32, 26393959276736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 26393992306880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 26425998655872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record054_result⟩)
 (.leaf ⟨(32, 26426002817408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 26426269073664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 26426405470400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record057_result⟩)
 (.leaf ⟨(32, 26427089559936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 26427106855296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 26427221680512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record060_result⟩)
 (.leaf ⟨(32, 26427227971776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 26427244486848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 26428349448448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record063_result⟩)
 (.leaf ⟨(32, 26428351513280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 26430530453504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 26431399725440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record066_result⟩)
 (.leaf ⟨(32, 26432644399360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 26432912802048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 26461583515936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record069_result⟩)
 (.leaf ⟨(32, 26461584036128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 26461634365712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record071_result⟩)
 (.leaf ⟨(32, 26462640087328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 26462708105473), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record073_result⟩)
 (.leaf ⟨(32, 26462708138240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 26463748325632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 26465795115280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record076_result⟩)
 (.leaf ⟨(32, 26466868855041), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 26467003089152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 26467007250688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record079_result⟩)
 (.leaf ⟨(32, 26475592990976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 26495196086400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 26498073592064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record082_result⟩)
 (.leaf ⟨(32, 26500238754048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 26500242915584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 26500507156736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record085_result⟩)
 (.leaf ⟨(32, 26501635391616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 26502443843840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 26502504710400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record088_result⟩)
 (.leaf ⟨(32, 26502675579008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 26503242843392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 26503775551744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record091_result⟩)
 (.leaf ⟨(32, 26504658428160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 26512097050880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 26512365486208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record094_result⟩)
 (.leaf ⟨(32, 26512633921536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 26512638083072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record096_result⟩)
 (.leaf ⟨(32, 26519378362624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 26530169295136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record098_result⟩)
 (.leaf ⟨(32, 26571161223424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33620 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33620 33720 :=
  block_of_table results 33620 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1035

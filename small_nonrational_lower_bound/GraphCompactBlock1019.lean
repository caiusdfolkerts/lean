module
prelude
import GraphInputsSix0Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1019
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 20757729542400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 20757754153088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record001_result⟩)
 (.leaf ⟨(32, 20758992584704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 20760032772096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 20763283308800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record004_result⟩)
 (.leaf ⟨(32, 20763349369088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 20770632763520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 20787795099904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record007_result⟩)
 (.leaf ⟨(32, 20787803195520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 20792079419520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 20792228249600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record010_result⟩)
 (.leaf ⟨(32, 20796518973696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 20796634579200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 20800929268480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record013_result⟩)
 (.leaf ⟨(32, 20804958029952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 20822087729408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 20822095825024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record016_result⟩)
 (.leaf ⟨(32, 20822161885312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 20822558247040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 20824291674240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record019_result⟩)
 (.leaf ⟨(32, 20824440504320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 20826372049024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record021_result⟩)
 (.leaf ⟨(32, 20826586939392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 20830877663488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record023_result⟩)
 (.leaf ⟨(32, 20830879809536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 20830927208704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 20833141523200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record026_result⟩)
 (.leaf ⟨(32, 20839250659456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 20894120493184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 20896266928256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record029_result⟩)
 (.leaf ⟨(32, 20896663289984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 20929535623296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 20930858385664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record032_result⟩)
 (.leaf ⟨(32, 20930862547200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 20930862612480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 20930864627968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record035_result⟩)
 (.leaf ⟨(32, 20931267280960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 20935157498112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 20935157563392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record038_result⟩)
 (.leaf ⟨(32, 20935428030528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 20938378711296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 20938649243712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record041_result⟩)
 (.leaf ⟨(32, 20943743238400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 20961747878016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 20963895353472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record044_result⟩)
 (.leaf ⟨(32, 20964297957504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 20965023056128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record046_result⟩)
 (.leaf ⟨(32, 20965023121408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 20965151015168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record048_result⟩)
 (.leaf ⟨(32, 20965155176704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 20965155241984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 20965157257472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record051_result⟩)
 (.leaf ⟨(32, 20965354528896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 20965627011136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 20966298095872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record054_result⟩)
 (.leaf ⟨(32, 20966700748864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 20969311764736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 20969315926272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record057_result⟩)
 (.leaf ⟨(32, 20969315991552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 20969318007040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 20969450127616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record060_result⟩)
 (.leaf ⟨(32, 20969450192896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 20969714368768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 20969714434048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record063_result⟩)
 (.leaf ⟨(32, 20969720660032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 20969787760704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 20970590966016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record066_result⟩)
 (.leaf ⟨(32, 20970861498432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 20978035867904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 20979176706304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record069_result⟩)
 (.leaf ⟨(32, 21007368716289), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 21035015475456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record071_result⟩)
 (.leaf ⟨(32, 21035286007872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 21038035386624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record073_result⟩)
 (.leaf ⟨(32, 21038035451904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 21038438039616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 21038505140288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record076_result⟩)
 (.leaf ⟨(32, 21039578878016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 21046621126912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 21046621192192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record079_result⟩)
 (.leaf ⟨(32, 21046627418176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 21046759538752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 21046826639424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record082_result⟩)
 (.leaf ⟨(32, 21047900377152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 21076086095873), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 21103054438656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record085_result⟩)
 (.leaf ⟨(32, 21107215188224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 21110907273472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 21111047782400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record088_result⟩)
 (.leaf ⟨(32, 21111444144128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 21111452467200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 21115536687360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record091_result⟩)
 (.leaf ⟨(32, 21115939340352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 21119497175296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 21119633522688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record094_result⟩)
 (.leaf ⟨(32, 21119641845760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 21119765643264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record096_result⟩)
 (.leaf ⟨(32, 21119773966336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 21120234307584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record098_result⟩)
 (.leaf ⟨(32, 21123792126208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00054.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32150 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 32150 32250 :=
  block_of_table results 32150 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1019

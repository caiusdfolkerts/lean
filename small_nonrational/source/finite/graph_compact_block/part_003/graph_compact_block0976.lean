module
prelude
import GraphInputsSix0Part00011Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0976
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 4355902145088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 4359391937028), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record001_result⟩)
 (.leaf ⟨(32, 4359391937792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 4359391938048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 4359391969536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record004_result⟩)
 (.leaf ⟨(32, 4359400326144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 4359530283008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 4359660437504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record007_result⟩)
 (.leaf ⟨(32, 4359668760576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 4359802847232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 4359928676868), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record010_result⟩)
 (.leaf ⟨(32, 4360197112320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 4360331329536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 4436309148032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record013_result⟩)
 (.leaf ⟨(32, 4438389522816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 4451270214016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 4472748212608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record016_result⟩)
 (.leaf ⟨(32, 4473788400000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 4477043163520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 4478083350912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record019_result⟩)
 (.leaf ⟨(32, 4485633065344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 4508113666432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record021_result⟩)
 (.leaf ⟨(32, 4508386164992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 4512408617344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record023_result⟩)
 (.leaf ⟨(32, 4512546914560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 4518868730240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 4520868413696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record026_result⟩)
 (.leaf ⟨(32, 4521271066688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 4522401366272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 4522405593088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record029_result⟩)
 (.leaf ⟨(32, 4523418550304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 4581264294144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 4589585793280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record032_result⟩)
 (.leaf ⟨(32, 4589856325696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 4590458142976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 4592003809312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record035_result⟩)
 (.leaf ⟨(32, 4691791495360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 4720852828192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 4722427789312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record038_result⟩)
 (.leaf ⟨(32, 4727020552448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 4727026843712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 4728157143296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record041_result⟩)
 (.leaf ⟨(32, 4728161370112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 4728169693184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 4735372394752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record044_result⟩)
 (.leaf ⟨(32, 4795947565184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 4803994322176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record046_result⟩)
 (.leaf ⟨(32, 4804527030528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 4899023634560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record048_result⟩)
 (.leaf ⟨(32, 5025674371456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 5026730942848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 5026802139392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record051_result⟩)
 (.leaf ⟨(32, 5035593400352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 5060037804288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 5064584397056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record054_result⟩)
 (.leaf ⟨(32, 5073174298880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 5073174364160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 5095519518976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record057_result⟩)
 (.leaf ⟨(32, 5102983782592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 5103841018112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 5104105259264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record060_result⟩)
 (.leaf ⟨(32, 5104111550528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 5104178659360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 5106282037504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record063_result⟩)
 (.leaf ⟨(32, 5106286264320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 5120769229056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 5123505979648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record066_result⟩)
 (.leaf ⟨(32, 5133169656064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 5136892133384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 5137326344384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record069_result⟩)
 (.leaf ⟨(32, 5137336156416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 5138477515008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record071_result⟩)
 (.leaf ⟨(32, 5138481741824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 5139746275584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record073_result⟩)
 (.leaf ⟨(32, 5140140720384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 5140144881920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 5140144947200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record076_result⟩)
 (.leaf ⟨(32, 5140148913408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 5140413219072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 5140545275136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record079_result⟩)
 (.leaf ⟨(32, 5140547551232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 5140677460224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 5140685783041), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record082_result⟩)
 (.leaf ⟨(32, 5140685848576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 5140941636352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 5140950024704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record085_result⟩)
 (.leaf ⟨(32, 5140950089728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 5141759557888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 5141759623168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record088_result⟩)
 (.leaf ⟨(32, 5176253489408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 5241275777280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 5241282068544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record091_result⟩)
 (.leaf ⟨(32, 5241349177376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 5258203988224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 5260944900352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record094_result⟩)
 (.leaf ⟨(32, 5260944965632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 5267049742592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record096_result⟩)
 (.leaf ⟨(32, 5268358332672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 5268358397952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record098_result⟩)
 (.leaf ⟨(32, 5270340174080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00011.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (27886 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 27886 27986 :=
  block_of_table results 27886 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0976

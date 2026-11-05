module
prelude
import GraphInputsSix0Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1005
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 16494981906448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 16494994458880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record001_result⟩)
 (.leaf ⟨(32, 16494998392960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 16494998421520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 16495109804288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record004_result⟩)
 (.leaf ⟨(32, 16495116107792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 16495132622864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 16495384510480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record007_result⟩)
 (.leaf ⟨(32, 16496071869056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 16496076030208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 16496076095488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record010_result⟩)
 (.leaf ⟨(32, 16496203989248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 16496208150784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 16496208216064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record013_result⟩)
 (.leaf ⟨(32, 16496210231552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 16496310882560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 16496441081872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record016_result⟩)
 (.leaf ⟨(32, 16496713535552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 16499934760976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 16501367703808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record019_result⟩)
 (.leaf ⟨(32, 16501373747216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 16501826936848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record021_result⟩)
 (.leaf ⟨(32, 16502552006912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 16502643294464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record023_result⟩)
 (.leaf ⟨(32, 16502649536768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 16502649602048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 16502684127488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record026_result⟩)
 (.leaf ⟨(32, 16502883508240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 16502911697152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 16502911762432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record029_result⟩)
 (.leaf ⟨(32, 16502913777920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 16502913843200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 16502921109568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record032_result⟩)
 (.leaf ⟨(32, 16502954659904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 16504095510544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 16511269867776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record035_result⟩)
 (.leaf ⟨(32, 16527193899024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 16527328100368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 16527596503056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record038_result⟩)
 (.leaf ⟨(32, 16531606145040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 16531619119360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 16531622789648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record041_result⟩)
 (.leaf ⟨(32, 16531623280896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 16531623346176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 16531626922240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record044_result⟩)
 (.leaf ⟨(32, 16532147013648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 16532675690752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record046_result⟩)
 (.leaf ⟨(32, 16532679852288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 16532679917568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record048_result⟩)
 (.leaf ⟨(32, 16532809777408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 16532818165760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 16533210300672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record051_result⟩)
 (.leaf ⟨(32, 16533220753409), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 16535918231808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 16535918297088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record054_result⟩)
 (.leaf ⟨(32, 16535919792384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 16536182472960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 16536182538240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record057_result⟩)
 (.leaf ⟨(32, 16536184033536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 16536190324800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 16536307763216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record060_result⟩)
 (.leaf ⟨(32, 16537111035904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 16537371050240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 16537381502977), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record063_result⟩)
 (.leaf ⟨(32, 16540322300160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 16540590702848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 16540602732544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record066_result⟩)
 (.leaf ⟨(32, 16545696776192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 16567102406912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 16567110795264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record069_result⟩)
 (.leaf ⟨(32, 16567568990464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 16567580499968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record071_result⟩)
 (.leaf ⟨(32, 16568642208000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 16568654237696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record073_result⟩)
 (.leaf ⟨(32, 16571263156480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 16571271544832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 16571403665408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record076_result⟩)
 (.leaf ⟨(32, 16571461337344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 16571663679744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 16571667906560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record079_result⟩)
 (.leaf ⟨(32, 16571729740032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 16571741249536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 16572534554880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record082_result⟩)
 (.leaf ⟨(32, 16572802957568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 16572814987264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 16575084634368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record085_result⟩)
 (.leaf ⟨(32, 16579989405696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 16602468778240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 16603005648896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record088_result⟩)
 (.leaf ⟨(32, 16603013971968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 16606629527808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 16606902157312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record091_result⟩)
 (.leaf ⟨(32, 16607166398464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 16607174721536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 16609443840768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record094_result⟩)
 (.leaf ⟨(32, 16621592674560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 16630205988880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record096_result⟩)
 (.leaf ⟨(32, 16630675693584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 16632403658768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record098_result⟩)
 (.leaf ⟨(32, 16632420303376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00040.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30786 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30786 30886 :=
  block_of_table results 30786 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1005

module
prelude
import GraphInputsRow24Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0146
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 16159547129856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 16176264511488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record001_result⟩)
 (.leaf ⟨(24, 16365302906880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 16398588116992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record003_result⟩)
 (.leaf ⟨(24, 16432831201280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 16432880746496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record005_result⟩)
 (.leaf ⟨(24, 16494042308864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 16494977683712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 16494981877888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record008_result⟩)
 (.leaf ⟨(24, 16494981906448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 16494998392960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record010_result⟩)
 (.leaf ⟨(24, 16494998421520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 16495109804288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record012_result⟩)
 (.leaf ⟨(24, 16496203989248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 16496208150784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 16496208216064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record015_result⟩)
 (.leaf ⟨(24, 16501367703808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 16501826936848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record017_result⟩)
 (.leaf ⟨(24, 16502643294464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 16502649536768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record019_result⟩)
 (.leaf ⟨(24, 16502649602048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(24, 16502684127488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 16502913843200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record022_result⟩)
 (.leaf ⟨(24, 16504095510544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 16511269867776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record024_result⟩)
 (.leaf ⟨(24, 16527193899024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 16531606145040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record026_result⟩)
 (.leaf ⟨(24, 16531619119360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(24, 16531623346176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 16532679852288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record029_result⟩)
 (.leaf ⟨(24, 16532679917568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(24, 16532809777408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record031_result⟩)
 (.leaf ⟨(24, 16532818165760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record032_result⟩))
 (.branch 34
 (.leaf ⟨(24, 16533210300672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record033_result⟩)
 (.leaf ⟨(24, 16536182472960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(24, 16536182538240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 16536184033536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record036_result⟩)
 (.leaf ⟨(24, 16536190324800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(24, 16536307763216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record038_result⟩)
 (.leaf ⟨(24, 16537111035904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record039_result⟩))
 (.branch 41
 (.leaf ⟨(24, 16537371050240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record040_result⟩)
 (.leaf ⟨(24, 16540322300160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(24, 16540590702848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record042_result⟩)
 (.branch 44
 (.leaf ⟨(24, 16540602732544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record043_result⟩)
 (.leaf ⟨(24, 16545696776192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(24, 16571403665408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record045_result⟩)
 (.leaf ⟨(24, 16571461337344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record046_result⟩))
 (.branch 48
 (.leaf ⟨(24, 16571663679744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record047_result⟩)
 (.leaf ⟨(24, 16571667906560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(24, 16571729740032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record049_result⟩)
 (.branch 51
 (.leaf ⟨(24, 16571741249536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record050_result⟩)
 (.leaf ⟨(24, 16572534554880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(24, 16572802957568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record052_result⟩)
 (.leaf ⟨(24, 16572814987264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record053_result⟩))
 (.branch 55
 (.leaf ⟨(24, 16579989405696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record054_result⟩)
 (.leaf ⟨(24, 16606902157312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00030.record055_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9182 + i))) 0 56 :=
  interval_of_check _ 0 56 (by decide +kernel)

public theorem complete : Block 9182 9238 :=
  block_of_table results 9182 56 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0146

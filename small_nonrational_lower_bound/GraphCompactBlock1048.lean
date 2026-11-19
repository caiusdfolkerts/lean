module
prelude
import GraphInputsSix0Part00083Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1048
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 27
 (.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 32025986732096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 32026600210688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record001_result⟩)
 (.leaf ⟨(32, 32027077263360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 32043780079616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 32044316884992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record004_result⟩)
 (.leaf ⟨(32, 32058795688192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 32059272740864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 32059313897728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record007_result⟩)
 (.leaf ⟨(32, 32074916708608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 32075371003904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record009_result⟩)
 (.leaf ⟨(32, 32076493488704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 32076512362496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record011_result⟩)
 (.leaf ⟨(32, 32078037139712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(32, 32078171406336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record013_result⟩)
 (.branch 15
 (.leaf ⟨(32, 32078179729408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record014_result⟩)
 (.leaf ⟨(32, 32078574010368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(32, 32078708081152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record016_result⟩)
 (.leaf ⟨(32, 32162959069248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record017_result⟩))
 (.branch 19
 (.leaf ⟨(32, 32163157250112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record018_result⟩)
 (.leaf ⟨(32, 32163421491264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(32, 32164039131392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record020_result⟩)
 (.branch 22
 (.leaf ⟨(32, 32164049600512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record021_result⟩)
 (.leaf ⟨(32, 32164247781376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(32, 32165173661728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record023_result⟩)
 (.leaf ⟨(32, 32167359447296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record024_result⟩))
 (.branch 26
 (.leaf ⟨(32, 32172629098496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record025_result⟩)
 (.leaf ⟨(32, 32196234608896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record026_result⟩))))))
 (.branch 41
 (.branch 34
 (.branch 30
 (.branch 28
 (.leaf ⟨(32, 32196245078016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record027_result⟩)
 (.branch 29
 (.leaf ⟨(32, 32196443258880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record028_result⟩)
 (.leaf ⟨(32, 32196484415744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(32, 32199101383232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record030_result⟩)
 (.leaf ⟨(32, 32200649146368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record031_result⟩))
 (.branch 33
 (.leaf ⟨(32, 32203765727488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record032_result⟩)
 (.leaf ⟨(32, 32204220022784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record033_result⟩))))
 (.branch 37
 (.branch 35
 (.leaf ⟨(32, 32205342507584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 32221985652736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record035_result⟩)
 (.leaf ⟨(32, 32232861401088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(32, 32232869724160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record037_result⟩)
 (.leaf ⟨(32, 32234871488768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record038_result⟩))
 (.branch 40
 (.leaf ⟨(32, 32235609661440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record039_result⟩)
 (.leaf ⟨(32, 32235911676160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record040_result⟩)))))
 (.branch 48
 (.branch 44
 (.branch 42
 (.leaf ⟨(32, 32236682878976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record041_result⟩)
 (.branch 43
 (.leaf ⟨(32, 32266097065984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record042_result⟩)
 (.leaf ⟨(32, 32266105389056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(32, 32268107153664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record044_result⟩)
 (.leaf ⟨(32, 32268425166848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record045_result⟩))
 (.branch 47
 (.leaf ⟨(32, 32268894871552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record046_result⟩)
 (.leaf ⟨(32, 32270236942592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record047_result⟩))))
 (.branch 51
 (.branch 49
 (.leaf ⟨(32, 32271042085376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record048_result⟩)
 (.branch 50
 (.leaf ⟨(32, 32299321147392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record049_result⟩)
 (.leaf ⟨(32, 32300394364928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record050_result⟩)))
 (.branch 53
 (.branch 52
 (.leaf ⟨(32, 32300402491648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record051_result⟩)
 (.leaf ⟨(32, 32300856786944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record052_result⟩))
 (.branch 54
 (.leaf ⟨(32, 32301979271744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record053_result⟩)
 (.leaf ⟨(32, 32332597969152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00083.record054_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34727 + i))) 0 55 :=
  interval_of_check _ 0 55 (by decide +kernel)

public theorem complete : Block 34727 34782 :=
  block_of_table results 34727 55 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1048

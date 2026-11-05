module
prelude
import GraphInputsRow26Part00072Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0388
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 32196234608896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 32196245078016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record001_result⟩)
 (.leaf ⟨(26, 32196443258880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(26, 32196484415744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record003_result⟩)
 (.branch 5
 (.leaf ⟨(26, 32200649146368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record004_result⟩)
 (.leaf ⟨(26, 32203765727488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(26, 32204220022784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 32221985652736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record007_result⟩)
 (.leaf ⟨(26, 32232861401088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(26, 32232869724160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record009_result⟩)
 (.branch 11
 (.leaf ⟨(26, 32234871488768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record010_result⟩)
 (.leaf ⟨(26, 32235609661440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(26, 32235911676160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 32236682878976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record013_result⟩)
 (.leaf ⟨(26, 32266097065984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(26, 32266105389056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 32268425166848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record016_result⟩)
 (.leaf ⟨(26, 32268894871552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(26, 32299321147392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 32300394364928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record019_result⟩)
 (.leaf ⟨(26, 32300402491648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 32300856786944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record021_result⟩)
 (.leaf ⟨(26, 32301979271744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 32332597969152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record023_result⟩)
 (.leaf ⟨(26, 32332606357504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00072.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17393 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 17393 17418 :=
  block_of_table results 17393 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0388

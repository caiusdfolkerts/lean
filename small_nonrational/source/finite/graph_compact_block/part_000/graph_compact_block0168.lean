module
prelude
import GraphInputsRow24Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0168
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 19684406607872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_result⟩)
 (.leaf ⟨(24, 19692720816128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 19693096435968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record002_result⟩)
 (.leaf ⟨(24, 19693108725760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 19697284169728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record004_result⟩)
 (.leaf ⟨(24, 19697391386880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 19697401595904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 19701686076160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record007_result⟩)
 (.leaf ⟨(24, 19705723095040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 19710410228288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record009_result⟩)
 (.leaf ⟨(24, 19718195003648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 19718329270272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 19718337593344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record012_result⟩)
 (.leaf ⟨(24, 19718731874304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 19718865945088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record014_result⟩)
 (.leaf ⟨(24, 19724792561920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 19724800950272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 19724924682496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record017_result⟩)
 (.leaf ⟨(24, 19724933070848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 19725040288000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record019_result⟩)
 (.leaf ⟨(24, 19725193085184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 19725197312000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record021_result⟩)
 (.leaf ⟨(24, 19725203554304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 19725308690688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record023_result⟩)
 (.leaf ⟨(24, 19725320980480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 19725442892032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record025_result⟩)
 (.branch 27
 (.leaf ⟨(24, 19727079505920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record026_result⟩)
 (.leaf ⟨(24, 19727120662784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 19727343747072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record028_result⟩)
 (.leaf ⟨(24, 19727389065472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 19727401355264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 19729607622656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record031_result⟩)
 (.leaf ⟨(24, 19731636617216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(24, 19731642859520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record033_result⟩)
 (.leaf ⟨(24, 19731684016384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record034_result⟩))
 (.branch 36
 (.leaf ⟨(24, 19731694225408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 19733898330880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record036_result⟩)
 (.leaf ⟨(24, 19739883603968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9776 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 9776 9814 :=
  block_of_table results 9776 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0168

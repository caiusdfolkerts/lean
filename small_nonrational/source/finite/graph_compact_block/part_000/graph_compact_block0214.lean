module
prelude
import GraphInputsRow24Part00098Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0214
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25327982088448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record000_result⟩)
 (.leaf ⟨(24, 25327984754688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25327988379712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 25328105818128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record003_result⟩)
 (.leaf ⟨(24, 25328772858112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 25328772923392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record005_result⟩)
 (.leaf ⟨(24, 25329041326080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 25329179557889), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 25332279689280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record008_result⟩)
 (.leaf ⟨(24, 25332281249856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 25332398688272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record010_result⟩)
 (.leaf ⟨(24, 25333472428033), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 25340720187408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 25340865429568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record013_result⟩)
 (.leaf ⟨(24, 25341793927169), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 25359790178560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 25359794340096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record016_result⟩)
 (.leaf ⟨(24, 25359794405376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 25359797981440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 25359930102016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record019_result⟩)
 (.leaf ⟨(24, 25362076082176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 25362076537088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record021_result⟩)
 (.leaf ⟨(24, 25362340778240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 25362344484864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 25363132653568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record024_result⟩)
 (.leaf ⟨(24, 25364601012480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 25366633648384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record026_result⟩)
 (.leaf ⟨(24, 25366639419456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 25366639435776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record028_result⟩)
 (.branch 30
 (.leaf ⟨(24, 25366639939648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record029_result⟩)
 (.leaf ⟨(24, 25366691317776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(24, 25367722082560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record031_result⟩)
 (.leaf ⟨(24, 25367765057537), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record032_result⟩))
 (.branch 34
 (.leaf ⟨(24, 25374880696336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record033_result⟩)
 (.branch 35
 (.leaf ⟨(24, 25375012816912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record034_result⟩)
 (.leaf ⟨(24, 25375225159744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(24, 25375225176064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 25375954436097), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record037_result⟩)
 (.leaf ⟨(24, 25376086556673), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(24, 25384901951488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record039_result⟩)
 (.branch 41
 (.leaf ⟨(24, 25398964453376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record040_result⟩)
 (.leaf ⟨(24, 25428515361024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00098.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10903 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 10903 10945 :=
  block_of_table results 10903 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0214

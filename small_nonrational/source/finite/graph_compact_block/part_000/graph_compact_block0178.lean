module
prelude
import GraphInputsRow24Part00062Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0178
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 22851929800960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record000_result⟩)
 (.leaf ⟨(24, 22851954411648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 22853265145856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 22859227398400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record003_result⟩)
 (.leaf ⟨(24, 22859495801088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 22859506270208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record005_result⟩)
 (.leaf ⟨(24, 22862783086848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 22866517035136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 22867817300224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record008_result⟩)
 (.leaf ⟨(24, 22867827769344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 22869761491200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record010_result⟩)
 (.leaf ⟨(24, 22869769879552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 22870298198656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 22876407267328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record013_result⟩)
 (.leaf ⟨(24, 22876944072704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 22924660637952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 22925197508608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record016_result⟩)
 (.leaf ⟨(24, 22925205831680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(24, 22928821387520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record018_result⟩)
 (.branch 20
 (.leaf ⟨(24, 22929094017024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record019_result⟩)
 (.leaf ⟨(24, 22929358258176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062.record020_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10169 + i))) 0 21 :=
  interval_of_check _ 0 21 (by decide +kernel)

public theorem complete : Block 10169 10190 :=
  block_of_table results 10169 21 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0178

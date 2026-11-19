module
prelude
import GraphInputsRow24Part00112Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0228
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27687105085440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record000_result⟩)
 (.leaf ⟨(24, 27689688776960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27689756983296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27689765306368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record003_result⟩)
 (.leaf ⟨(24, 27690225647616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 27697508057344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 27697786929152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record006_result⟩)
 (.leaf ⟨(24, 27704226234368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 27712547733504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 27721969238016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record009_result⟩)
 (.leaf ⟨(24, 27721977561088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 27730743722240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record011_result⟩)
 (.leaf ⟨(24, 27730752110592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 27730859327744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 27731012124928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record014_result⟩)
 (.leaf ⟨(24, 27731016351744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 27731022594048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 27731127730432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record017_result⟩)
 (.leaf ⟨(24, 27731140020224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 27731261931776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 27735426662400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record020_result⟩)
 (.leaf ⟨(24, 27737461899264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11226 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 11226 11248 :=
  block_of_table results 11226 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0228

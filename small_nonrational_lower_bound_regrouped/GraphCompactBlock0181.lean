module
prelude
import GraphInputsRow24Part00065Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0181
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23245641285888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record000_result⟩)
 (.leaf ⟨(24, 23245647528192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23245647593472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 23246050181184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record003_result⟩)
 (.leaf ⟨(24, 23246051221568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 23247124959296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 23267517726976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record006_result⟩)
 (.leaf ⟨(24, 23267526115328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 23280402579712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 23280410968064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record009_result⟩)
 (.leaf ⟨(24, 23280468640000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 23281551802369), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record011_result⟩)
 (.leaf ⟨(24, 23282080350464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 23282617221120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 23282625544192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record014_result⟩)
 (.leaf ⟨(24, 23284160725248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 23284301234176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 23284697595904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record017_result⟩)
 (.leaf ⟨(24, 23284705918976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 23284838039552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 23299729981696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record020_result⟩)
 (.leaf ⟨(24, 23314769657856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00065.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10251 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 10251 10273 :=
  block_of_table results 10251 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0181

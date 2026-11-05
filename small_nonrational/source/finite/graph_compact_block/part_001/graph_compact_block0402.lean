module
prelude
import GraphInputsRow26Part00086Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0402
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 34746856112128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record000_result⟩)
 (.leaf ⟨(26, 34747359363072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 34763465294340), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record002_result⟩)
 (.leaf ⟨(26, 34763465428992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 34763482595328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record004_result⟩)
 (.leaf ⟨(26, 34763515625472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 34764539166720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record006_result⟩)
 (.leaf ⟨(26, 34875134576896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 34875151548416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record008_result⟩)
 (.leaf ⟨(26, 34875688353792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 34892314445824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record010_result⟩)
 (.leaf ⟨(26, 35115652745224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 35115669522432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record012_result⟩)
 (.leaf ⟨(26, 35115669782528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 35150012483584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record014_result⟩)
 (.leaf ⟨(26, 35150029389824), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17657 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 17657 17673 :=
  block_of_table results 17657 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0402

module
prelude
import GraphInputsRow24Part00173Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0289
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 34746856112128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 34747359363072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record001_result⟩)
 (.leaf ⟨(24, 34763465294340), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 34763465428992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 34763482595328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record004_result⟩)
 (.leaf ⟨(24, 34763515625472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 34764539166720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 34875134576896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record007_result⟩)
 (.leaf ⟨(24, 34875151548416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 34875688353792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record009_result⟩)
 (.leaf ⟨(24, 34892314445824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 35150012483584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record011_result⟩)
 (.leaf ⟨(24, 35150029389824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00173.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12117 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 12117 12130 :=
  block_of_table results 12117 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0289

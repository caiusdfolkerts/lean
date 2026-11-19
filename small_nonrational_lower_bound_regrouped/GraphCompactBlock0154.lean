module
prelude
import GraphInputsRow24Part00038Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0154
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 17232893575168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 17235703922944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record001_result⟩)
 (.leaf ⟨(24, 17235741573120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 17236509065728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 17236509589504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record004_result⟩)
 (.leaf ⟨(24, 17237054324736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 17244335636480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 17244864118784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record007_result⟩)
 (.leaf ⟨(24, 17282969436416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 17291563565056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 17292100370432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record010_result⟩)
 (.leaf ⟨(24, 17300149305344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9411 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 9411 9423 :=
  block_of_table results 9411 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0154

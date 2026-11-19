module
prelude
import GraphInputsRow24Part00078Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0194
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 24379711832320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record000_result⟩)
 (.leaf ⟨(24, 24380114485312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 24380794994689), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 24383808667648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record003_result⟩)
 (.leaf ⟨(24, 24383816990720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 24383940788224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 24383949111296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record006_result⟩)
 (.leaf ⟨(24, 24384409452544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 24384477593600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 24387967271168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record009_result⟩)
 (.leaf ⟨(24, 24388101537792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 24388109860864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record011_result⟩)
 (.leaf ⟨(24, 24388504141824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 24388570202112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 24391690764288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record014_result⟩)
 (.leaf ⟨(24, 24398973174016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 24399241576704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 24399252045824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record017_result⟩)
 (.leaf ⟨(24, 24405691351040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 24414012850176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 24415884574976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record020_result⟩)
 (.leaf ⟨(24, 24416020922368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00078.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10578 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 10578 10600 :=
  block_of_table results 10578 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0194

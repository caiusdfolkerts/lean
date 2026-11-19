module
prelude
import GraphInputsRow24Part00158Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0274
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 32789458059776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record000_result⟩)
 (.leaf ⟨(24, 32804960342048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32804977516544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record002_result⟩)
 (.leaf ⟨(24, 32805011587072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 32806034087936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record004_result⟩)
 (.leaf ⟨(24, 32806101188608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 32813567213824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32813835681792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record007_result⟩)
 (.leaf ⟨(24, 32813844004864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00158.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11956 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 11956 11965 :=
  block_of_table results 11956 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0274

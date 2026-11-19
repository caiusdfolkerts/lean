module
prelude
import GraphInputsRow24Part00094Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0210
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 25153788446720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record000_result⟩)
 (.leaf ⟨(24, 25154952364800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 25155355017792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record002_result⟩)
 (.leaf ⟨(24, 25156902780928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 25160019362048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record004_result⟩)
 (.leaf ⟨(24, 25160029571072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 25160128661504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 25160472600640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record007_result⟩)
 (.leaf ⟨(24, 25160473657344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10820 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 10820 10829 :=
  block_of_table results 10820 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0210

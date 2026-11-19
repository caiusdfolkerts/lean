module
prelude
import GraphInputsRow24Part00172Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0288
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 34737712824576), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 34738790268928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record001_result⟩)
 (.leaf ⟨(24, 34739062833152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 34739574800384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 34746302791680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record004_result⟩)
 (.leaf ⟨(24, 34746839597056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12111 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 12111 12117 :=
  block_of_table results 12111 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0288

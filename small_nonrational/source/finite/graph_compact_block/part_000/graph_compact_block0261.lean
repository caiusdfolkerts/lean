module
prelude
import GraphInputsRow24Part00145Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0261
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 32232861401088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00145.record000_result⟩)
 (.leaf ⟨(24, 32232869724160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00145.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32234871488768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00145.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 32235609661440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00145.record003_result⟩)
 (.leaf ⟨(24, 32235911676160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00145.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11833 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 11833 11838 :=
  block_of_table results 11833 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0261

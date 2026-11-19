module
prelude
import GraphInputsRow24Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0149
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 16748770230272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record000_result⟩)
 (.leaf ⟨(24, 16752658415616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 16757091729408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record002_result⟩)
 (.leaf ⟨(24, 16757620211712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 16767638667280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record004_result⟩)
 (.leaf ⟨(24, 16767846211600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 16769838417936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record006_result⟩)
 (.leaf ⟨(24, 16776211662864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9275 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 9275 9283 :=
  block_of_table results 9275 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0149

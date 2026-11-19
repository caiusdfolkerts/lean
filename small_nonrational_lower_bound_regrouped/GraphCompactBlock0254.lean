module
prelude
import GraphInputsRow24Part00138Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0254
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 31761317765376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31763465306112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record001_result⟩)
 (.leaf ⟨(24, 31763539689472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 31764002111488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 31778497634304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record004_result⟩)
 (.leaf ⟨(24, 31778564734976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11740 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 11740 11746 :=
  block_of_table results 11740 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0254

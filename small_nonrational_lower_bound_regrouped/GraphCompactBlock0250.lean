module
prelude
import GraphInputsRow24Part00134Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0250
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 31570191777792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31570266161152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record001_result⟩)
 (.leaf ⟨(24, 31570728583168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31578768081152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record003_result⟩)
 (.leaf ⟨(24, 31579040710656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31579304951808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record005_result⟩)
 (.leaf ⟨(24, 31579313274880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00134.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11699 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 11699 11706 :=
  block_of_table results 11699 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0250

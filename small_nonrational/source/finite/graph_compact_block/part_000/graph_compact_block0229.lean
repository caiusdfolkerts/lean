module
prelude
import GraphInputsRow24Part00113Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0229
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27737503056128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record000_result⟩)
 (.leaf ⟨(24, 27745824555264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27746047639552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 27748441522752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record003_result⟩)
 (.leaf ⟨(24, 27756226298112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 27756360564736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record005_result⟩)
 (.leaf ⟨(24, 27756368887808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 27756763168768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27756897239552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record008_result⟩)
 (.leaf ⟨(24, 27783240646656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00113.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11248 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 11248 11258 :=
  block_of_table results 11248 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0229

module
prelude
import GraphInputsRow24Part00163Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0279
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 33545171509504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record000_result⟩)
 (.leaf ⟨(24, 33546245247232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 33574049349632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record002_result⟩)
 (.leaf ⟨(24, 33578342219776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 33578457239808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record004_result⟩)
 (.leaf ⟨(24, 33579530715904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 33612699803904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record006_result⟩)
 (.leaf ⟨(24, 33612749869312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00163.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12014 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 12014 12022 :=
  block_of_table results 12014 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0279

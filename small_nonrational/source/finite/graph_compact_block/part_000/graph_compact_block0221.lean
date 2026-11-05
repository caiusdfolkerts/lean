module
prelude
import GraphInputsRow24Part00105Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0221
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 25963115118592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 25964427870208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_result⟩)
 (.leaf ⟨(24, 25964956352512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 25976121856256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 25976524509248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record004_result⟩)
 (.leaf ⟨(24, 25993284814864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 26113556615424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 26113695027264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record007_result⟩)
 (.leaf ⟨(24, 26130719574032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 26188600901632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 26220796379136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record010_result⟩)
 (.leaf ⟨(24, 26319584888832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11051 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 11051 11063 :=
  block_of_table results 11051 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0221

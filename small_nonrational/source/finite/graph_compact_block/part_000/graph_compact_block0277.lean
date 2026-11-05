module
prelude
import GraphInputsRow24Part00161Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0277
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 33126320455680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record000_result⟩)
 (.leaf ⟨(24, 33158515933184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 33158557090048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 33167415181888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record003_result⟩)
 (.leaf ⟨(24, 33195132256256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 33197212631040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record005_result⟩)
 (.leaf ⟨(24, 33204426776832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 33205534130176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 33206070935552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record008_result⟩)
 (.leaf ⟨(24, 33206574317568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11993 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 11993 12003 :=
  block_of_table results 11993 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0277

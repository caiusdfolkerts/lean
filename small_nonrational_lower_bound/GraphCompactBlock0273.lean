module
prelude
import GraphInputsRow24Part00157Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0273
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(24, 32788334518272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record000_result⟩)
 (.leaf ⟨(24, 32788335558656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32788351033344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record002_result⟩)
 (.leaf ⟨(24, 32788854219008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11952 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 11952 11956 :=
  block_of_table results 11952 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0273

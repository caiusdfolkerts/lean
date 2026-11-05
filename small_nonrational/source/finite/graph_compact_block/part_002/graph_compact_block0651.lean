module
prelude
import GraphInputsRow29Part00217Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0651
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 29596619637252), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00217.record000_result⟩)
 (.leaf ⟨(29, 29690213466112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00217.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29692359901184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00217.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 29692384542976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00217.record003_result⟩)
 (.leaf ⟨(29, 29692756262912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00217.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23116 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23116 23121 :=
  block_of_table results 23116 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0651

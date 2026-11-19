module
prelude
import GraphInputsRow29Part00072Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0506
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 12512519061504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072.record000_result⟩)
 (.leaf ⟨(29, 12545754726400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12546270855168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12554600448000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072.record003_result⟩)
 (.leaf ⟨(29, 12577830633728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21497 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 21497 21502 :=
  block_of_table results 21497 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0506

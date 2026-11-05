module
prelude
import GraphInputsRow29Part00066Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0500
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 12021882028032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record000_result⟩)
 (.leaf ⟨(29, 12098258080000), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12100338454784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12134763266304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record003_result⟩)
 (.leaf ⟨(29, 12134771654656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00066.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21427 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 21427 21432 :=
  block_of_table results 21427 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0500

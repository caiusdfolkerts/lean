module
prelude
import GraphInputsRow29Part00252Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0686
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 32351841304576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252.record000_result⟩)
 (.leaf ⟨(29, 32475598356480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 32476135161856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252.record002_result⟩)
 (.leaf ⟨(29, 32488344846336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00252.record003_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23381 + i))) 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)

public theorem complete : Block 23381 23385 :=
  block_of_table results 23381 4 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0686

module
prelude
import GraphInputsRow29Part00268Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0702
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 33613831733248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00268.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 33682416992256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00268.record001_result⟩)
 (.leaf ⟨(29, 33685463171072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00268.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23450 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23450 23453 :=
  block_of_table results 23450 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0702

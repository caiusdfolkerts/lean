module
prelude
import GraphInputsRow29Part00280Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0714
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 1
 (.leaf ⟨(29, 34225001086976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00280.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 34228742000896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00280.record001_result⟩)
 (.leaf ⟨(29, 34239496593472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00280.record002_result⟩)))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23490 + i))) 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)

public theorem complete : Block 23490 23493 :=
  block_of_table results 23490 3 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0714

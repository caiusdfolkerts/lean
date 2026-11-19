module
prelude
import GraphInputsRow29Part00244Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0678
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 31842955689984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244.record000_result⟩)
 (.leaf ⟨(29, 31891509018880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 31891777421568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 31891788931072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244.record003_result⟩)
 (.leaf ⟨(29, 31896072372480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23341 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 23341 23346 :=
  block_of_table results 23341 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0678

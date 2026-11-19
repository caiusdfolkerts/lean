module
prelude
import GraphInputsRow31Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0832
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 8333587185664), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record000_result⟩)
 (.leaf ⟨(31, 8334115602944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 8334123991040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record002_result⟩)
 (.leaf ⟨(31, 8340826624256), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 8478810701824), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record004_result⟩)
 (.leaf ⟨(31, 8525795885056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 8534100152576), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_result⟩)
 (.leaf ⟨(31, 8538797903872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25830 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25830 25838 :=
  block_of_table results 25830 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0832

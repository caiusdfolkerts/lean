module
prelude
import GraphInputsRow29Part00040Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0474
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 7578002161664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 7585717551680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record001_result⟩)
 (.leaf ⟨(29, 7585718616064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 7593653469440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 7593657696256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record004_result⟩)
 (.leaf ⟨(29, 7593665759232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00040.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21049 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 21049 21055 :=
  block_of_table results 21049 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0474

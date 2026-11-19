module
prelude
import GraphInputsRow29Part00112Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0546
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 19564259704832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00112.record000_result⟩)
 (.leaf ⟨(29, 19572837057152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00112.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 19573914992640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00112.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 19586326233344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00112.record003_result⟩)
 (.leaf ⟨(29, 19588947443712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00112.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22144 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 22144 22149 :=
  block_of_table results 22144 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0546

module
prelude
import GraphInputsRow29Part00190Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0624
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 27671000055808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 27673145377536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record001_result⟩)
 (.leaf ⟨(29, 27685428412672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 27747774693376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 27748443619328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record004_result⟩)
 (.leaf ⟨(29, 27756368756736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22940 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22940 22946 :=
  block_of_table results 22940 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0624

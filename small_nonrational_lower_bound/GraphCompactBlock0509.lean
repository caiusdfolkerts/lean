module
prelude
import GraphInputsRow29Part00075Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0509
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(29, 12578483109888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075.record000_result⟩)
 (.leaf ⟨(29, 12582106857728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 12582912000512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 12584455831552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075.record003_result⟩)
 (.leaf ⟨(29, 12584810971136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21508 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 21508 21513 :=
  block_of_table results 21508 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0509

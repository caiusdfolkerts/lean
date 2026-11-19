module
prelude
import GraphInputsRow29Part00169Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0603
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 25659409694720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 25702227263744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record001_result⟩)
 (.leaf ⟨(29, 25704441905152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 25704978710528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 25706522279936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record004_result⟩)
 (.leaf ⟨(29, 25706662723584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00169.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22761 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22761 22767 :=
  block_of_table results 22761 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0603

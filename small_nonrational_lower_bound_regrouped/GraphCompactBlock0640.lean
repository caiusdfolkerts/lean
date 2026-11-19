module
prelude
import GraphInputsRow29Part00206Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0640
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29140856111104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record000_result⟩)
 (.leaf ⟨(29, 29140951007360), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29141085208704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record002_result⟩)
 (.leaf ⟨(29, 29144306421888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 29146923696384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record004_result⟩)
 (.leaf ⟨(29, 29146935726080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 29147027013632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 29147067846656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record007_result⟩)
 (.leaf ⟨(29, 29147293302912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23044 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23044 23053 :=
  block_of_table results 23044 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0640

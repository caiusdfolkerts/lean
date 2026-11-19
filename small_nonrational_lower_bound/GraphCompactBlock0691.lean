module
prelude
import GraphInputsRow29Part00257Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0691
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 32660080558080), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 32660609040384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record001_result⟩)
 (.leaf ⟨(29, 32693316222976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 32693844705280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 32711613907200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record004_result⟩)
 (.leaf ⟨(29, 32716951191552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00257.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23400 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23400 23406 :=
  block_of_table results 23400 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0691

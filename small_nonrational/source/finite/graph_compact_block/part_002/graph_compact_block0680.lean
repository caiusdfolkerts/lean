module
prelude
import GraphInputsRow29Part00246Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0680
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 31938788261888), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 31939559981312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record001_result⟩)
 (.leaf ⟨(29, 31940330143744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 31960731811840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record003_result⟩)
 (.leaf ⟨(29, 31963709186048), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 31972294926336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record005_result⟩)
 (.leaf ⟨(29, 31973615600160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23349 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 23349 23356 :=
  block_of_table results 23349 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0680

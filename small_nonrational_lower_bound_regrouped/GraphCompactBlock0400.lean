module
prelude
import GraphInputsRow26Part00084Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0400
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 34673288315136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record000_result⟩)
 (.leaf ⟨(26, 34673556783104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 34673565106176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record002_result⟩)
 (.leaf ⟨(26, 34674076553216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 34674344886528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record004_result⟩)
 (.leaf ⟨(26, 34674382536704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 34674655100928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 34675150029312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record007_result⟩)
 (.leaf ⟨(26, 34675150553088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17635 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 17635 17644 :=
  block_of_table results 17635 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0400

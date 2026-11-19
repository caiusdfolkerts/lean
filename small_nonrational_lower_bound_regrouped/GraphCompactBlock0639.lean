module
prelude
import GraphInputsRow29Part00205Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0639
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29070572158976), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record000_result⟩)
 (.leaf ⟨(29, 29140451361024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29140459749376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record002_result⟩)
 (.leaf ⟨(29, 29140583481600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 29140587708416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record004_result⟩)
 (.leaf ⟨(29, 29140591869952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 29140682572032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 29140694601728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record007_result⟩)
 (.leaf ⟨(29, 29140851916928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00205.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23035 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23035 23044 :=
  block_of_table results 23035 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0639

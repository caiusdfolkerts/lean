module
prelude
import GraphInputsRow29Part00207Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0641
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29147295416320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record000_result⟩)
 (.leaf ⟨(29, 29147326333056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29148198736128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record002_result⟩)
 (.leaf ⟨(29, 29148467171456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 29155513630848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record004_result⟩)
 (.leaf ⟨(29, 29155647832192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 29155653586944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 29175998611712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record007_result⟩)
 (.leaf ⟨(29, 29176002838528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23053 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23053 23062 :=
  block_of_table results 23053 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0641

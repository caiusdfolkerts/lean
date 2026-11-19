module
prelude
import GraphInputsRow29Part00153Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0587
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 24742413205505), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record000_result⟩)
 (.leaf ⟨(29, 24742813794304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 24744960229376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record002_result⟩)
 (.leaf ⟨(29, 24744984871168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 24757838839808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record004_result⟩)
 (.leaf ⟨(29, 24759010594944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 24777943287824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 24778220536064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record007_result⟩)
 (.leaf ⟨(29, 24778228924416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22619 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22619 22628 :=
  block_of_table results 22619 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0587

module
prelude
import GraphInputsRow23Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0105
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 32172057051136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 32198434553856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record001_result⟩)
 (.leaf ⟨(23, 32199103479808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 32205344604160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 32270513602560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record004_result⟩)
 (.leaf ⟨(23, 32271042084864), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 32301981368320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 32334680227840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record007_result⟩)
 (.leaf ⟨(23, 32335217033216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 32351841304576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record009_result⟩)
 (.leaf ⟨(23, 32475598356480), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 32476135161856), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record011_result⟩)
 (.leaf ⟨(23, 32488344846336), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7619 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 7619 7632 :=
  block_of_table results 7619 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0105

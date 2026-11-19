module
prelude
import GraphInputsRow31Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0814
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 6379905482752), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 6417494835200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record001_result⟩)
 (.leaf ⟨(31, 6425292112128), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 6433886240768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record003_result⟩)
 (.leaf ⟨(31, 6434423046144), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 6442471981056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record005_result⟩)
 (.leaf ⟨(31, 6443256512512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(31, 6451041075200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 6451586138112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record008_result⟩)
 (.leaf ⟨(31, 6607316459584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 6671975849984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record010_result⟩)
 (.leaf ⟨(31, 6676136599552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 6684446589184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record012_result⟩)
 (.leaf ⟨(31, 6684458098688), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25712 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 25712 25726 :=
  block_of_table results 25712 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0814

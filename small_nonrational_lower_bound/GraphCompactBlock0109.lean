module
prelude
import GraphInputsRow23Part00031Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0109
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(23, 32822693724160), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record000_result⟩)
 (.leaf ⟨(23, 32839320076288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record001_result⟩))
 (.branch 3
 (.leaf ⟨(23, 32916647247872), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record002_result⟩)
 (.leaf ⟨(23, 32918802006016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(23, 32919330488320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record004_result⟩)
 (.leaf ⟨(23, 32933827051520), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record005_result⟩))
 (.branch 7
 (.leaf ⟨(23, 32935956840448), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record006_result⟩)
 (.leaf ⟨(23, 32986578297088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(23, 32986582491264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record008_result⟩)
 (.leaf ⟨(23, 32988672852224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record009_result⟩))
 (.branch 11
 (.leaf ⟨(23, 32989174579328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record010_result⟩)
 (.leaf ⟨(23, 32995315564800), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(23, 32995324993536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record012_result⟩)
 (.leaf ⟨(23, 33022410244224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record013_result⟩))
 (.branch 15
 (.leaf ⟨(23, 33029709955072), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record014_result⟩)
 (.leaf ⟨(23, 33064135753728), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00031.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7669 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 7669 7685 :=
  block_of_table results 7669 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0109

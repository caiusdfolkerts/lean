module
prelude
import GraphInputsRow29Part00052Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0486
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 10138673283328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 10138826080512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record001_result⟩)
 (.leaf ⟨(29, 10138830307328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 10138941686016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 10138953975808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record004_result⟩)
 (.leaf ⟨(29, 10184051134496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 10208472530944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 10210552905728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record007_result⟩)
 (.leaf ⟨(29, 10214713655296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 10218410868737), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record009_result⟩)
 (.leaf ⟨(29, 10276000825344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 10293696561152), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record011_result⟩)
 (.leaf ⟨(29, 10301617537024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00052.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21270 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 21270 21283 :=
  block_of_table results 21270 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0486

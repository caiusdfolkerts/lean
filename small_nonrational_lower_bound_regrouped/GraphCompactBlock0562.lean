module
prelude
import GraphInputsRow29Part00128Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0562
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 21522118934784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 21522887016448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record001_result⟩)
 (.leaf ⟨(29, 21527047442560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(29, 21528120918656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record003_result⟩)
 (.leaf ⟨(29, 21535001706752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record004_result⟩))
 (.branch 6
 (.leaf ⟨(29, 21535771869184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record005_result⟩)
 (.leaf ⟨(29, 21587715752192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(29, 21588252622848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 21588260945920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record008_result⟩)
 (.leaf ⟨(29, 21590836314368), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(29, 21591472275456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record010_result⟩)
 (.leaf ⟨(29, 21596305654016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record011_result⟩))
 (.branch 13
 (.leaf ⟨(29, 21596574121984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record012_result⟩)
 (.leaf ⟨(29, 21596582445056), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22314 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 22314 22328 :=
  block_of_table results 22314 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0562

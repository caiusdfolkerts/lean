module
prelude
import GraphInputsRow29Part00118Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0552
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 20394251681920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record000_result⟩)
 (.leaf ⟨(29, 20397471334528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 20412123582720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record002_result⟩)
 (.leaf ⟨(29, 20414270017792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 20415661506816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record004_result⟩)
 (.leaf ⟨(29, 20415669895168), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 20419962765312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 20423174029568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record007_result⟩)
 (.leaf ⟨(29, 20428143755520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 20428152143872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record009_result⟩)
 (.leaf ⟨(29, 20428284264448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 20428350324736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 20428544311424), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record012_result⟩)
 (.leaf ⟨(29, 20429683589248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 20466324472448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record014_result⟩)
 (.leaf ⟨(29, 20482855276800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 20496869523456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 20525787185408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record017_result⟩)
 (.leaf ⟨(29, 20526059814912), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00118.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22203 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 22203 22222 :=
  block_of_table results 22203 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0552

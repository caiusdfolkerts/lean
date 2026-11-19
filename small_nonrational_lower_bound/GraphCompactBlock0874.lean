module
prelude
import GraphInputsRow31Part00086Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0874
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 17198122991616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record000_result⟩)
 (.leaf ⟨(31, 17198399619072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 17198928101376), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record002_result⟩)
 (.leaf ⟨(31, 17205680930816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 17257723854848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record004_result⟩)
 (.leaf ⟨(31, 17274895335424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 17317325472000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record006_result⟩)
 (.branch 8
 (.leaf ⟨(31, 17326452244480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record007_result⟩)
 (.leaf ⟨(31, 17334505340928), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(31, 17335561912320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record009_result⟩)
 (.leaf ⟨(31, 17343078076416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record010_result⟩))
 (.branch 12
 (.leaf ⟨(31, 17454747224320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record011_result⟩)
 (.leaf ⟨(31, 17454768128000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(31, 17459318882304), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record013_result⟩)
 (.leaf ⟨(31, 17480517025792), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record014_result⟩))
 (.branch 16
 (.leaf ⟨(31, 17532593373184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record015_result⟩)
 (.branch 17
 (.leaf ⟨(31, 17595518500992), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record016_result⟩)
 (.leaf ⟨(31, 17595584561280), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00086.record017_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26195 + i))) 0 18 :=
  interval_of_check _ 0 18 (by decide +kernel)

public theorem complete : Block 26195 26213 :=
  block_of_table results 26195 18 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0874

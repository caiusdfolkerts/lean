module
prelude
import GraphInputsRow26Part00060Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0376
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 28865574518784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record000_result⟩)
 (.leaf ⟨(26, 28869799215232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 28869803409408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record002_result⟩)
 (.leaf ⟨(26, 28869999476864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 28874162339840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record004_result⟩)
 (.leaf ⟨(26, 28897767882880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 28897769963648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record006_result⟩)
 (.leaf ⟨(26, 28897769996288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 28900941891712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record008_result⟩)
 (.leaf ⟨(26, 28900990689280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 28901007952000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record010_result⟩)
 (.leaf ⟨(26, 28901121736832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 28901121769472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record012_result⟩)
 (.leaf ⟨(26, 28901122809856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 28932062593152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 28933135810688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record015_result⟩)
 (.leaf ⟨(26, 28933333991552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 28965345722496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record017_result⟩)
 (.leaf ⟨(26, 28965347803264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 28965347835904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record019_result⟩)
 (.leaf ⟨(26, 28965349623936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 28965547804800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record021_result⟩)
 (.leaf ⟨(26, 28965549137920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 28965601282056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 28967545473152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record024_result⟩)
 (.leaf ⟨(26, 28967545505792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 28967562150400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record026_result⟩)
 (.leaf ⟨(26, 28967681655816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 28967698432001), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record028_result⟩)
 (.leaf ⟨(26, 28974120961032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 28974137737217), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record030_result⟩)
 (.leaf ⟨(26, 29001937586304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 29034133063808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 29036262852736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record033_result⟩)
 (.leaf ⟨(26, 29038343227520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060.record034_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17019 + i))) 0 35 :=
  interval_of_check _ 0 35 (by decide +kernel)

public theorem complete : Block 17019 17054 :=
  block_of_table results 17019 35 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0376

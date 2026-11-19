module
prelude
import GraphInputsRow31Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0805
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(31, 4076200853504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record000_result⟩)
 (.branch 2
 (.leaf ⟨(31, 4076729270784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record001_result⟩)
 (.leaf ⟨(31, 4076737658880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(31, 4136456749056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record003_result⟩)
 (.leaf ⟨(31, 4196455743744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record004_result⟩))
 (.branch 6
 (.leaf ⟨(31, 4213635612672), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record005_result⟩)
 (.leaf ⟨(31, 4214172418048), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(31, 4217796362240), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 4329345941760), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record008_result⟩)
 (.leaf ⟨(31, 4333643038720), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 4333898891264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record010_result⟩)
 (.leaf ⟨(31, 4333915602944), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 4334427570176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record012_result⟩)
 (.leaf ⟨(31, 4342212132864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(31, 4342757195776), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record014_result⟩)
 (.branch 16
 (.leaf ⟨(31, 4351078694912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record015_result⟩)
 (.leaf ⟨(31, 4351607177216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(31, 4359391936512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record017_result⟩)
 (.leaf ⟨(31, 4401378984192), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record018_result⟩))
 (.branch 20
 (.leaf ⟨(31, 4436172947584), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record019_result⟩)
 (.leaf ⟨(31, 4436445380864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(31, 4442686505216), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record021_result⟩)
 (.leaf ⟨(31, 4508377743616), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record022_result⟩))
 (.branch 24
 (.leaf ⟨(31, 4508386131968), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record023_result⟩)
 (.leaf ⟨(31, 4512274252032), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(31, 4512538493184), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record025_result⟩)
 (.leaf ⟨(31, 4512546881536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record026_result⟩))
 (.branch 28
 (.leaf ⟨(31, 4514817048832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record027_result⟩)
 (.leaf ⟨(31, 4520859992320), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00017.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25603 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 25603 25632 :=
  block_of_table results 25603 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0805

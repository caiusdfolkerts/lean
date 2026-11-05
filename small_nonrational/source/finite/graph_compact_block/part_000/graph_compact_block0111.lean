module
prelude
import GraphInputsRow23Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0111
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 33719788437504), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 33751002251264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record001_result⟩)
 (.leaf ⟨(23, 33751530733568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 34088117371136), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 34088253718528), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record004_result⟩)
 (.leaf ⟨(23, 34088262041600), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 34088385839104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 34088394162176), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record007_result⟩)
 (.leaf ⟨(23, 34088484929536), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 34088887533568), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record009_result⟩)
 (.leaf ⟨(23, 34091337023744), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 34092108746752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record011_result⟩)
 (.leaf ⟨(23, 34094558757120), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(23, 34094726053888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record013_result⟩)
 (.branch 15
 (.leaf ⟨(23, 34095095627776), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record014_result⟩)
 (.leaf ⟨(23, 34095097708544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(23, 34095128657920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record016_result⟩)
 (.branch 18
 (.leaf ⟨(23, 34095631974656), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record017_result⟩)
 (.leaf ⟨(23, 34096269496320), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(23, 34110664351808), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record019_result⟩)
 (.branch 21
 (.leaf ⟨(23, 34123532501248), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record020_result⟩)
 (.leaf ⟨(23, 34123800969216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(23, 34123809292288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record022_result⟩)
 (.leaf ⟨(23, 34124320739328), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record023_result⟩))
 (.branch 25
 (.leaf ⟨(23, 34124589072640), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record024_result⟩)
 (.leaf ⟨(23, 34124865863680), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7701 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 7701 7727 :=
  block_of_table results 7701 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0111

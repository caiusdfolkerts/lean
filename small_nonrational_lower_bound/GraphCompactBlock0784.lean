module
prelude
import GraphInputsRow30Part00056Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0784
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 33298210357760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 33579539103744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record001_result⟩)
 (.leaf ⟨(30, 33613831733248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(30, 33682416992256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record003_result⟩)
 (.branch 5
 (.leaf ⟨(30, 33685463171072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record004_result⟩)
 (.leaf ⟨(30, 33751002251264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(30, 33751530733568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 34088117371136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record007_result⟩)
 (.leaf ⟨(30, 34088253718528), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(30, 34088262041600), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record009_result⟩)
 (.branch 11
 (.leaf ⟨(30, 34088385839104), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record010_result⟩)
 (.leaf ⟨(30, 34088394162176), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(30, 34088484929536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record012_result⟩)
 (.branch 14
 (.leaf ⟨(30, 34088887533568), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record013_result⟩)
 (.leaf ⟨(30, 34091337023744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(30, 34092108746752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record015_result⟩)
 (.branch 17
 (.leaf ⟨(30, 34094558757120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record016_result⟩)
 (.leaf ⟨(30, 34094726053888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(30, 34095095627776), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record018_result⟩)
 (.branch 20
 (.leaf ⟨(30, 34095097708544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record019_result⟩)
 (.leaf ⟨(30, 34095128657920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(30, 34095631974656), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record021_result⟩)
 (.leaf ⟨(30, 34096269496320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record022_result⟩))
 (.branch 24
 (.leaf ⟨(30, 34110664351808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record023_result⟩)
 (.leaf ⟨(30, 34123532501248), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00056.record024_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25338 + i))) 0 25 :=
  interval_of_check _ 0 25 (by decide +kernel)

public theorem complete : Block 25338 25363 :=
  block_of_table results 25338 25 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0784

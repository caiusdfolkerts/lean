module
prelude
import GraphInputsRow19Part00037Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0077
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 34682415091712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 34682431606784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record001_result⟩)
 (.leaf ⟨(19, 34682934792448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(19, 34682968408064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record003_result⟩)
 (.leaf ⟨(19, 34682976731136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record004_result⟩))
 (.branch 6
 (.leaf ⟨(19, 34683471663104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record005_result⟩)
 (.leaf ⟨(19, 34683505082880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(19, 34699074473984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record007_result⟩)
 (.branch 9
 (.leaf ⟨(19, 34699074994176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record008_result⟩)
 (.leaf ⟨(19, 34737746116864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(19, 34737750343680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record010_result⟩)
 (.leaf ⟨(19, 34737758406656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record011_result⟩))
 (.branch 13
 (.leaf ⟨(19, 34737980969216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record012_result⟩)
 (.leaf ⟨(19, 34737989357568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(19, 34737989617664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record014_result⟩)
 (.branch 16
 (.leaf ⟨(19, 34737997744384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record015_result⟩)
 (.leaf ⟨(19, 34739037800704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(19, 34739046189056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record017_result⟩)
 (.leaf ⟨(19, 34739054445312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record018_result⟩))
 (.branch 20
 (.leaf ⟨(19, 34746327500800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record019_result⟩)
 (.leaf ⟨(19, 34746822428688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 34746839073296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record021_result⟩)
 (.leaf ⟨(19, 34746855850504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 34763465426960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record023_result⟩)
 (.leaf ⟨(19, 34763482206208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(19, 34763482726400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record025_result⟩)
 (.leaf ⟨(19, 34763515625984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record026_result⟩))
 (.branch 28
 (.leaf ⟨(19, 34764539036164), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record027_result⟩)
 (.leaf ⟨(19, 34764539167744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5551 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 5551 5580 :=
  block_of_table results 5551 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0077

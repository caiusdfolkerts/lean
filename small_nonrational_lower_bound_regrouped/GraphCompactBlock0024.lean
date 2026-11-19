module
prelude
import GraphInputsRow16Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0024
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 24934612992000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record000_result⟩)
 (.leaf ⟨(16, 24965776736256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 24966696304896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record002_result⟩)
 (.leaf ⟨(16, 24966700531712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 24966707814400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record004_result⟩)
 (.leaf ⟨(16, 24966939025408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 24966955540480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record006_result⟩)
 (.leaf ⟨(16, 24967785906432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 24967790133248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record008_result⟩)
 (.leaf ⟨(16, 24967798326272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 24967995596800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record010_result⟩)
 (.leaf ⟨(16, 24967996507136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 24968260748288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record012_result⟩)
 (.leaf ⟨(16, 24981832532224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 24981840920576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record014_result⟩)
 (.leaf ⟨(16, 24982348660992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(16, 24996911284480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record016_result⟩)
 (.leaf ⟨(16, 25003152277760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record017_result⟩))
 (.branch 19
 (.leaf ⟨(16, 25003420745728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record018_result⟩)
 (.leaf ⟨(16, 25003429068800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(16, 25003957420544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record020_result⟩)
 (.leaf ⟨(16, 25028017029376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record021_result⟩))
 (.branch 23
 (.leaf ⟨(16, 25053959880704), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record022_result⟩)
 (.leaf ⟨(16, 25083974263040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(16, 25095779655936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record024_result⟩)
 (.leaf ⟨(16, 25119407800320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record025_result⟩))
 (.branch 27
 (.leaf ⟨(16, 25125847105536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record026_result⟩)
 (.leaf ⟨(16, 25129190948864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(16, 25157972820224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record028_result⟩)
 (.leaf ⟨(16, 25190184812800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record029_result⟩))
 (.branch 31
 (.leaf ⟨(16, 25191262519296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 25256710438912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record031_result⟩)
 (.leaf ⟨(16, 25256718761984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00024.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1463 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 1463 1496 :=
  block_of_table results 1463 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0024

module
prelude
import GraphInputsRow26Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0349
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 19595324882944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 19595331125248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record001_result⟩)
 (.leaf ⟨(26, 19596360843520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 19596365070336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record003_result⟩)
 (.leaf ⟨(26, 19602341890176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 19611963654400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record005_result⟩)
 (.leaf ⟨(26, 19612100001792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(26, 19612108324864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 19612232122368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record008_result⟩)
 (.leaf ⟨(26, 19612240445440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 19612504686592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record010_result⟩)
 (.leaf ⟨(26, 19612700786688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 19612768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record012_result⟩)
 (.leaf ⟨(26, 19623709967368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(26, 19628556321024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 19628560547840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record015_result⟩)
 (.leaf ⟨(26, 19628566790144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 19628684216320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record017_result⟩)
 (.leaf ⟨(26, 19632970858496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 19636733216896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record019_result⟩)
 (.leaf ⟨(26, 19646004592640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 19649744011264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record021_result⟩)
 (.leaf ⟨(26, 19649752334336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 19657404776448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record023_result⟩)
 (.leaf ⟨(26, 19657664790784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(26, 19657675259904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record025_result⟩)
 (.leaf ⟨(26, 19659485151232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record026_result⟩))
 (.branch 28
 (.leaf ⟨(26, 19664048504832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record027_result⟩)
 (.leaf ⟨(26, 19680825704448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15794 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 15794 15823 :=
  block_of_table results 15794 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0349

module
prelude
import GraphInputsRow26Part00067Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0383
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 31521914290176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record000_result⟩)
 (.leaf ⟨(26, 31522451095552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 31526202933504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record002_result⟩)
 (.leaf ⟨(26, 31526537461760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 31526743965696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record004_result⟩)
 (.leaf ⟨(26, 31528419655680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 31528692219904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record006_result⟩)
 (.leaf ⟨(26, 31529220702208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 31529389555968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record008_result⟩)
 (.leaf ⟨(26, 31530160758784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 31530500030464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record010_result⟩)
 (.leaf ⟨(26, 31530772594688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 31531235016704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record012_result⟩)
 (.leaf ⟨(26, 31537979523072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 31538053906432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 31538516328448), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record015_result⟩)
 (.leaf ⟨(26, 31545532416256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 31545805045760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record017_result⟩)
 (.leaf ⟨(26, 31546069286912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 31546077609984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record019_result⟩)
 (.leaf ⟨(26, 31546267467776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 31551971721472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record021_result⟩)
 (.leaf ⟨(26, 31552508592128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 31552516915200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 31553011908864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record024_result⟩)
 (.leaf ⟨(26, 31560561623296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 31560830091264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record026_result⟩)
 (.leaf ⟨(26, 31560838414336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 31561299795968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record028_result⟩)
 (.leaf ⟨(26, 31561601810688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(26, 31562373013504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record030_result⟩)
 (.leaf ⟨(26, 31568044237056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record031_result⟩))
 (.branch 33
 (.leaf ⟨(26, 31569151590400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record032_result⟩)
 (.branch 34
 (.leaf ⟨(26, 31569688395776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record033_result⟩)
 (.leaf ⟨(26, 31570191777792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00067.record034_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (17261 + i))) 0 35 :=
  interval_of_check _ 0 35 (by decide +kernel)

public theorem complete : Block 17261 17296 :=
  block_of_table results 17261 35 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0383

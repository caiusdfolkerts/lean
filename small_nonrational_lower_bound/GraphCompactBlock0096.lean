module
prelude
import GraphInputsRow23Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0096
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 25772622610432), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 25774702985216), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record001_result⟩)
 (.leaf ⟨(23, 25776246423552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(23, 25787001487360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record003_result⟩)
 (.leaf ⟨(23, 25787185233920), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record004_result⟩))
 (.branch 6
 (.leaf ⟨(23, 25789131276288), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record005_result⟩)
 (.leaf ⟨(23, 25843929776384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(23, 25844202405888), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record007_result⟩)
 (.leaf ⟨(23, 25844466647040), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record008_result⟩))
 (.branch 10
 (.leaf ⟨(23, 25844474970112), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record009_result⟩)
 (.leaf ⟨(23, 25844697858048), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(23, 25848759517184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record011_result⟩)
 (.leaf ⟨(23, 25848767840256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record012_result⟩))
 (.branch 14
 (.leaf ⟨(23, 25848858607616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record013_result⟩)
 (.leaf ⟨(23, 25856812548352), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(23, 25857180106752), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record015_result⟩)
 (.branch 17
 (.leaf ⟨(23, 25857353580544), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record016_result⟩)
 (.leaf ⟨(23, 25857582710784), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(23, 25860032200960), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record018_result⟩)
 (.leaf ⟨(23, 25860803923968), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record019_result⟩))
 (.branch 21
 (.leaf ⟨(23, 25912888328192), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record020_result⟩)
 (.leaf ⟨(23, 25916386902016), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(23, 25916395225088), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record022_result⟩)
 (.leaf ⟨(23, 25924439933184), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record023_result⟩))
 (.branch 25
 (.leaf ⟨(23, 25924980965376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record024_result⟩)
 (.leaf ⟨(23, 25925228171264), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(23, 25925496504576), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record026_result⟩)
 (.leaf ⟨(23, 25926301647360), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record027_result⟩))
 (.branch 29
 (.leaf ⟨(23, 25928755380224), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record028_result⟩)
 (.leaf ⟨(23, 25963354128384), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00018.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7168 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 7168 7198 :=
  block_of_table results 7168 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0096

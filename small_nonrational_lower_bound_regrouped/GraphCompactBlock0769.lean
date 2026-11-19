module
prelude
import GraphInputsRow30Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0769
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(30, 25772110643200), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 25772507004928), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record001_result⟩)
 (.leaf ⟨(30, 25772622610432), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 25774702985216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record003_result⟩)
 (.leaf ⟨(30, 25776246423552), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 25787001487360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record005_result⟩)
 (.leaf ⟨(30, 25787185233920), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(30, 25789131276288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record007_result⟩)
 (.branch 9
 (.leaf ⟨(30, 25844474970112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record008_result⟩)
 (.leaf ⟨(30, 25844697858048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(30, 25848759517184), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record010_result⟩)
 (.leaf ⟨(30, 25848767840256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record011_result⟩))
 (.branch 13
 (.leaf ⟨(30, 25857353580544), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record012_result⟩)
 (.leaf ⟨(30, 25857582710784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(30, 25860803923968), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record014_result⟩)
 (.branch 16
 (.leaf ⟨(30, 25864327151872), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record015_result⟩)
 (.leaf ⟨(30, 25916395225088), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(30, 25924980965376), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record017_result⟩)
 (.leaf ⟨(30, 25925228171264), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record018_result⟩))
 (.branch 20
 (.leaf ⟨(30, 25926301647360), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record019_result⟩)
 (.leaf ⟨(30, 25933012668672), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(30, 25980811411456), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 25993159393536), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record022_result⟩)
 (.leaf ⟨(30, 25993696264192), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 25993813430272), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record024_result⟩)
 (.leaf ⟨(30, 26117981929472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 26122545283072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record026_result⟩)
 (.leaf ⟨(30, 26130983948288), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00041.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24932 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 24932 24960 :=
  block_of_table results 24932 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0769

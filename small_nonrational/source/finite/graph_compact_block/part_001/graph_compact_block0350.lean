module
prelude
import GraphInputsRow26Part00034Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0350
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 19681286045696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record000_result⟩)
 (.leaf ⟨(26, 19683937943552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 19683946266624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record002_result⟩)
 (.leaf ⟨(26, 19684012326912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 19684045357056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record004_result⟩)
 (.leaf ⟨(26, 19684406607872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 19692720816128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 19693096435968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record007_result⟩)
 (.leaf ⟨(26, 19693108725760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 19697284169728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record009_result⟩)
 (.leaf ⟨(26, 19697391386880), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 19697401595904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 19701686076160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record012_result⟩)
 (.leaf ⟨(26, 19705723095040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 19710410228288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record014_result⟩)
 (.leaf ⟨(26, 19718195003648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 19718329270272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 19718337593344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record017_result⟩)
 (.leaf ⟨(26, 19718731874304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(26, 19718865945088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record019_result⟩)
 (.leaf ⟨(26, 19724792561920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record020_result⟩))
 (.branch 22
 (.leaf ⟨(26, 19724800950272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 19724924682496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record022_result⟩)
 (.leaf ⟨(26, 19724933070848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 19725040288000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record024_result⟩)
 (.leaf ⟨(26, 19725193085184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 19725197312000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record026_result⟩)
 (.branch 28
 (.leaf ⟨(26, 19725203554304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record027_result⟩)
 (.leaf ⟨(26, 19725308690688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(26, 19725320980480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record029_result⟩)
 (.leaf ⟨(26, 19725442892032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record030_result⟩))
 (.branch 32
 (.leaf ⟨(26, 19727079505920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 19727120662784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record032_result⟩)
 (.leaf ⟨(26, 19727343747072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(26, 19727401355264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record034_result⟩)
 (.leaf ⟨(26, 19729607622656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record035_result⟩))
 (.branch 37
 (.leaf ⟨(26, 19731642859520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 19731684016384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record037_result⟩)
 (.leaf ⟨(26, 19731694225408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00034.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15823 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 15823 15862 :=
  block_of_table results 15823 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0350

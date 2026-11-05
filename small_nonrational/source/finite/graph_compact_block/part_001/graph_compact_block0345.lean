module
prelude
import GraphInputsRow26Part00029Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0345
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 23
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 17857068990464), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record000_result⟩)
 (.leaf ⟨(26, 17857077313536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 17972446937344), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 17976931680512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record003_result⟩)
 (.leaf ⟨(26, 17977200115840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 17993971040512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 17993979428864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record006_result⟩)
 (.leaf ⟨(26, 17994103161088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 17994107387904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 17994111549440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record009_result⟩)
 (.leaf ⟨(26, 17994371596416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(26, 17994571858048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 17998272299008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record012_result⟩)
 (.leaf ⟨(26, 18045516939520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(26, 18186579820672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 18246385352960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record015_result⟩)
 (.leaf ⟨(26, 18246653755648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(26, 18253922517000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record017_result⟩)
 (.branch 19
 (.leaf ⟨(26, 18256975003904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record018_result⟩)
 (.leaf ⟨(26, 18256975069184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(26, 18263889182848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record020_result⟩)
 (.branch 22
 (.leaf ⟨(26, 18265696896256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record021_result⟩)
 (.leaf ⟨(26, 18266097484032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record022_result⟩))))))
 (.branch 34
 (.branch 28
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 18266105872384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record023_result⟩)
 (.leaf ⟨(26, 18266365952000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 18266374275072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 18271933989120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record026_result⟩)
 (.leaf ⟨(26, 18271934054400), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record027_result⟩))))
 (.branch 31
 (.branch 29
 (.leaf ⟨(26, 18272479117312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 18287008186624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record029_result⟩)
 (.leaf ⟨(26, 18288533348672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record030_result⟩)))
 (.branch 32
 (.leaf ⟨(26, 18289589920064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record031_result⟩)
 (.branch 33
 (.leaf ⟨(26, 18289654841600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record032_result⟩)
 (.leaf ⟨(26, 18334823251968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record033_result⟩)))))
 (.branch 40
 (.branch 37
 (.branch 35
 (.leaf ⟨(26, 18335268897024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record034_result⟩)
 (.branch 36
 (.leaf ⟨(26, 18336358563840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record035_result⟩)
 (.leaf ⟨(26, 18336503037953), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record036_result⟩)))
 (.branch 38
 (.leaf ⟨(26, 18336903626752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record037_result⟩)
 (.branch 39
 (.leaf ⟨(26, 18337031585792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record038_result⟩)
 (.leaf ⟨(26, 18337039908864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record039_result⟩))))
 (.branch 43
 (.branch 41
 (.leaf ⟨(26, 18402479505408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record040_result⟩)
 (.branch 42
 (.leaf ⟨(26, 18402487828480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record041_result⟩)
 (.leaf ⟨(26, 18406086673664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record042_result⟩)))
 (.branch 44
 (.leaf ⟨(26, 18406086738944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record043_result⟩)
 (.branch 45
 (.leaf ⟨(26, 18406355042560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record044_result⟩)
 (.leaf ⟨(26, 18406359171588), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00029.record045_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15570 + i))) 0 46 :=
  interval_of_check _ 0 46 (by decide +kernel)

public theorem complete : Block 15570 15616 :=
  block_of_table results 15570 46 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0345

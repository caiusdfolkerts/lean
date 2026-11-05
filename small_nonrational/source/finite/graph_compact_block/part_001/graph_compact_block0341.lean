module
prelude
import GraphInputsRow26Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0341
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 16632556556544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record000_result⟩)
 (.leaf ⟨(26, 16639265873984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 16639265890304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 16639266394176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record003_result⟩)
 (.leaf ⟨(26, 16639317772304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 16648574664704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 16648780128256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record006_result⟩)
 (.leaf ⟨(26, 16649853865984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 16657528406016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 16709168726016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record009_result⟩)
 (.leaf ⟨(26, 16713403858944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 16717155696896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record011_result⟩)
 (.leaf ⟨(26, 16717490225152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 16721452793856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 16721725358080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record014_result⟩)
 (.leaf ⟨(26, 16722187780096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 16729469091840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 16744609480704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record017_result⟩)
 (.leaf ⟨(26, 16752658415616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 16757091729408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 16767644909584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record020_result⟩)
 (.leaf ⟨(26, 16769838417936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 16776211662864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record022_result⟩)
 (.leaf ⟨(26, 16777519055104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 16846339244032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 16881779998720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record025_result⟩)
 (.leaf ⟨(26, 16906155261952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 16906359685120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 16914135392320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record028_result⟩)
 (.leaf ⟨(26, 16914136449024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 16930778390592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 16930812477440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record031_result⟩)
 (.leaf ⟨(26, 16930814558208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 16931904159744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 16939506532352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record034_result⟩)
 (.leaf ⟨(26, 16939646715904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(26, 16939753933056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 16943914551552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record037_result⟩)
 (.leaf ⟨(26, 16943922939904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 16948083689472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 16948612039176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record040_result⟩)
 (.leaf ⟨(26, 16969415787012), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 16969415918592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 16976013492224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record043_result⟩)
 (.leaf ⟨(26, 16976021815296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00025.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15395 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 15395 15440 :=
  block_of_table results 15395 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0341

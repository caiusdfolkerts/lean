module
prelude
import GraphInputsRow26Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0370
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 25787052984320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record000_result⟩)
 (.leaf ⟨(26, 25787184972296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 25839756935424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 25839757000704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record003_result⟩)
 (.leaf ⟨(26, 25839891136768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(26, 25839891202048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record005_result⟩)
 (.branch 7
 (.leaf ⟨(26, 25840156938496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record006_result⟩)
 (.leaf ⟨(26, 25840159604736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(26, 25840163229760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record008_result⟩)
 (.branch 10
 (.leaf ⟨(26, 25843112349952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record009_result⟩)
 (.leaf ⟨(26, 25843112415232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 25843376591104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record011_result⟩)
 (.leaf ⟨(26, 25843376656384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 25843384455184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record013_result⟩)
 (.branch 15
 (.leaf ⟨(26, 25843401230352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record014_result⟩)
 (.leaf ⟨(26, 25844063994112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(26, 25844168986624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 25844437389312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record017_result⟩)
 (.leaf ⟨(26, 25844474970113), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(26, 25847675752512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record019_result⟩)
 (.branch 21
 (.leaf ⟨(26, 25847677325328), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record020_result⟩)
 (.leaf ⟨(26, 25847694100496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 25848767840257), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record022_result⟩)
 (.leaf ⟨(26, 25855883479056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 25856015599632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record024_result⟩)
 (.branch 26
 (.leaf ⟨(26, 25856261492800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record025_result⟩)
 (.leaf ⟨(26, 25856263065616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(26, 25856279840784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record027_result⟩)
 (.branch 29
 (.leaf ⟨(26, 25857353580545), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record028_result⟩)
 (.leaf ⟨(26, 25878927048704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(26, 25907536597248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 25912091902208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record031_result⟩)
 (.leaf ⟨(26, 25913219678208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record032_result⟩)))))
 (.branch 39
 (.branch 36
 (.branch 34
 (.leaf ⟨(26, 25916378056720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 25916395225089), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record034_result⟩)
 (.leaf ⟨(26, 25924699555856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record035_result⟩)))
 (.branch 37
 (.leaf ⟨(26, 25924980965377), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 25925701926912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record037_result⟩)
 (.leaf ⟨(26, 25947248066560), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record038_result⟩))))
 (.branch 42
 (.branch 40
 (.leaf ⟨(26, 25963115118592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 25964427870208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record040_result⟩)
 (.leaf ⟨(26, 25964956352512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record041_result⟩)))
 (.branch 43
 (.leaf ⟨(26, 25976121856256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 25976524509248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record043_result⟩)
 (.leaf ⟨(26, 25993284814864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00054.record044_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16781 + i))) 0 45 :=
  interval_of_check _ 0 45 (by decide +kernel)

public theorem complete : Block 16781 16826 :=
  block_of_table results 16781 45 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0370

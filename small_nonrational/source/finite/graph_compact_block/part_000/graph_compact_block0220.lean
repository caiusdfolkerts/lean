module
prelude
import GraphInputsRow24Part00104Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0220
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 25787184972296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 25839752773888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record001_result⟩)
 (.leaf ⟨(24, 25839756935424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 25839757000704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record003_result⟩)
 (.leaf ⟨(24, 25839891136768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 25839891202048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record005_result⟩)
 (.leaf ⟨(24, 25840159604736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 25843112349952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record007_result⟩)
 (.leaf ⟨(24, 25843112415232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 25843376591104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record009_result⟩)
 (.leaf ⟨(24, 25843376656384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 25844063994112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record011_result⟩)
 (.leaf ⟨(24, 25844168921344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 25844168986624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record013_result⟩)
 (.leaf ⟨(24, 25844437389312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(24, 25844563607808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 25847675752512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record016_result⟩)
 (.leaf ⟨(24, 25847677325328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 25847694100496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record018_result⟩)
 (.leaf ⟨(24, 25848767840257), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 25856015599632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record020_result⟩)
 (.leaf ⟨(24, 25878927048704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 25907536597248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record022_result⟩)
 (.leaf ⟨(24, 25912091902208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 25913219678208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record024_result⟩)
 (.leaf ⟨(24, 25913722994944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 25916395225089), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record026_result⟩)
 (.leaf ⟨(24, 25924699555856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 25925701926912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record028_result⟩)
 (.leaf ⟨(24, 25947248066560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00104.record029_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11021 + i))) 0 30 :=
  interval_of_check _ 0 30 (by decide +kernel)

public theorem complete : Block 11021 11051 :=
  block_of_table results 11021 30 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0220

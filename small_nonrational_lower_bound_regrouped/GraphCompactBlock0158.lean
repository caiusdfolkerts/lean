module
prelude
import GraphInputsRow24Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0158
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 18266105872384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 18266365952000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record001_result⟩)
 (.leaf ⟨(24, 18266374275072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 18272479117312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record003_result⟩)
 (.leaf ⟨(24, 18288533348672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 18289654841600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record005_result⟩)
 (.leaf ⟨(24, 18297976340736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 18319723757824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 18327239950592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record008_result⟩)
 (.leaf ⟨(24, 18333481140224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 18334823251968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record010_result⟩)
 (.leaf ⟨(24, 18335301927168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 18336358498560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record012_result⟩)
 (.leaf ⟨(24, 18336358563840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 18336903626752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 18337031585792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record015_result⟩)
 (.leaf ⟨(24, 18337039908864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 18400254363776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record017_result⟩)
 (.leaf ⟨(24, 18402479505408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 18402487828480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_result⟩)
 (.leaf ⟨(24, 18406355042560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 18406359367680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record021_result⟩)
 (.leaf ⟨(24, 18406619382016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 18406627770368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_result⟩)
 (.leaf ⟨(24, 18406631801856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 18406891913216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record025_result⟩)
 (.leaf ⟨(24, 18406900236288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 18411052662784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record027_result⟩)
 (.leaf ⟨(24, 18411060985856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9490 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 9490 9519 :=
  block_of_table results 9490 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0158

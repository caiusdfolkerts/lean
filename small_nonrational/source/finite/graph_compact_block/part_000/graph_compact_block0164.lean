module
prelude
import GraphInputsRow24Part00048Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0164
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 19512581816320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record000_result⟩)
 (.leaf ⟨(24, 19534926921728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 19538991153152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 19539090243584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record003_result⟩)
 (.leaf ⟨(24, 19564259704833), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 19573374091520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 19573382479872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record006_result⟩)
 (.leaf ⟨(24, 19573910798976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 19586219016448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 19586739079296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record009_result⟩)
 (.leaf ⟨(24, 19587358294272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record010_result⟩)))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ⟨(24, 19587754656000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 19587779266688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record012_result⟩)
 (.leaf ⟨(24, 19588679008512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record013_result⟩)))
 (.branch 15
 (.leaf ⟨(24, 19588687396864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 19589079531776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record015_result⟩)
 (.leaf ⟨(24, 19589090000896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record016_result⟩))))
 (.branch 20
 (.branch 18
 (.leaf ⟨(24, 19590759383296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 19590767771648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record018_result⟩)
 (.leaf ⟨(24, 19595052253440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record019_result⟩)))
 (.branch 21
 (.leaf ⟨(24, 19595060641792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 19595320656128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record021_result⟩)
 (.leaf ⟨(24, 19595324882944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048.record022_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9703 + i))) 0 23 :=
  interval_of_check _ 0 23 (by decide +kernel)

public theorem complete : Block 9703 9726 :=
  block_of_table results 9703 23 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0164

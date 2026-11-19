module
prelude
import GraphInputsRow24Part00130Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0246
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31480768635136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record000_result⟩)
 (.leaf ⟨(24, 31483386462464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31483394850816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 31483798495232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record003_result⟩)
 (.leaf ⟨(24, 31483856167168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 31484872232960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 31484929384704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record006_result⟩)
 (.leaf ⟨(24, 31491976364288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 31491980591104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 31491987873792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record009_result⟩)
 (.leaf ⟨(24, 31492119994368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 31492177666304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record011_result⟩)
 (.leaf ⟨(24, 31495801020448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 31511239786752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 31511512416256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record014_result⟩)
 (.leaf ⟨(24, 31511776657408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(24, 31511784980480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 31513320161536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record017_result⟩)
 (.leaf ⟨(24, 31513592791040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(24, 31513857032192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 31513865355264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record020_result⟩)
 (.leaf ⟨(24, 31514055213056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00130.record021_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11640 + i))) 0 22 :=
  interval_of_check _ 0 22 (by decide +kernel)

public theorem complete : Block 11640 11662 :=
  block_of_table results 11640 22 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0246

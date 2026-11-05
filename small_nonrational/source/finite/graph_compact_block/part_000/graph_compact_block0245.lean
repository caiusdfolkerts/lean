module
prelude
import GraphInputsRow24Part00129Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0245
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31449630703616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record000_result⟩)
 (.leaf ⟨(24, 31450703332096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31451248656384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record002_result⟩)
 (.leaf ⟨(24, 31451785461760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 31464965046528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record004_result⟩)
 (.leaf ⟨(24, 31465735717408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 31465736249344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record006_result⟩)
 (.leaf ⟨(24, 31466075521024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 31466348085248), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record008_result⟩)
 (.leaf ⟨(24, 31466810507264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 31466876567552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record010_result⟩)
 (.leaf ⟨(24, 31478109446400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 31478381547552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record012_result⟩)
 (.leaf ⟨(24, 31480298930432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 31480567333120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record014_result⟩)
 (.leaf ⟨(24, 31480579362816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00129.record015_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11624 + i))) 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)

public theorem complete : Block 11624 11640 :=
  block_of_table results 11624 16 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0245

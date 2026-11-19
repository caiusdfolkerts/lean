module
prelude
import GraphInputsRow24Part00128Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0244
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 31414809591808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record000_result⟩)
 (.leaf ⟨(24, 31415069606144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 31415081107457), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record002_result⟩)
 (.leaf ⟨(24, 31415081115648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 31415270908160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record004_result⟩)
 (.leaf ⟨(24, 31415874420992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 31416142823680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 31416154853376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_result⟩)
 (.leaf ⟨(24, 31416344125696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 31423395332096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record009_result⟩)
 (.leaf ⟨(24, 31431376511008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 31442654527744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 31443191398400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record012_result⟩)
 (.leaf ⟨(24, 31443199721472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 31448316772353), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record014_result⟩)
 (.leaf ⟨(24, 31448895652096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 31449168281600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 31449432522752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record017_result⟩)
 (.leaf ⟨(24, 31449440845824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11605 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 11605 11624 :=
  block_of_table results 11605 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0244

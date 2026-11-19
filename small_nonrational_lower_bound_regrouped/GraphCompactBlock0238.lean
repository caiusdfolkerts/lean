module
prelude
import GraphInputsRow24Part00122Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0238
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 28900990689280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record000_result⟩)
 (.leaf ⟨(24, 28901007952000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 28901121769472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record002_result⟩)
 (.leaf ⟨(24, 28901122809856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 28902250512385), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record004_result⟩)
 (.leaf ⟨(24, 28905300822144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 28932062593152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 28933333991552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record007_result⟩)
 (.leaf ⟨(24, 28965347835904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 28965549137920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record009_result⟩)
 (.leaf ⟨(24, 28967545505792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 29000897398912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 29001937586304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record012_result⟩)
 (.leaf ⟨(24, 29147029061888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 29147063652608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record014_result⟩)
 (.leaf ⟨(24, 29180297756928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 29180299317504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 29181490561024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record017_result⟩)
 (.leaf ⟨(24, 29215783190528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00122.record018_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11443 + i))) 0 19 :=
  interval_of_check _ 0 19 (by decide +kernel)

public theorem complete : Block 11443 11462 :=
  block_of_table results 11443 19 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0238

module
prelude
import GraphInputsRow24Part00144Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0260
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32165173661728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32167359447296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record001_result⟩)
 (.leaf ⟨(24, 32172629098496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32196234608896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32196245078016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record004_result⟩)
 (.leaf ⟨(24, 32196443258880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 32196484415744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32199101383232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record007_result⟩)
 (.leaf ⟨(24, 32200649146368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 32203765727488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 32204220022784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record010_result⟩)
 (.leaf ⟨(24, 32221985652736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00144.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11821 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 11821 11833 :=
  block_of_table results 11821 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0260

module
prelude
import GraphInputsRow24Part00151Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0267
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 32514580153088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record000_result⟩)
 (.leaf ⟨(24, 32521828176128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32522051260416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 32522297937952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record003_result⟩)
 (.leaf ⟨(24, 32522901652224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 32523371414048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 32524445155856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record006_result⟩)
 (.leaf ⟨(24, 32531727515648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 32642843083008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 32642917531648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record009_result⟩)
 (.leaf ⟨(24, 32643379953664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11901 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 11901 11912 :=
  block_of_table results 11901 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0267

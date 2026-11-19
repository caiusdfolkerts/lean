module
prelude
import GraphInputsRow24Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0138
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 12577958528008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 12577975304193), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record001_result⟩)
 (.leaf ⟨(24, 12578103296000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 12578354889736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 12578371665921), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record004_result⟩)
 (.leaf ⟨(24, 12580030711808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 12580249731072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 12584323516672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record007_result⟩)
 (.leaf ⟨(24, 12584323581952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(24, 12584542601216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record009_result⟩)
 (.branch 11
 (.leaf ⟨(24, 12584794194952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record010_result⟩)
 (.leaf ⟨(24, 12584810971137), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00022.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8880 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 8880 8892 :=
  block_of_table results 8880 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0138

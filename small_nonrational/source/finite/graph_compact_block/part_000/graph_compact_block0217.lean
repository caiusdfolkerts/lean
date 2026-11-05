module
prelude
import GraphInputsRow24Part00101Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0217
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(24, 25641525452864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 25658186022912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record001_result⟩)
 (.leaf ⟨(24, 25659208507456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 25659275624448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 25659277705216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record004_result⟩)
 (.leaf ⟨(24, 25659409695232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00101.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10971 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 10971 10977 :=
  block_of_table results 10971 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0217

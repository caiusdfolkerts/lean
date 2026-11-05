module
prelude
import GraphInputsRow24Part00067Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0183
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23420190343168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record000_result⟩)
 (.leaf ⟨(24, 23420324544512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23421262504000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record002_result⟩)
 (.leaf ⟨(24, 23421599645952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 23421735993344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record004_result⟩)
 (.leaf ⟨(24, 23421744316416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 23421868113920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 23421876436992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record007_result⟩)
 (.leaf ⟨(24, 23422336778240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00067.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10319 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 10319 10328 :=
  block_of_table results 10319 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0183

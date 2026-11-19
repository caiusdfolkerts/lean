module
prelude
import GraphInputsRow29Part00187Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0621
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 27222062665760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 27224254726272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record001_result⟩)
 (.leaf ⟨(29, 27250632196352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 27251301187584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 27257542311936), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record004_result⟩)
 (.leaf ⟨(29, 27258582499328), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22919 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 22919 22925 :=
  block_of_table results 22919 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0621

module
prelude
import GraphInputsRow29Part00183Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0617
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 26571622596864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record000_result⟩)
 (.leaf ⟨(29, 26648730697728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 26670014664736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record002_result⟩)
 (.leaf ⟨(29, 26777579716608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 26943718170880), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record004_result⟩)
 (.leaf ⟨(29, 26943986606208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 26948279476352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 26956865216640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record007_result⟩)
 (.leaf ⟨(29, 26990985904384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22887 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22887 22896 :=
  block_of_table results 22887 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0617

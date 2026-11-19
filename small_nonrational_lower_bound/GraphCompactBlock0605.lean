module
prelude
import GraphInputsRow29Part00171Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0605
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 25735462928640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record000_result⟩)
 (.leaf ⟨(29, 25739757944832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 25739898388480), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record002_result⟩)
 (.leaf ⟨(29, 25740294750208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 25740410355712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record004_result⟩)
 (.leaf ⟨(29, 25752642797568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 25756919021568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 25769821618432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record007_result⟩)
 (.leaf ⟨(29, 25772110643200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22770 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22770 22779 :=
  block_of_table results 22770 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0605

module
prelude
import GraphInputsRow31Part00051Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0839
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 10678102392832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record000_result⟩)
 (.leaf ⟨(31, 10814727815424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 10815532958208), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record002_result⟩)
 (.leaf ⟨(31, 10896625631232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 10904922161152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record004_result⟩)
 (.leaf ⟨(31, 10905467224064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 10913788723200), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record006_result⟩)
 (.leaf ⟨(31, 10914317205504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00051.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25901 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25901 25909 :=
  block_of_table results 25901 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0839

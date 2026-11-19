module
prelude
import GraphInputsRow31Part00074Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0862
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 14037098201344), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record000_result⟩)
 (.leaf ⟨(31, 14037635072000), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 14037833252864), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 14044577693952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record003_result⟩)
 (.leaf ⟨(31, 14045348896768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 14158632386816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record005_result⟩)
 (.leaf ⟨(31, 14182053380096), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 14182788366336), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 14299322974464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record008_result⟩)
 (.leaf ⟨(31, 14299591377152), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26057 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 26057 26067 :=
  block_of_table results 26057 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0862

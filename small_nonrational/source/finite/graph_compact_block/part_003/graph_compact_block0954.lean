module
prelude
import GraphInputsRow31Part00166Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0954
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 2
 (.branch 1
 (.leaf ⟨(31, 32644444192768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00166.record000_result⟩)
 (.leaf ⟨(31, 32693827928064), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00166.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 32781614710784), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00166.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 32804960337920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00166.record003_result⟩)
 (.leaf ⟨(31, 32805027315712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00166.record004_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26733 + i))) 0 5 :=
  interval_of_check _ 0 5 (by decide +kernel)

public theorem complete : Block 26733 26738 :=
  block_of_table results 26733 5 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0954

module
prelude
import GraphInputsRow31Part00117Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0905
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 26467065929984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record000_result⟩)
 (.leaf ⟨(31, 26468139147520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 26498610298880), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record002_result⟩)
 (.leaf ⟨(31, 26498618621952), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 26502498353920), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record004_result⟩)
 (.leaf ⟨(31, 26502779371520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 26511100870656), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record006_result⟩)
 (.leaf ⟨(31, 26511493070848), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26461 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 26461 26469 :=
  block_of_table results 26461 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0905

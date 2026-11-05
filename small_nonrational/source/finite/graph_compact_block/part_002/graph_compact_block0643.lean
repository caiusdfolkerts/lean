module
prelude
import GraphInputsRow29Part00209Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0643
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 29176267047040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record000_result⟩)
 (.leaf ⟨(29, 29176518414464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 29177059409920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 29177591890560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record003_result⟩)
 (.leaf ⟨(29, 29180303511552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 29180410728704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 29180561997952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record006_result⟩)
 (.leaf ⟨(29, 29180567752704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 29180679164032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 29181484204800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record009_result⟩)
 (.leaf ⟨(29, 29181752640128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23064 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 23064 23075 :=
  block_of_table results 23064 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0643

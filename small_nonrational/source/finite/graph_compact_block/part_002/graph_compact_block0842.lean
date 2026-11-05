module
prelude
import GraphInputsRow31Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0842
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 11880017985536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record000_result⟩)
 (.leaf ⟨(31, 11914239443072), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 11948871647232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record002_result⟩)
 (.leaf ⟨(31, 11959474880768), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(31, 11982958903424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record004_result⟩)
 (.leaf ⟨(31, 11983027994624), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record005_result⟩))
 (.branch 7
 (.leaf ⟨(31, 11996116353024), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record006_result⟩)
 (.leaf ⟨(31, 12004710416384), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25921 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 25921 25929 :=
  block_of_table results 25921 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0842

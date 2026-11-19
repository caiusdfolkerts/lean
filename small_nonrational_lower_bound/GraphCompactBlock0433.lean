module
prelude
import GraphInputsRow28Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0433
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(28, 34746822295552), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record000_result⟩)
 (.leaf ⟨(28, 34763465293824), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record001_result⟩))
 (.branch 3
 (.leaf ⟨(28, 34772072595456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record002_result⟩)
 (.branch 4
 (.leaf ⟨(28, 34789252399104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record003_result⟩)
 (.leaf ⟨(28, 34790308970496), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(28, 34840799870976), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record005_result⟩)
 (.leaf ⟨(28, 34892314312704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record006_result⟩))
 (.branch 8
 (.leaf ⟨(28, 35046933268480), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record007_result⟩)
 (.branch 9
 (.leaf ⟨(28, 35115669389312), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record008_result⟩)
 (.leaf ⟨(28, 35150012350464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20436 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 20436 20446 :=
  block_of_table results 20436 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0433

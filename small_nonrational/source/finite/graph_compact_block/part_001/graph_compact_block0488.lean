module
prelude
import GraphInputsRow29Part00054Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0488
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 10448996929792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record000_result⟩)
 (.leaf ⟨(29, 10455599890432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 10456781557776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record002_result⟩)
 (.leaf ⟨(29, 10484309393408), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 10484312969472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record004_result⟩)
 (.leaf ⟨(29, 10488604344320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 10488605839616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 10488868585472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record007_result⟩)
 (.leaf ⟨(29, 10488870080768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21290 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 21290 21299 :=
  block_of_table results 21290 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0488

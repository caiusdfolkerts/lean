module
prelude
import GraphInputsRow30Part00019Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0747
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(30, 10484309393408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record000_result⟩)
 (.branch 2
 (.leaf ⟨(30, 10484312969472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record001_result⟩)
 (.leaf ⟨(30, 10488604344320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(30, 10488605839616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record003_result⟩)
 (.leaf ⟨(30, 10488868585472), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record004_result⟩))
 (.branch 6
 (.leaf ⟨(30, 10488870080768), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record005_result⟩)
 (.leaf ⟨(30, 10488993810448), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019.record006_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (24161 + i))) 0 7 :=
  interval_of_check _ 0 7 (by decide +kernel)

public theorem complete : Block 24161 24168 :=
  block_of_table results 24161 7 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0747

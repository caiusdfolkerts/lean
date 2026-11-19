module
prelude
import GraphInputsRow29Part00230Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0664
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 30898560966656), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 30900687601665), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record001_result⟩)
 (.leaf ⟨(29, 30900817559552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 30900825882624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 30900947518208), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record004_result⟩)
 (.leaf ⟨(29, 30903096115200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23246 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23246 23252 :=
  block_of_table results 23246 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0664

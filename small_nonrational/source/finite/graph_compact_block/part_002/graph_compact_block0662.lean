module
prelude
import GraphInputsRow29Part00228Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0662
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 30830959329280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 30830965571584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record001_result⟩)
 (.leaf ⟨(29, 30831021162752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 30831032672256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 30831155364096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record004_result⟩)
 (.leaf ⟨(29, 30839549198337), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 30840617189504), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 30857758773280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record007_result⟩)
 (.leaf ⟨(29, 30864197558304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(29, 30864198078496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record009_result⟩)
 (.branch 11
 (.leaf ⟨(29, 30865045389568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record010_result⟩)
 (.leaf ⟨(29, 30865053777920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00228.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23217 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 23217 23229 :=
  block_of_table results 23217 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0662

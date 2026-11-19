module
prelude
import GraphInputsRow29Part00222Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0656
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 30238203449344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record000_result⟩)
 (.leaf ⟨(29, 30238314860672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30241150472448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 30241158860800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record003_result⟩)
 (.leaf ⟨(29, 30241166987520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 30241175375872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 30241418907776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record006_result⟩)
 (.leaf ⟨(29, 30241435422848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 30241670303760), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 30242240463616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record009_result⟩)
 (.leaf ⟨(29, 30242508898944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23148 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 23148 23159 :=
  block_of_table results 23148 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0656

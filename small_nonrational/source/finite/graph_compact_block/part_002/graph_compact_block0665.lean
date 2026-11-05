module
prelude
import GraphInputsRow29Part00231Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0665
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 30915979903520), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record000_result⟩)
 (.leaf ⟨(29, 30931012821248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 30934033252608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record002_result⟩)
 (.leaf ⟨(29, 30934041640960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 30934042681344), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record004_result⟩)
 (.leaf ⟨(29, 30934100353280), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 30935173570816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 30942354751744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record007_result⟩)
 (.leaf ⟨(29, 30942363140096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00231.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23252 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 23252 23261 :=
  block_of_table results 23252 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0665

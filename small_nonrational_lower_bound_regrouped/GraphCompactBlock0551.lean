module
prelude
import GraphInputsRow29Part00117Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0551
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 20199436713984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record000_result⟩)
 (.leaf ⟨(29, 20278893674496), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 20346675663104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record002_result⟩)
 (.leaf ⟨(29, 20381100474624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 20381368877312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record004_result⟩)
 (.leaf ⟨(29, 20381377265664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 20385670135808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 20388881400064), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record007_result⟩)
 (.leaf ⟨(29, 20393991634944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22194 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22194 22203 :=
  block_of_table results 22194 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0551

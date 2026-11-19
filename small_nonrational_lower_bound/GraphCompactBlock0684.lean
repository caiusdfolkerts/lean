module
prelude
import GraphInputsRow29Part00250Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0684
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 3
 (.branch 1
 (.leaf ⟨(29, 32198434553856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 32199103479808), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record001_result⟩)
 (.leaf ⟨(29, 32205344604160), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 32270513602560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 32271042084864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record004_result⟩)
 (.leaf ⟨(29, 32301981368320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250.record005_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (23373 + i))) 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)

public theorem complete : Block 23373 23379 :=
  block_of_table results 23373 6 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0684

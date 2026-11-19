module
prelude
import GraphInputsRow29Part00104Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0538
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 17783727341824), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record000_result⟩)
 (.leaf ⟨(29, 17784129994816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 17786141155456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record002_result⟩)
 (.leaf ⟨(29, 17786277470272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 17839352250624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record004_result⟩)
 (.leaf ⟨(29, 17856532119552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 17914990174336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record006_result⟩)
 (.leaf ⟨(29, 18143305605440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104.record007_result⟩))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22005 + i))) 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)

public theorem complete : Block 22005 22013 :=
  block_of_table results 22005 8 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0538

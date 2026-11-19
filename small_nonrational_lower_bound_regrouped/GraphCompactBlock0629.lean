module
prelude
import GraphInputsRow29Part00195Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0629
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 28453495635968), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record000_result⟩)
 (.leaf ⟨(29, 28488811675648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 28492831981568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 28493484392448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record003_result⟩)
 (.leaf ⟨(29, 28531543244800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 28592851394688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 28592983515264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record006_result⟩)
 (.leaf ⟨(29, 28593247756416), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 28625296457728), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 28625556504704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record009_result⟩)
 (.leaf ⟨(29, 28627236323584), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22966 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 22966 22977 :=
  block_of_table results 22966 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0629

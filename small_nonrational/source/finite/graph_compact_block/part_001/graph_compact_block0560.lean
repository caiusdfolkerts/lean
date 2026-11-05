module
prelude
import GraphInputsRow29Part00126Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0560
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 21382631063552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record000_result⟩)
 (.leaf ⟨(29, 21383167868928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 21384711438336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record002_result⟩)
 (.leaf ⟨(29, 21397596291072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 21401891241984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record004_result⟩)
 (.leaf ⟨(29, 21402023362560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 21441704132864), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 21446017483008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record007_result⟩)
 (.leaf ⟨(29, 21446426394624), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22292 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 22292 22301 :=
  block_of_table results 22292 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0560

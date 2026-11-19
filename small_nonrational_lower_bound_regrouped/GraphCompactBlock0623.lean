module
prelude
import GraphInputsRow29Part00189Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0623
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 27404038979712), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record000_result⟩)
 (.leaf ⟨(29, 27493339767040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 27493740322944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 27561367707776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record003_result⟩)
 (.leaf ⟨(29, 27562495442945), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(29, 27566980219136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record005_result⟩)
 (.leaf ⟨(29, 27602290999296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record006_result⟩))
 (.branch 8
 (.leaf ⟨(29, 27602414796800), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record007_result⟩)
 (.branch 9
 (.leaf ⟨(29, 27635565478144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record008_result⟩)
 (.leaf ⟨(29, 27638786171136), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22930 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 22930 22940 :=
  block_of_table results 22930 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0623

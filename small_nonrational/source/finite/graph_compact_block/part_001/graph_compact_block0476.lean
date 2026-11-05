module
prelude
import GraphInputsRow29Part00042Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0476
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 7598090813440), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record000_result⟩)
 (.leaf ⟨(29, 7598355054592), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 7598363377664), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record002_result⟩)
 (.leaf ⟨(29, 7598602453512), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 7598602780672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record004_result⟩)
 (.leaf ⟨(29, 7607200776192), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 7611085029376), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 7611237826560), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record007_result⟩)
 (.leaf ⟨(29, 7611241988096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042.record008_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21060 + i))) 0 9 :=
  interval_of_check _ 0 9 (by decide +kernel)

public theorem complete : Block 21060 21069 :=
  block_of_table results 21060 9 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0476

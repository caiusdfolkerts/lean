module
prelude
import GraphInputsRow31Part00115Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0903
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 26126328004608), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record000_result⟩)
 (.leaf ⟨(31, 26132057423872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 26139206615040), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 26207890571264), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record003_result⟩)
 (.leaf ⟨(31, 26250859053056), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 26319584755712), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record005_result⟩)
 (.leaf ⟨(31, 26336756236288), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 26391807541504), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 26392080171136), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record008_result⟩)
 (.leaf ⟨(31, 26428349415424), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26448 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 26448 26458 :=
  block_of_table results 26448 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0903

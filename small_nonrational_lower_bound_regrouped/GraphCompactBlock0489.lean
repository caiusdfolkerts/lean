module
prelude
import GraphInputsRow29Part00055Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0489
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 10488993810448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 10490067550209), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record001_result⟩)
 (.leaf ⟨(29, 10498781249792), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 10585242603776), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 10585506844928), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record004_result⟩)
 (.leaf ⟨(29, 10601399058433), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 10639451881472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 10643736428544), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record007_result⟩)
 (.leaf ⟨(29, 10678094004992), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 10722677362944), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record009_result⟩)
 (.leaf ⟨(29, 10740371570816), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 10781580132352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record011_result⟩)
 (.leaf ⟨(29, 10781852696576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21299 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 21299 21312 :=
  block_of_table results 21299 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0489

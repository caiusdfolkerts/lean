module
prelude
import GraphInputsRow16Part00039Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0039
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 34674630524928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 34674638848000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record001_result⟩)
 (.leaf ⟨(16, 34674671878144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 34675150295040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record003_result⟩)
 (.leaf ⟨(16, 34675167330304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 34681911836672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record005_result⟩)
 (.leaf ⟨(16, 34681920159744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(16, 34682415091712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record007_result⟩)
 (.branch 9
 (.leaf ⟨(16, 34682431606784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record008_result⟩)
 (.leaf ⟨(16, 34682968408064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(16, 34682976731136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record010_result⟩)
 (.leaf ⟨(16, 34683471663104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record011_result⟩))
 (.branch 13
 (.leaf ⟨(16, 34683505082880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record012_result⟩)
 (.leaf ⟨(16, 34763482726400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2084 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 2084 2098 :=
  block_of_table results 2084 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0039

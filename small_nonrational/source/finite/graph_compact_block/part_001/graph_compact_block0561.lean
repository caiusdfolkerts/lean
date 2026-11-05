module
prelude
import GraphInputsRow29Part00127Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0561
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(29, 21446517096704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record000_result⟩)
 (.branch 2
 (.leaf ⟨(29, 21462623195264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record001_result⟩)
 (.leaf ⟨(29, 21514045391104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(29, 21514053779456), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record003_result⟩)
 (.branch 5
 (.leaf ⟨(29, 21514837623040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record004_result⟩)
 (.leaf ⟨(29, 21515110350848), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(29, 21515374493696), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 21515382816768), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record007_result⟩)
 (.leaf ⟨(29, 21518998372608), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 21519271002112), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record009_result⟩)
 (.leaf ⟨(29, 21519535243264), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 21519543566336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record011_result⟩)
 (.leaf ⟨(29, 21519667363840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22301 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 22301 22314 :=
  block_of_table results 22301 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0561

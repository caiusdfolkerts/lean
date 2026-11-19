module
prelude
import GraphInputsRow24Part00082Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0198
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 24458228285440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 24458362356224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record001_result⟩)
 (.leaf ⟨(24, 24467525894400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 24470918009088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record003_result⟩)
 (.leaf ⟨(24, 24471761092608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 24471827152896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record005_result⟩)
 (.leaf ⟨(24, 24484705763328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 24499721371904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 24499779012736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record008_result⟩)
 (.leaf ⟨(24, 24502123692032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 24504204066816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record010_result⟩)
 (.leaf ⟨(24, 24508494790912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 24508560851200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record012_result⟩)
 (.leaf ⟨(24, 24512789807104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082.record013_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10634 + i))) 0 14 :=
  interval_of_check _ 0 14 (by decide +kernel)

public theorem complete : Block 10634 10648 :=
  block_of_table results 10634 14 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0198

module
prelude
import GraphInputsRow23Part00036Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0114
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 34681902858240), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 34703353086208), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record001_result⟩)
 (.leaf ⟨(23, 34711943053312), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 34712479858688), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 34712999624704), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record004_result⟩)
 (.leaf ⟨(23, 34729105690624), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 34737716527104), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 34739046055936), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record007_result⟩)
 (.leaf ⟨(23, 34747896037376), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(23, 34763465424896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record009_result⟩)
 (.leaf ⟨(23, 34763498848256), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record010_result⟩))
 (.branch 12
 (.leaf ⟨(23, 34764539035648), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record011_result⟩)
 (.leaf ⟨(23, 34875159609344), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00036.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7769 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 7769 7782 :=
  block_of_table results 7769 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0114

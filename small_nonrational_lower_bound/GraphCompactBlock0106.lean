module
prelude
import GraphInputsRow23Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0106
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(23, 32488617410560), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record000_result⟩)
 (.branch 2
 (.leaf ⟨(23, 32491465408512), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record001_result⟩)
 (.leaf ⟨(23, 32492233424896), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(23, 32505457606912), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record003_result⟩)
 (.branch 5
 (.leaf ⟨(23, 32514051735552), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record004_result⟩)
 (.leaf ⟨(23, 32514588540928), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(23, 32515091922944), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record006_result⟩)
 (.branch 8
 (.leaf ⟨(23, 32522637475840), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record007_result⟩)
 (.leaf ⟨(23, 32522910040064), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(23, 32523372462080), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record009_result⟩)
 (.branch 11
 (.leaf ⟨(23, 32523677663232), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record010_result⟩)
 (.leaf ⟨(23, 32524445679616), Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028.record011_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7632 + i))) 0 12 :=
  interval_of_check _ 0 12 (by decide +kernel)

public theorem complete : Block 7632 7644 :=
  block_of_table results 7632 12 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0106

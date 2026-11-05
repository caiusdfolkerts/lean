module
prelude
import GraphInputsRow31Part00126Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0914
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 28674344648832), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record000_result⟩)
 (.leaf ⟨(31, 28674679144448), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 28692667465984), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 28697096683520), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record003_result⟩)
 (.leaf ⟨(31, 28697633488896), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 28701257433088), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record005_result⟩)
 (.leaf ⟨(31, 28701529997312), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 28701794238464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 28709847334912), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record008_result⟩)
 (.leaf ⟨(31, 28716220579840), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00126.record009_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26522 + i))) 0 10 :=
  interval_of_check _ 0 10 (by decide +kernel)

public theorem complete : Block 26522 26532 :=
  block_of_table results 26522 10 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0914

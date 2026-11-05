module
prelude
import GraphInputsRow24Part00167Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0283
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 34127952873488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_result⟩)
 (.leaf ⟨(24, 34155878973696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 34194419941376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 34195732692992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record003_result⟩)
 (.leaf ⟨(24, 34196261175296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(24, 34222385664256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record005_result⟩)
 (.branch 7
 (.leaf ⟨(24, 34222391955520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record006_result⟩)
 (.leaf ⟨(24, 34223424553216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(24, 34223943852096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record008_result⟩)
 (.branch 10
 (.leaf ⟨(24, 34239548622864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record009_result⟩)
 (.leaf ⟨(24, 34240604422144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record010_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12061 + i))) 0 11 :=
  interval_of_check _ 0 11 (by decide +kernel)

public theorem complete : Block 12061 12072 :=
  block_of_table results 12061 11 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0283

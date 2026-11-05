module
prelude
import GraphInputsRow24Part00159Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0275
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 32814355712000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 32822140209408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record001_result⟩)
 (.leaf ⟨(24, 32822677080064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 32822693724672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 32839319945732), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record004_result⟩)
 (.leaf ⟨(24, 32916646404352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 32916713570304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 32916721893376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record007_result⟩)
 (.leaf ⟨(24, 32917183275008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 32917233600512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record009_result⟩)
 (.leaf ⟨(24, 32918776973568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 32919313844224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record011_result⟩)
 (.leaf ⟨(24, 32919330488832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00159.record012_result⟩)))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11965 + i))) 0 13 :=
  interval_of_check _ 0 13 (by decide +kernel)

public theorem complete : Block 11965 11978 :=
  block_of_table results 11965 13 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0275

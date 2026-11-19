module
prelude
import GraphInputsRow31Part00070Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0858
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(31, 13377346732800), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record000_result⟩)
 (.leaf ⟨(31, 13377355186176), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record001_result⟩))
 (.branch 3
 (.leaf ⟨(31, 13385668231936), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record002_result⟩)
 (.branch 4
 (.leaf ⟨(31, 13385940926464), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record003_result⟩)
 (.leaf ⟨(31, 13385949249536), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(31, 13387484430592), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record005_result⟩)
 (.leaf ⟨(31, 13388218368544), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record006_result⟩))
 (.branch 8
 (.leaf ⟨(31, 13388219482112), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record007_result⟩)
 (.branch 9
 (.leaf ⟨(31, 13480158044416), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record008_result⟩)
 (.leaf ⟨(31, 13522842976512), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(31, 13523111444480), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record010_result⟩)
 (.leaf ⟨(31, 13523119767552), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record011_result⟩))
 (.branch 13
 (.leaf ⟨(31, 13523379847168), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record012_result⟩)
 (.branch 14
 (.leaf ⟨(31, 13523511967744), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record013_result⟩)
 (.leaf ⟨(31, 13524923351296), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(31, 13525658402816), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record015_result⟩)
 (.leaf ⟨(31, 13563574911232), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record016_result⟩))
 (.branch 18
 (.leaf ⟨(31, 13564313083904), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record017_result⟩)
 (.branch 19
 (.leaf ⟨(31, 13753862127872), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record018_result⟩)
 (.leaf ⟨(31, 13754130530560), Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00070.record019_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (26021 + i))) 0 20 :=
  interval_of_check _ 0 20 (by decide +kernel)

public theorem complete : Block 26021 26041 :=
  block_of_table results 26021 20 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0858

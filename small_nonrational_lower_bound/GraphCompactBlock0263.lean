module
prelude
import GraphInputsRow24Part00147Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0263
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 32332597969152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record000_result⟩)
 (.leaf ⟨(24, 32332606357504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 32333118048320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record002_result⟩)
 (.leaf ⟨(24, 32335198292032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 32335214936640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record004_result⟩)
 (.leaf ⟨(24, 32438986277120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 32438994665472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record006_result⟩)
 (.leaf ⟨(24, 32439217488128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 32439386800384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record008_result⟩)
 (.leaf ⟨(24, 32439391027200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 32439485890816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record010_result⟩)
 (.leaf ⟨(24, 32439497920512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 32441264832768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record012_result⟩)
 (.leaf ⟨(24, 32441273221120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 32441297862912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 32441533235456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record015_result⟩)
 (.leaf ⟨(24, 32441537462272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147.record016_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11850 + i))) 0 17 :=
  interval_of_check _ 0 17 (by decide +kernel)

public theorem complete : Block 11850 11867 :=
  block_of_table results 11850 17 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0263

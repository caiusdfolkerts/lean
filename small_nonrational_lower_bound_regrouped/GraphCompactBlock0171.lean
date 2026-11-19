module
prelude
import GraphInputsRow24Part00055Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0171
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 20574304796672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record000_result⟩)
 (.leaf ⟨(24, 20626989388032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 20629978906624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record002_result⟩)
 (.leaf ⟨(24, 20638694654080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 20685726449920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record004_result⟩)
 (.leaf ⟨(24, 20685726515200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 20685730644096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record006_result⟩)
 (.leaf ⟨(24, 20685732724864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 20685792510208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record008_result⟩)
 (.leaf ⟨(24, 20685792575488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 20685796704384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record010_result⟩)
 (.leaf ⟨(24, 20685924630784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 20685924696064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record012_result⟩)
 (.leaf ⟨(24, 20685926776832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 20685927817216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record014_result⟩)
 (.leaf ⟨(24, 20685930905728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 20685978077440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record016_result⟩)
 (.leaf ⟨(24, 20685982271616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 20686048331904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record018_result⟩)
 (.leaf ⟨(24, 20686193066112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 20686195146880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record020_result⟩)
 (.leaf ⟨(24, 20686195179520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 20688198959105), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record022_result⟩)
 (.leaf ⟨(24, 20688970713216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 20689144348672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record024_result⟩)
 (.leaf ⟨(24, 20689147469824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 20689168894080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record026_result⟩)
 (.leaf ⟨(24, 20689412718720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 20689415872512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record028_result⟩)
 (.leaf ⟨(24, 20693259389184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 20693707702272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record030_result⟩)
 (.leaf ⟨(24, 20693708742656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00055.record031_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9910 + i))) 0 32 :=
  interval_of_check _ 0 32 (by decide +kernel)

public theorem complete : Block 9910 9942 :=
  block_of_table results 9910 32 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0171

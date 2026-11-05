module
prelude
import GraphInputsRow24Part00001Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0117
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 751730524160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record000_result⟩)
 (.leaf ⟨(24, 751792357632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 751796519168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record002_result⟩)
 (.leaf ⟨(24, 751796584448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 752030916608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record004_result⟩)
 (.leaf ⟨(24, 776661401856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 818334105600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record006_result⟩)
 (.leaf ⟨(24, 819130794752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 819139183104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_result⟩)
 (.leaf ⟨(24, 873298231296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 873830875136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record010_result⟩)
 (.leaf ⟨(24, 874871062528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 939134058752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record012_result⟩)
 (.leaf ⟨(24, 939134124032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 947858194560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record014_result⟩)
 (.leaf ⟨(24, 952144789760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 952153178112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record016_result⟩)
 (.leaf ⟨(24, 956037136640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 956045524992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record018_result⟩)
 (.leaf ⟨(24, 956305539328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 956313927680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record020_result⟩)
 (.leaf ⟨(24, 956437659904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 956574007296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_result⟩)
 (.leaf ⟨(24, 956582330368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 977216307200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record024_result⟩)
 (.leaf ⟨(24, 1007851438336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 1009931813120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record026_result⟩)
 (.leaf ⟨(24, 1009931878400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(24, 1016443453568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record028_result⟩)
 (.leaf ⟨(24, 1025031307264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record029_result⟩))
 (.branch 31
 (.leaf ⟨(24, 1026566553856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_result⟩)
 (.branch 32
 (.leaf ⟨(24, 1026570585344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_result⟩)
 (.leaf ⟨(24, 1026843213825), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (7818 + i))) 0 33 :=
  interval_of_check _ 0 33 (by decide +kernel)

public theorem complete : Block 7818 7851 :=
  block_of_table results 7818 33 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0117

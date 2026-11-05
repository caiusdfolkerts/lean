module
prelude
import GraphInputsRow24Part00058Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0174
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 21124395057152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 21127515619328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record001_result⟩)
 (.leaf ⟨(24, 21235546226944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 21235603867776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 21244385706240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record004_result⟩)
 (.leaf ⟨(24, 21256936259584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 21306672168960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 21316594311232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record007_result⟩)
 (.leaf ⟨(24, 21333137178688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 21333205336064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record009_result⟩)
 (.leaf ⟨(24, 21333271396352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 21333273477120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record011_result⟩)
 (.leaf ⟨(24, 21342105634816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record012_result⟩)))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 21367596662784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 21367598743552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record014_result⟩)
 (.leaf ⟨(24, 21374057873664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record015_result⟩)))
 (.branch 17
 (.leaf ⟨(24, 21374062100480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 21374068342784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record017_result⟩)
 (.leaf ⟨(24, 21374192075008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record018_result⟩))))
 (.branch 22
 (.branch 20
 (.leaf ⟨(24, 21374200463360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record019_result⟩)
 (.branch 21
 (.leaf ⟨(24, 21374307680512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record020_result⟩)
 (.leaf ⟨(24, 21374317889536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 21374710333504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record022_result⟩)
 (.leaf ⟨(24, 21376208535552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 21376253853952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record024_result⟩)
 (.leaf ⟨(24, 21376266143744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00058.record025_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9993 + i))) 0 26 :=
  interval_of_check _ 0 26 (by decide +kernel)

public theorem complete : Block 9993 10019 :=
  block_of_table results 9993 26 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0174

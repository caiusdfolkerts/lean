module
prelude
import GraphInputsRow24Part00125Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0241
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 30864919592960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 30864922648832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record001_result⟩)
 (.leaf ⟨(24, 30865319010560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(24, 30865392410656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record003_result⟩)
 (.branch 5
 (.leaf ⟨(24, 30866466148384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record004_result⟩)
 (.leaf ⟨(24, 30873640509696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(24, 30896665133057), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 30898271750176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record007_result⟩)
 (.leaf ⟨(24, 30900752547840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record008_result⟩)))
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 30900825882625), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record009_result⟩)
 (.leaf ⟨(24, 30935115370560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 30942222647552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record011_result⟩)
 (.leaf ⟨(24, 30942222712832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record012_result⟩)))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ⟨(24, 30961951604992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record013_result⟩)
 (.branch 15
 (.leaf ⟨(24, 30961962074112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record014_result⟩)
 (.leaf ⟨(24, 30968401379328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record015_result⟩)))
 (.branch 18
 (.branch 17
 (.leaf ⟨(24, 30970541572096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record016_result⟩)
 (.leaf ⟨(24, 30976722878464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record017_result⟩))
 (.branch 19
 (.leaf ⟨(24, 30978863071232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record018_result⟩)
 (.leaf ⟨(24, 30979399876608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record019_result⟩))))
 (.branch 23
 (.branch 21
 (.leaf ⟨(24, 30986144382976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record020_result⟩)
 (.branch 22
 (.leaf ⟨(24, 31033894436864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record021_result⟩)
 (.leaf ⟨(24, 31033902759936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 31042488500224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record023_result⟩)
 (.leaf ⟨(24, 31046240338176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 31046574866432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record025_result⟩)
 (.leaf ⟨(24, 31046781370368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00125.record026_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11535 + i))) 0 27 :=
  interval_of_check _ 0 27 (by decide +kernel)

public theorem complete : Block 11535 11562 :=
  block_of_table results 11535 27 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0241

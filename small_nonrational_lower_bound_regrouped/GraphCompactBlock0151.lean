module
prelude
import GraphInputsRow24Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0151
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 16976153935872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record000_result⟩)
 (.leaf ⟨(24, 16976261218304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 16978023579904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record002_result⟩)
 (.leaf ⟨(24, 16978292047872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 16978300370944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record004_result⟩)
 (.leaf ⟨(24, 16978341593088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 16978811297792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record006_result⟩)
 (.leaf ⟨(24, 16982502342656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(24, 16982857482240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record008_result⟩)
 (.leaf ⟨(24, 16982972047360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record009_result⟩))
 (.branch 11
 (.leaf ⟨(24, 16985119261184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record010_result⟩)
 (.leaf ⟨(24, 17003775664128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(24, 17003842764800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record012_result⟩)
 (.leaf ⟨(24, 17010356453376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record013_result⟩))
 (.branch 15
 (.leaf ⟨(24, 17014789767168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 17023639748608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record015_result⟩)
 (.leaf ⟨(24, 17043798130944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 17043798196224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record017_result⟩)
 (.leaf ⟨(24, 17048105189632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 17048113577984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record019_result⟩)
 (.leaf ⟨(24, 17048604803328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 17048616833024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record021_result⟩)
 (.leaf ⟨(24, 17051314360320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 17051578536192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record023_result⟩)
 (.branch 25
 (.leaf ⟨(24, 17051578601472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record024_result⟩)
 (.leaf ⟨(24, 17051603175440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(24, 17052406448128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record026_result⟩)
 (.leaf ⟨(24, 17052497150208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record027_result⟩))
 (.branch 29
 (.leaf ⟨(24, 17052666462464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record028_result⟩)
 (.leaf ⟨(24, 17052670689280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 17052676915201), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record030_result⟩)
 (.leaf ⟨(24, 17052765552896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 17052777582592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 17056120967424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record033_result⟩)
 (.leaf ⟨(24, 17082431373568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00035.record034_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9328 + i))) 0 35 :=
  interval_of_check _ 0 35 (by decide +kernel)

public theorem complete : Block 9328 9363 :=
  block_of_table results 9328 35 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0151

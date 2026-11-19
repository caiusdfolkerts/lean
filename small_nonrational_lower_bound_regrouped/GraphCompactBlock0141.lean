module
prelude
import GraphInputsRow24Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0141
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 14630070059008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 14630606864384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record001_result⟩)
 (.leaf ⟨(24, 14678860300288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 14678868623360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record003_result⟩)
 (.leaf ⟨(24, 14683029372928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 14685299605504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record005_result⟩)
 (.leaf ⟨(24, 14699664048128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(24, 14699936612352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record007_result⟩)
 (.leaf ⟨(24, 14700465094656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record008_result⟩))
 (.branch 10
 (.leaf ⟨(24, 14701744422912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record009_result⟩)
 (.leaf ⟨(24, 14702016987136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(24, 14702479409152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record011_result⟩)
 (.leaf ⟨(24, 14709795356928), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record012_result⟩))
 (.branch 14
 (.leaf ⟨(24, 14709805826048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record013_result⟩)
 (.leaf ⟨(24, 14716245131264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record014_result⟩)))))
 (.branch 23
 (.branch 19
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 14724566630400), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record015_result⟩)
 (.leaf ⟨(24, 14733988134912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 14742762619136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record017_result⟩)
 (.leaf ⟨(24, 14743031021824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record018_result⟩)))
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 14743041490944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record019_result⟩)
 (.leaf ⟨(24, 14747445559296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 14749480796160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record021_result⟩)
 (.leaf ⟨(24, 14749521953024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record022_result⟩))))
 (.branch 27
 (.branch 25
 (.branch 24
 (.leaf ⟨(24, 14758066536448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record023_result⟩)
 (.leaf ⟨(24, 14768379461632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record024_result⟩))
 (.branch 26
 (.leaf ⟨(24, 14768387784704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record025_result⟩)
 (.leaf ⟨(24, 14768782065664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record026_result⟩)))
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 14781738188800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record027_result⟩)
 (.leaf ⟨(24, 14781746511872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 14786039382016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record029_result⟩)
 (.leaf ⟨(24, 14794084090112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00025.record030_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9013 + i))) 0 31 :=
  interval_of_check _ 0 31 (by decide +kernel)

public theorem complete : Block 9013 9044 :=
  block_of_table results 9013 31 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0141

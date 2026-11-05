module
prelude
import GraphInputsRow24Part00121Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0237
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 28813929103488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 28813935248384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record001_result⟩)
 (.leaf ⟨(24, 28827906834432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 28827913044096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record003_result⟩)
 (.leaf ⟨(24, 28827913076736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 28827914864768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record005_result⟩)
 (.leaf ⟨(24, 28828034402312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 28830106585088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 28830110713984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record008_result⟩)
 (.leaf ⟨(24, 28830114776072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 28830131552257), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record010_result⟩)
 (.leaf ⟨(24, 28830259544064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 28830511137800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record012_result⟩)
 (.leaf ⟨(24, 28841109159936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 28845069699200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 28864483999760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_result⟩)
 (.leaf ⟨(24, 28865508425856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 28865572405376), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record017_result⟩)
 (.leaf ⟨(24, 28865574486144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 28865574518784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record019_result⟩)
 (.leaf ⟨(24, 28869799215232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 28869803409408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record021_result⟩)
 (.leaf ⟨(24, 28869999476864), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 28874162339840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_result⟩)
 (.leaf ⟨(24, 28897703903360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 28897767882880), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_result⟩)
 (.leaf ⟨(24, 28897769963648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 28897769996288), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_result⟩)
 (.leaf ⟨(24, 28897821329536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11414 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 11414 11443 :=
  block_of_table results 11414 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0237

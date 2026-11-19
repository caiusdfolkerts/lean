module
prelude
import GraphInputsRow24Part00109Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0225
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 27189428945152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record000_result⟩)
 (.leaf ⟨(24, 27189701574656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 27191509319936), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record002_result⟩)
 (.leaf ⟨(24, 27192244371456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 27193862324224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record004_result⟩)
 (.leaf ⟨(24, 27194399129600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 27206881378304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 27208961753088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record007_result⟩)
 (.leaf ⟨(24, 27216247275648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 27216445456512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record009_result⟩)
 (.leaf ⟨(24, 27216478486656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 27224826740992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record011_result⟩)
 (.leaf ⟨(24, 27233416675456), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(24, 27248442753152), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record013_result⟩)
 (.leaf ⟨(24, 27248640934016), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record014_result⟩))
 (.branch 16
 (.leaf ⟨(24, 27248905175168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 27249714151552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record016_result⟩)
 (.leaf ⟨(24, 27249978392704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 27256417697920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record018_result⟩)
 (.leaf ⟨(24, 27267808002176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 27267812196352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record020_result⟩)
 (.leaf ⟨(24, 27267942203520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 27267948348416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record022_result⟩)
 (.leaf ⟨(24, 27268076274304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 27274183327872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 27351518822528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record025_result⟩)
 (.leaf ⟨(24, 27353054462080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 27384804032640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record027_result⟩)
 (.leaf ⟨(24, 27393637236992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 27398000148480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 27430212403200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record030_result⟩)
 (.leaf ⟨(24, 27525780668672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 27527865270272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record032_result⟩)
 (.leaf ⟨(24, 27527867285760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 27529008124160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 27532021793024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record035_result⟩)
 (.leaf ⟨(24, 27532025954560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00109.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11138 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 11138 11175 :=
  block_of_table results 11138 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0225

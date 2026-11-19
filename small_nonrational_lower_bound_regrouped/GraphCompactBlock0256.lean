module
prelude
import GraphInputsRow24Part00140Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0256
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 31819283071232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 31819353358336), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record001_result⟩)
 (.leaf ⟨(24, 31819361681408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 31819551539200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record003_result⟩)
 (.leaf ⟨(24, 31819559862272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 31819601084416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record005_result⟩)
 (.leaf ⟨(24, 31820070789120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 31825725497600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 31826262368256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record008_result⟩)
 (.leaf ⟨(24, 31826311913472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 31827855286528), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record010_result⟩)
 (.leaf ⟨(24, 31828459127296), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 31842887671840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record012_result⟩)
 (.leaf ⟨(24, 31889171693824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 31889369874688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 31889634115840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record015_result⟩)
 (.leaf ⟨(24, 31889674997824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 31890426368032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record017_result⟩)
 (.leaf ⟨(24, 31890690609184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 31891386278144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record019_result⟩)
 (.leaf ⟨(24, 31891482939424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(24, 31896114303040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 31904435802176), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record022_result⟩)
 (.leaf ⟨(24, 31922638569728), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 31922910662720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record024_result⟩)
 (.leaf ⟨(24, 31925771239680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 31926237823232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record026_result⟩)
 (.leaf ⟨(24, 31927311040768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00140.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11760 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 11760 11788 :=
  block_of_table results 11760 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0256

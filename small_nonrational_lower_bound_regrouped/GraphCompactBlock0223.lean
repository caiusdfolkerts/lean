module
prelude
import GraphInputsRow24Part00107Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0223
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 26735442673792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 26768678338688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record001_result⟩)
 (.leaf ⟨(24, 26768942579840), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 26794220732544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record003_result⟩)
 (.leaf ⟨(24, 26846030741760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 26982406439168), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record005_result⟩)
 (.leaf ⟨(24, 27015634297088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 27015902699776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 27016759935232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record008_result⟩)
 (.leaf ⟨(24, 27016833278208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 27049995600128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record010_result⟩)
 (.leaf ⟨(24, 27052258427136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 27052266815488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record012_result⟩)
 (.leaf ⟨(24, 27094068248832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 27094136398080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 27095977722112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record015_result⟩)
 (.leaf ⟨(24, 27096514592768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 27096518754304), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record017_result⟩)
 (.leaf ⟨(24, 27111470416000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 27119834956032), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record019_result⟩)
 (.leaf ⟨(24, 27120984195072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(24, 27121783210240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 27122055839744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record022_result⟩)
 (.leaf ⟨(24, 27122320080896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 27122328403968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record024_result⟩)
 (.leaf ⟨(24, 27122452201472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 27123122241792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record026_result⟩)
 (.leaf ⟨(24, 27128710070272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00107.record027_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (11100 + i))) 0 28 :=
  interval_of_check _ 0 28 (by decide +kernel)

public theorem complete : Block 11100 11128 :=
  block_of_table results 11100 28 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0223

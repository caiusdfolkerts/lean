module
prelude
import GraphInputsRow24Part00027Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0143
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(24, 15214654259200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record000_result⟩)
 (.branch 2
 (.leaf ⟨(24, 15214720319488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record001_result⟩)
 (.leaf ⟨(24, 15230520262656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(24, 15230759665664), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record003_result⟩)
 (.leaf ⟨(24, 15247134064896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record004_result⟩))
 (.branch 6
 (.leaf ⟨(24, 15247939207680), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record005_result⟩)
 (.leaf ⟨(24, 15247955984384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(24, 15259083538688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 15259356168192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record008_result⟩)
 (.leaf ⟨(24, 15259620409344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 15259628732416), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record010_result⟩)
 (.leaf ⟨(24, 15261163913472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 15261436542976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record012_result⟩)
 (.leaf ⟨(24, 15261700784128), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(24, 15261709107200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record014_result⟩)
 (.branch 16
 (.leaf ⟨(24, 15261898964992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record015_result⟩)
 (.leaf ⟨(24, 15262476730368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(24, 15262740971520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record017_result⟩)
 (.leaf ⟨(24, 15262749294592), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record018_result⟩))
 (.branch 20
 (.leaf ⟨(24, 15266001977344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record019_result⟩)
 (.leaf ⟨(24, 15266059714560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record020_result⟩))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ⟨(24, 15267042164736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record021_result⟩)
 (.leaf ⟨(24, 15268643406080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record022_result⟩))
 (.branch 24
 (.leaf ⟨(24, 15274046685440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record023_result⟩)
 (.leaf ⟨(24, 15274381213696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record024_result⟩)))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 15274587717632), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record025_result⟩)
 (.leaf ⟨(24, 15277233307904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 15278004510720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record027_result⟩)
 (.leaf ⟨(24, 15285823275008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00027.record028_result⟩))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (9089 + i))) 0 29 :=
  interval_of_check _ 0 29 (by decide +kernel)

public theorem complete : Block 9089 9118 :=
  block_of_table results 9089 29 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0143

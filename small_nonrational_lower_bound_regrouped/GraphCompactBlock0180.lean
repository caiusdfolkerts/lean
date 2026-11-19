module
prelude
import GraphInputsRow24Part00064Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0180
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 23014716669952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record000_result⟩)
 (.leaf ⟨(24, 23014724993024), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 23015119273984), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record002_result⟩)
 (.leaf ⟨(24, 23015253344768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 23028075397120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record004_result⟩)
 (.leaf ⟨(24, 23095693901856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 23099988852768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 23108574593056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record007_result⟩)
 (.leaf ⟨(24, 23129818726656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record008_result⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 23130087129344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record009_result⟩)
 (.leaf ⟨(24, 23130087194624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 23130089210112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record011_result⟩)
 (.leaf ⟨(24, 23133979476224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record012_result⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(24, 23134382080256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record013_result⟩)
 (.leaf ⟨(24, 23134382145536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record014_result⟩))
 (.branch 16
 (.leaf ⟨(24, 23137603293440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record015_result⟩)
 (.branch 17
 (.leaf ⟨(24, 23142565216512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record016_result⟩)
 (.leaf ⟨(24, 23142569378048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record017_result⟩))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ⟨(24, 23142569443328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record018_result⟩)
 (.leaf ⟨(24, 23142571458816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record019_result⟩))
 (.branch 21
 (.leaf ⟨(24, 23142703579392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record020_result⟩)
 (.leaf ⟨(24, 23142703644672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record021_result⟩)))
 (.branch 24
 (.branch 23
 (.leaf ⟨(24, 23142769704960), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record022_result⟩)
 (.leaf ⟨(24, 23142967820544), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record023_result⟩))
 (.branch 25
 (.leaf ⟨(24, 23142974111808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record024_result⟩)
 (.branch 26
 (.leaf ⟨(24, 23143041212480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record025_result⟩)
 (.leaf ⟨(24, 23144114950208), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record026_result⟩)))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ⟨(24, 23163321286688), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record027_result⟩)
 (.leaf ⟨(24, 23167616237600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record028_result⟩))
 (.branch 30
 (.leaf ⟨(24, 23176201977888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record029_result⟩)
 (.branch 31
 (.leaf ⟨(24, 23177062269184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record030_result⟩)
 (.leaf ⟨(24, 23211883380992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record031_result⟩))))
 (.branch 34
 (.branch 33
 (.leaf ⟨(24, 23214970405120), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record032_result⟩)
 (.leaf ⟨(24, 23219736215808), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record033_result⟩))
 (.branch 35
 (.leaf ⟨(24, 23220273086464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record034_result⟩)
 (.branch 36
 (.leaf ⟨(24, 23220281409536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record035_result⟩)
 (.leaf ⟨(24, 23234240057600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00064.record036_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (10214 + i))) 0 37 :=
  interval_of_check _ 0 37 (by decide +kernel)

public theorem complete : Block 10214 10251 :=
  block_of_table results 10214 37 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0180

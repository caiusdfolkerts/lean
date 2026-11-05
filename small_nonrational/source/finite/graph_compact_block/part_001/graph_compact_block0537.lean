module
prelude
import GraphInputsRow29Part00103Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0537
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 22
 (.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 17532610150400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record000_result⟩)
 (.leaf ⟨(29, 17549236502528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 17566953111552), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record002_result⟩)
 (.branch 4
 (.leaf ⟨(29, 17595714584896), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record003_result⟩)
 (.leaf ⟨(29, 17595718746432), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record004_result⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨(29, 17631130755392), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record005_result⟩)
 (.branch 7
 (.leaf ⟨(29, 17632191488320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record006_result⟩)
 (.leaf ⟨(29, 17632529055872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record007_result⟩)))
 (.branch 9
 (.leaf ⟨(29, 17632531152960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record008_result⟩)
 (.branch 10
 (.leaf ⟨(29, 17636621631744), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record009_result⟩)
 (.leaf ⟨(29, 17636824006784), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record010_result⟩)))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf ⟨(29, 17636824023104), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record011_result⟩)
 (.leaf ⟨(29, 17640010629248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record012_result⟩))
 (.branch 14
 (.leaf ⟨(29, 17640010645568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record013_result⟩)
 (.branch 15
 (.leaf ⟨(29, 17672222900288), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record014_result⟩)
 (.leaf ⟨(29, 17701980406532), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record015_result⟩))))
 (.branch 19
 (.branch 17
 (.leaf ⟨(29, 17702053773568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 17702253199488), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record017_result⟩)
 (.leaf ⟨(29, 17702391415040), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record018_result⟩)))
 (.branch 20
 (.leaf ⟨(29, 17704149926144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record019_result⟩)
 (.branch 21
 (.leaf ⟨(29, 17704418361472), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record020_result⟩)
 (.leaf ⟨(29, 17706413785856), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record021_result⟩))))))
 (.branch 33
 (.branch 27
 (.branch 24
 (.branch 23
 (.leaf ⟨(29, 17706417979648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record022_result⟩)
 (.leaf ⟨(29, 17706548150400), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record023_result⟩))
 (.branch 25
 (.leaf ⟨(29, 17706548166720), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record024_result⟩)
 (.branch 26
 (.leaf ⟨(29, 17706684285184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record025_result⟩)
 (.leaf ⟨(29, 17706686382336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record026_result⟩))))
 (.branch 30
 (.branch 28
 (.leaf ⟨(29, 17706686447616), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record027_result⟩)
 (.branch 29
 (.leaf ⟨(29, 17706820583680), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record028_result⟩)
 (.leaf ⟨(29, 17715005784320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record029_result⟩)))
 (.branch 31
 (.leaf ⟨(29, 17715274219648), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record030_result⟩)
 (.branch 32
 (.leaf ⟨(29, 17717423775872), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record031_result⟩)
 (.leaf ⟨(29, 17721852960832), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record032_result⟩)))))
 (.branch 38
 (.branch 35
 (.branch 34
 (.leaf ⟨(29, 17739902173248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record033_result⟩)
 (.leaf ⟨(29, 17740942360640), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record034_result⟩))
 (.branch 36
 (.leaf ⟨(29, 17743089836096), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record035_result⟩)
 (.branch 37
 (.leaf ⟨(29, 17775135359232), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record036_result⟩)
 (.leaf ⟨(29, 17775267627072), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record037_result⟩))))
 (.branch 41
 (.branch 39
 (.leaf ⟨(29, 17775403761920), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record038_result⟩)
 (.branch 40
 (.leaf ⟨(29, 17775403827200), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record039_result⟩)
 (.leaf ⟨(29, 17775405842688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record040_result⟩)))
 (.branch 42
 (.leaf ⟨(29, 17777415102528), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record041_result⟩)
 (.branch 43
 (.leaf ⟨(29, 17777484136704), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record042_result⟩)
 (.leaf ⟨(29, 17783725326336), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00103.record043_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (21961 + i))) 0 44 :=
  interval_of_check _ 0 44 (by decide +kernel)

public theorem complete : Block 21961 22005 :=
  block_of_table results 21961 44 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0537

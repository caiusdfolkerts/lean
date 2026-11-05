module
prelude
import GraphInputsRow29Part00132Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0566
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(29, 22030575501568), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record000_result⟩)
 (.leaf ⟨(29, 22033744863296), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record001_result⟩))
 (.branch 3
 (.leaf ⟨(29, 22034801434688), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record002_result⟩)
 (.leaf ⟨(29, 22034872549632), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(29, 22065974378752), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record004_result⟩)
 (.leaf ⟨(29, 22077820117120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record005_result⟩))
 (.branch 7
 (.leaf ⟨(29, 22100299645184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record006_result⟩)
 (.branch 8
 (.leaf ⟨(29, 22100563788032), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record007_result⟩)
 (.leaf ⟨(29, 22100572176384), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(29, 22104460296448), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record009_result⟩)
 (.leaf ⟨(29, 22104724537600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record010_result⟩))
 (.branch 12
 (.leaf ⟨(29, 22104732925952), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record011_result⟩)
 (.branch 13
 (.leaf ⟨(29, 22104856658176), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record012_result⟩)
 (.leaf ⟨(29, 22107003093248), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(29, 22111055782016), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record014_result⟩)
 (.leaf ⟨(29, 22113046036736), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record015_result⟩))
 (.branch 17
 (.leaf ⟨(29, 22113054425088), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record016_result⟩)
 (.branch 18
 (.leaf ⟨(29, 22113457029120), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record017_result⟩)
 (.leaf ⟨(29, 22115604504576), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(29, 22119887945984), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record019_result⟩)
 (.leaf ⟨(29, 22137948619008), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record020_result⟩))
 (.branch 22
 (.leaf ⟨(29, 22146270118144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record021_result⟩)
 (.leaf ⟨(29, 22173441917184), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(29, 22173450305536), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record023_result⟩)
 (.leaf ⟨(29, 22175588352256), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record024_result⟩))
 (.branch 26
 (.leaf ⟨(29, 22181763416320), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record025_result⟩)
 (.branch 27
 (.leaf ⟨(29, 22181771804672), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record026_result⟩)
 (.leaf ⟨(29, 22182042288128), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(29, 22182166020352), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record028_result⟩)
 (.leaf ⟨(29, 22218672185600), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record029_result⟩))
 (.branch 31
 (.leaf ⟨(29, 22283704877312), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_result⟩)
 (.branch 32
 (.leaf ⟨(29, 22312758870272), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record031_result⟩)
 (.leaf ⟨(29, 22313027272960), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(29, 22313038782464), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record033_result⟩)
 (.leaf ⟨(29, 22313161474304), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record034_result⟩))
 (.branch 36
 (.leaf ⟨(29, 22319202337024), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record035_result⟩)
 (.branch 37
 (.leaf ⟨(29, 22319206563840), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record036_result⟩)
 (.leaf ⟨(29, 22319212806144), Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record037_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (22350 + i))) 0 38 :=
  interval_of_check _ 0 38 (by decide +kernel)

public theorem complete : Block 22350 22388 :=
  block_of_table results 22350 38 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0566

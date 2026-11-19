module
prelude
import GraphInputsRow26Part00055Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0371
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 26113695027264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record000_result⟩)
 (.leaf ⟨(26, 26130719574032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 26188600901632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record002_result⟩)
 (.branch 4
 (.leaf ⟨(26, 26220796379136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record003_result⟩)
 (.leaf ⟨(26, 26319584888832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(26, 26320096593928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record005_result⟩)
 (.leaf ⟨(26, 26320113238536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record006_result⟩))
 (.branch 8
 (.leaf ⟨(26, 26393820864896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 26393952985472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record008_result⟩)
 (.leaf ⟨(26, 26427221680512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 26461583515936), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record010_result⟩)
 (.leaf ⟨(26, 26461584036128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 26461634365712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record012_result⟩)
 (.branch 14
 (.leaf ⟨(26, 26467003089152), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record013_result⟩)
 (.leaf ⟨(26, 26500238754048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 26501635391616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 26512365486208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record016_result⟩)
 (.leaf ⟨(26, 26512633921536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(26, 26512638083072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record018_result⟩)
 (.branch 20
 (.leaf ⟨(26, 26580690698240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record019_result⟩)
 (.leaf ⟨(26, 26648747474944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(26, 26648751636480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record021_result⟩)
 (.leaf ⟨(26, 26657052229632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record022_result⟩))
 (.branch 24
 (.leaf ⟨(26, 26700951863424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record023_result⟩)
 (.branch 25
 (.leaf ⟨(26, 26703230419072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record024_result⟩)
 (.leaf ⟨(26, 26718121263232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 26718125457408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record026_result⟩)
 (.leaf ⟨(26, 26721241825408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 26725604950016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 26735442673792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record029_result⟩)
 (.leaf ⟨(26, 26768678338688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(26, 26768942579840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record031_result⟩)
 (.leaf ⟨(26, 26794220732544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record032_result⟩))
 (.branch 34
 (.leaf ⟨(26, 26846030741760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record033_result⟩)
 (.branch 35
 (.leaf ⟨(26, 27015902699776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record034_result⟩)
 (.leaf ⟨(26, 27094068248832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(26, 27096514592768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record036_result⟩)
 (.branch 38
 (.leaf ⟨(26, 27096518754304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record037_result⟩)
 (.leaf ⟨(26, 27111470416000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(26, 27120984195072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record039_result⟩)
 (.branch 41
 (.leaf ⟨(26, 27122320080896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record040_result⟩)
 (.leaf ⟨(26, 27122328403968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00055.record041_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (16826 + i))) 0 42 :=
  interval_of_check _ 0 42 (by decide +kernel)

public theorem complete : Block 16826 16868 :=
  block_of_table results 16826 42 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0371

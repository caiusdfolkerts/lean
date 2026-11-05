module
prelude
import GraphInputsRow26Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0329
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 8041321955336), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 8041412985088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record001_result⟩)
 (.leaf ⟨(26, 8041413050368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 8041466431744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record003_result⟩)
 (.leaf ⟨(26, 8041809412096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 8041866987648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record005_result⟩)
 (.leaf ⟨(26, 8044785174784), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(26, 8045032185856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record007_result⟩)
 (.leaf ⟨(26, 8046164049921), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record008_result⟩))
 (.branch 10
 (.leaf ⟨(26, 8067227910144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record009_result⟩)
 (.leaf ⟨(26, 8067236233216), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(26, 8067368353792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record011_result⟩)
 (.leaf ⟨(26, 8067632594944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record012_result⟩))
 (.branch 14
 (.leaf ⟨(26, 8067828695040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record013_result⟩)
 (.leaf ⟨(26, 8135953612800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(26, 8136413954048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record015_result⟩)
 (.branch 17
 (.leaf ⟨(26, 8139074174976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record016_result⟩)
 (.leaf ⟨(26, 8139140235264), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(26, 8139534516224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record018_result⟩)
 (.leaf ⟨(26, 8147848724480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record019_result⟩))
 (.branch 21
 (.leaf ⟨(26, 8148224344320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record020_result⟩)
 (.leaf ⟨(26, 8148236634112), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(26, 8152412078080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record022_result⟩)
 (.leaf ⟨(26, 8152519295232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record023_result⟩))
 (.branch 25
 (.leaf ⟨(26, 8152529504256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record024_result⟩)
 (.leaf ⟨(26, 8160851003392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(26, 8165538136640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record026_result⟩)
 (.leaf ⟨(26, 8173322912000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record027_result⟩))
 (.branch 29
 (.leaf ⟨(26, 8173457178624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record028_result⟩)
 (.leaf ⟨(26, 8173465501696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(26, 8173859782656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 8173993853440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record031_result⟩)
 (.leaf ⟨(26, 8180060979200), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 8180331462656), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record033_result⟩)
 (.leaf ⟨(26, 8180436599040), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 8180448888832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record035_result⟩)
 (.leaf ⟨(26, 8182207414272), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(26, 8182471655424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record037_result⟩)
 (.leaf ⟨(26, 8184735531008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record038_result⟩))
 (.branch 40
 (.leaf ⟨(26, 8186762379520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record039_result⟩)
 (.leaf ⟨(26, 8186764525568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(26, 8186770767872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record041_result⟩)
 (.leaf ⟨(26, 8186811924736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record042_result⟩))
 (.branch 44
 (.leaf ⟨(26, 8186822133760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record043_result⟩)
 (.leaf ⟨(26, 8195011512320), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record044_result⟩)))))
 (.branch 53
 (.branch 49
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 8195143632896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record045_result⟩)
 (.leaf ⟨(26, 8247975182352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 8251194834960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record047_result⟩)
 (.leaf ⟨(26, 8256581894144), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record048_result⟩)))
 (.branch 51
 (.branch 50
 (.leaf ⟨(26, 8324209278976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record049_result⟩)
 (.leaf ⟨(26, 8334128185345), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record050_result⟩))
 (.branch 52
 (.leaf ⟨(26, 8337349414912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record051_result⟩)
 (.leaf ⟨(26, 8371709149184), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record052_result⟩))))
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf ⟨(26, 8402713444353), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record053_result⟩)
 (.leaf ⟨(26, 8509143908352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record054_result⟩))
 (.branch 56
 (.leaf ⟨(26, 8517465407488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record055_result⟩)
 (.leaf ⟨(26, 8525787105296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record056_result⟩)))
 (.branch 59
 (.branch 58
 (.leaf ⟨(26, 8534783692800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record057_result⟩)
 (.leaf ⟨(26, 8569143427072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record058_result⟩))
 (.branch 60
 (.leaf ⟨(26, 8637992927232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record059_result⟩)
 (.leaf ⟨(26, 8650202611712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00013.record060_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14710 + i))) 0 61 :=
  interval_of_check _ 0 61 (by decide +kernel)

public theorem complete : Block 14710 14771 :=
  block_of_table results 14710 61 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0329

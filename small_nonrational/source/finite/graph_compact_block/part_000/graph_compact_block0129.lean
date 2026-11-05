module
prelude
import GraphInputsRow24Part00013Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0129
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 41
 (.branch 20
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 8067632594944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record000_result⟩)
 (.leaf ⟨(24, 8067828695040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 8112532684800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record002_result⟩)
 (.branch 4
 (.leaf ⟨(24, 8112803168256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record003_result⟩)
 (.leaf ⟨(24, 8114613059584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(24, 8119176413184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record005_result⟩)
 (.leaf ⟨(24, 8131178930240), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record006_result⟩))
 (.branch 8
 (.leaf ⟨(24, 8135953612800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record007_result⟩)
 (.branch 9
 (.leaf ⟨(24, 8136413954048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record008_result⟩)
 (.leaf ⟨(24, 8138997645568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(24, 8139065851904), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record010_result⟩)
 (.leaf ⟨(24, 8139074174976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record011_result⟩))
 (.branch 13
 (.leaf ⟨(24, 8139140235264), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record012_result⟩)
 (.branch 14
 (.leaf ⟨(24, 8139534516224), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record013_result⟩)
 (.leaf ⟨(24, 8147848724480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record014_result⟩))))
 (.branch 17
 (.branch 16
 (.leaf ⟨(24, 8148224344320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record015_result⟩)
 (.leaf ⟨(24, 8148236634112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record016_result⟩))
 (.branch 18
 (.leaf ⟨(24, 8152412078080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record017_result⟩)
 (.branch 19
 (.leaf ⟨(24, 8152519295232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record018_result⟩)
 (.leaf ⟨(24, 8152529504256), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record019_result⟩))))))
 (.branch 30
 (.branch 25
 (.branch 22
 (.branch 21
 (.leaf ⟨(24, 8160851003392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record020_result⟩)
 (.leaf ⟨(24, 8165538136640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record021_result⟩))
 (.branch 23
 (.leaf ⟨(24, 8173322912000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record022_result⟩)
 (.branch 24
 (.leaf ⟨(24, 8173457178624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record023_result⟩)
 (.leaf ⟨(24, 8173465501696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record024_result⟩))))
 (.branch 27
 (.branch 26
 (.leaf ⟨(24, 8173859782656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record025_result⟩)
 (.leaf ⟨(24, 8173993853440), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record026_result⟩))
 (.branch 28
 (.leaf ⟨(24, 8179920470272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record027_result⟩)
 (.branch 29
 (.leaf ⟨(24, 8179928858624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record028_result⟩)
 (.leaf ⟨(24, 8180052590848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record029_result⟩)))))
 (.branch 35
 (.branch 32
 (.branch 31
 (.leaf ⟨(24, 8180060979200), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record030_result⟩)
 (.leaf ⟨(24, 8180325220352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record031_result⟩))
 (.branch 33
 (.leaf ⟨(24, 8180331462656), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record032_result⟩)
 (.branch 34
 (.leaf ⟨(24, 8180436599040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record033_result⟩)
 (.leaf ⟨(24, 8180448888832), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(24, 8180570800384), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record035_result⟩)
 (.branch 37
 (.leaf ⟨(24, 8182207414272), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record036_result⟩)
 (.leaf ⟨(24, 8182248571136), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record037_result⟩)))
 (.branch 39
 (.leaf ⟨(24, 8182471655424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record038_result⟩)
 (.branch 40
 (.leaf ⟨(24, 8182516973824), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record039_result⟩)
 (.leaf ⟨(24, 8182529263616), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record040_result⟩)))))))
 (.branch 61
 (.branch 51
 (.branch 46
 (.branch 43
 (.branch 42
 (.leaf ⟨(24, 8184735531008), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record041_result⟩)
 (.leaf ⟨(24, 8186409320704), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record042_result⟩))
 (.branch 44
 (.leaf ⟨(24, 8186762379520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record043_result⟩)
 (.branch 45
 (.leaf ⟨(24, 8186764525568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record044_result⟩)
 (.leaf ⟨(24, 8186770767872), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record045_result⟩))))
 (.branch 48
 (.branch 47
 (.leaf ⟨(24, 8186811924736), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record046_result⟩)
 (.leaf ⟨(24, 8186822133760), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record047_result⟩))
 (.branch 49
 (.leaf ⟨(24, 8189026239232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record048_result⟩)
 (.branch 50
 (.leaf ⟨(24, 8195011512320), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record049_result⟩)
 (.leaf ⟨(24, 8195143632896), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record050_result⟩)))))
 (.branch 56
 (.branch 53
 (.branch 52
 (.leaf ⟨(24, 8195356508160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record051_result⟩)
 (.leaf ⟨(24, 8195407874048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record052_result⟩))
 (.branch 54
 (.leaf ⟨(24, 8195603177536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record053_result⟩)
 (.branch 55
 (.leaf ⟨(24, 8197750391360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record054_result⟩)
 (.leaf ⟨(24, 8252289024000), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record055_result⟩))))
 (.branch 58
 (.branch 57
 (.leaf ⟨(24, 8256581894144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record056_result⟩)
 (.leaf ⟨(24, 8256684560640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record057_result⟩))
 (.branch 59
 (.leaf ⟨(24, 8265167634432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record058_result⟩)
 (.branch 60
 (.leaf ⟨(24, 8265408712768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record059_result⟩)
 (.leaf ⟨(24, 8324209278976), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record060_result⟩))))))
 (.branch 71
 (.branch 66
 (.branch 63
 (.branch 62
 (.leaf ⟨(24, 8324212855040), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record061_result⟩)
 (.leaf ⟨(24, 8333054445584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record062_result⟩))
 (.branch 64
 (.leaf ⟨(24, 8334128185345), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record063_result⟩)
 (.branch 65
 (.leaf ⟨(24, 8337337385216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record064_result⟩)
 (.leaf ⟨(24, 8337349414912), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record065_result⟩))))
 (.branch 68
 (.branch 67
 (.leaf ⟨(24, 8371700826112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record066_result⟩)
 (.leaf ⟨(24, 8371709149184), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record067_result⟩))
 (.branch 69
 (.leaf ⟨(24, 8402713444353), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record068_result⟩)
 (.branch 70
 (.leaf ⟨(24, 8509143908352), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record069_result⟩)
 (.leaf ⟨(24, 8517465407488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record070_result⟩)))))
 (.branch 76
 (.branch 73
 (.branch 72
 (.leaf ⟨(24, 8530371285056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record071_result⟩)
 (.leaf ⟨(24, 8534783692800), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record072_result⟩))
 (.branch 74
 (.leaf ⟨(24, 8538810222608), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record073_result⟩)
 (.branch 75
 (.leaf ⟨(24, 8569143427072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record074_result⟩)
 (.leaf ⟨(24, 8615773634816), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record075_result⟩))))
 (.branch 79
 (.branch 77
 (.leaf ⟨(24, 8637992927232), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record076_result⟩)
 (.branch 78
 (.leaf ⟨(24, 8650202611712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record077_result⟩)
 (.leaf ⟨(24, 8654635925504), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record078_result⟩)))
 (.branch 80
 (.leaf ⟨(24, 8727398909952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record079_result⟩)
 (.branch 81
 (.leaf ⟨(24, 8727659086080), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record080_result⟩)
 (.leaf ⟨(24, 8727667474432), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00013.record081_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8462 + i))) 0 82 :=
  interval_of_check _ 0 82 (by decide +kernel)

public theorem complete : Block 8462 8544 :=
  block_of_table results 8462 82 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0129

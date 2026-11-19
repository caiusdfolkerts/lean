module
prelude
import GraphInputsRow19Part00035Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0075
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 32806035129344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record000_result⟩)
 (.leaf ⟨(19, 32813571311616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 32990890598656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record002_result⟩)
 (.leaf ⟨(19, 33022011818240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(19, 33029700468736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record004_result⟩)
 (.leaf ⟨(19, 33034104537088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record005_result⟩))
 (.branch 7
 (.leaf ⟨(19, 33034112860160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record006_result⟩)
 (.leaf ⟨(19, 33066316791808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(19, 33066325114880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record008_result⟩)
 (.leaf ⟨(19, 33068132925440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record009_result⟩))
 (.branch 11
 (.leaf ⟨(19, 33068330000640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record010_result⟩)
 (.leaf ⟨(19, 33068363030784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(19, 33093012955392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record012_result⟩)
 (.leaf ⟨(19, 33101368590336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record013_result⟩))
 (.branch 15
 (.leaf ⟨(19, 33102458191872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record014_result⟩)
 (.leaf ⟨(19, 33102655267072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(19, 33102664565760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record016_result⟩)
 (.leaf ⟨(19, 33132536938752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record017_result⟩))
 (.branch 19
 (.leaf ⟨(19, 33133073809408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record018_result⟩)
 (.leaf ⟨(19, 33158292768832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(19, 33192737251584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record020_result⟩)
 (.leaf ⟨(19, 33193761704192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record021_result⟩))
 (.branch 23
 (.leaf ⟨(19, 33193810469120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record022_result⟩)
 (.leaf ⟨(19, 33195908139264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(19, 33196089024768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record024_result⟩)
 (.leaf ⟨(19, 33196089090048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record025_result⟩))
 (.branch 27
 (.leaf ⟨(19, 33196096364576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record026_result⟩)
 (.leaf ⟨(19, 33196096884768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(19, 33198235459840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record028_result⟩)
 (.leaf ⟨(19, 33204443554048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record029_result⟩))
 (.branch 31
 (.leaf ⟨(19, 33204451942400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record030_result⟩)
 (.leaf ⟨(19, 33204476584192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(19, 33204477689856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record032_result⟩)
 (.leaf ⟨(19, 33204484972544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record033_result⟩))
 (.branch 35
 (.leaf ⟨(19, 33204946346016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record034_result⟩)
 (.leaf ⟨(19, 33204996411424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(19, 33205541543936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record036_result⟩)
 (.leaf ⟨(19, 33206581731328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record037_result⟩))
 (.branch 39
 (.leaf ⟨(19, 33206582641664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record038_result⟩)
 (.leaf ⟨(19, 33206615671808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(19, 33207076655136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record040_result⟩)
 (.leaf ⟨(19, 33207078093824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record041_result⟩))
 (.branch 43
 (.leaf ⟨(19, 33226022526976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record042_result⟩)
 (.leaf ⟨(19, 33230439842824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(19, 33230456619009), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record044_result⟩)
 (.leaf ⟨(19, 33537407881472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record045_result⟩))
 (.branch 47
 (.leaf ⟨(19, 33537540002048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record046_result⟩)
 (.leaf ⟨(19, 33538464452864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(19, 33581678788608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record048_result⟩)
 (.leaf ⟨(19, 33605187805440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record049_result⟩))
 (.branch 51
 (.leaf ⟨(19, 33613807681536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record050_result⟩)
 (.leaf ⟨(19, 33613816004608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(19, 33673773064448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record052_result⟩)
 (.leaf ⟨(19, 33685487755264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record053_result⟩))
 (.branch 55
 (.leaf ⟨(19, 33686535938304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record054_result⟩)
 (.leaf ⟨(19, 33686544326656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(19, 33687072670240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record056_result⟩)
 (.leaf ⟨(19, 33741317873920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record057_result⟩))
 (.branch 59
 (.leaf ⟨(19, 33741317939200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record058_result⟩)
 (.leaf ⟨(19, 33741318654208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(19, 33741557205024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record060_result⟩)
 (.leaf ⟨(19, 33742408255744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record061_result⟩))
 (.branch 63
 (.leaf ⟨(19, 33742408321024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record062_result⟩)
 (.leaf ⟨(19, 33749895088160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00035.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (5435 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 5435 5499 :=
  block_of_table results 5435 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0075

module
prelude
import GraphInputsRow25Part00022Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0312
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(25, 31819336581120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record000_result⟩)
 (.leaf ⟨(25, 31827930644480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record001_result⟩))
 (.branch 3
 (.leaf ⟨(25, 31828459126784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record002_result⟩)
 (.leaf ⟨(25, 31842955689984), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(25, 31891788931072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record004_result⟩)
 (.leaf ⟨(25, 31896072372480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record005_result⟩))
 (.branch 7
 (.leaf ⟨(25, 31896081801216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record006_result⟩)
 (.leaf ⟨(25, 31930466762752), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(25, 31938788261888), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record008_result⟩)
 (.leaf ⟨(25, 31940330143744), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record009_result⟩))
 (.branch 11
 (.leaf ⟨(25, 31963709186048), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record010_result⟩)
 (.leaf ⟨(25, 31972294926336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(25, 31973615600160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record012_result⟩)
 (.leaf ⟨(25, 31995635761152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record013_result⟩))
 (.branch 15
 (.leaf ⟨(25, 32010462625792), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record014_result⟩)
 (.leaf ⟨(25, 32028125307136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(25, 32041010208832), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record016_result⟩)
 (.leaf ⟨(25, 32041127383072), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record017_result⟩))
 (.branch 19
 (.leaf ⟨(25, 32043208032256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record018_result⟩)
 (.leaf ⟨(25, 32076495585280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(25, 32078179598336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record020_result⟩)
 (.leaf ⟨(25, 32078708080640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record021_result⟩))
 (.branch 23
 (.leaf ⟨(25, 32165295825152), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record022_result⟩)
 (.leaf ⟨(25, 32169859227712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(25, 32172057051136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record024_result⟩)
 (.leaf ⟨(25, 32198434553856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record025_result⟩))
 (.branch 27
 (.leaf ⟨(25, 32199103479808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record026_result⟩)
 (.leaf ⟨(25, 32205344604160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(25, 32270513602560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record028_result⟩)
 (.leaf ⟨(25, 32271042084864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record029_result⟩))
 (.branch 31
 (.leaf ⟨(25, 32301981368320), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record030_result⟩)
 (.leaf ⟨(25, 32334680227840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(25, 32335217033216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record032_result⟩)
 (.leaf ⟨(25, 32351841304576), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record033_result⟩))
 (.branch 35
 (.leaf ⟨(25, 32476135161856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record034_result⟩)
 (.leaf ⟨(25, 32488344846336), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(25, 32488617410560), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record036_result⟩)
 (.leaf ⟨(25, 32492233424896), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record037_result⟩))
 (.branch 39
 (.leaf ⟨(25, 32514051735552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record038_result⟩)
 (.leaf ⟨(25, 32514588540928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(25, 32522637475840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record040_result⟩)
 (.leaf ⟨(25, 32522910040064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record041_result⟩))
 (.branch 43
 (.leaf ⟨(25, 32523372462080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record042_result⟩)
 (.leaf ⟨(25, 32524445679616), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(25, 32530116968448), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record044_result⟩)
 (.leaf ⟨(25, 32642900754432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record045_result⟩))
 (.branch 47
 (.leaf ⟨(25, 32645517934592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record046_result⟩)
 (.leaf ⟨(25, 32660080558080), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(25, 32660609040384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record048_result⟩)
 (.leaf ⟨(25, 32693316222976), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record049_result⟩))
 (.branch 51
 (.leaf ⟨(25, 32693844705280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record050_result⟩)
 (.leaf ⟨(25, 32711613907200), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(25, 32716951191552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record052_result⟩)
 (.leaf ⟨(25, 32717719207936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record053_result⟩))
 (.branch 55
 (.leaf ⟨(25, 32723390496768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record054_result⟩)
 (.leaf ⟨(25, 32729128239104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(25, 32730201456640), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record056_result⟩)
 (.leaf ⟨(25, 32780335513600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record057_result⟩))
 (.branch 59
 (.leaf ⟨(25, 32782688452608), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record058_result⟩)
 (.leaf ⟨(25, 32783216934912), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(25, 32788929576960), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record060_result⟩)
 (.leaf ⟨(25, 32789458059264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record061_result⟩))
 (.branch 63
 (.leaf ⟨(25, 32804960207364), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record062_result⟩)
 (.branch 64
 (.leaf ⟨(25, 32804960346112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record063_result⟩)
 (.leaf ⟨(25, 32804994809856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00022.record064_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (13822 + i))) 0 65 :=
  interval_of_check _ 0 65 (by decide +kernel)

public theorem complete : Block 13822 13887 :=
  block_of_table results 13822 65 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0312

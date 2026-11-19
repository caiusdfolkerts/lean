module
prelude
import GraphInputsRow30Part00053Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0781
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(30, 31596732219392), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record000_result⟩)
 (.leaf ⟨(30, 31602444861440), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record001_result⟩))
 (.branch 3
 (.leaf ⟨(30, 31611253166112), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record002_result⟩)
 (.leaf ⟨(30, 31750614974720), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(30, 31785043951616), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record004_result⟩)
 (.leaf ⟨(30, 31789477265408), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record005_result⟩))
 (.branch 7
 (.leaf ⟨(30, 31790005747712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record006_result⟩)
 (.branch 8
 (.leaf ⟨(30, 31795718389760), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record007_result⟩)
 (.leaf ⟨(30, 31812889870336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(30, 31819336581120), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record009_result⟩)
 (.leaf ⟨(30, 31827930644480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record010_result⟩))
 (.branch 12
 (.leaf ⟨(30, 31828459126784), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record011_result⟩)
 (.branch 13
 (.leaf ⟨(30, 31842955689984), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record012_result⟩)
 (.leaf ⟨(30, 31891788931072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(30, 31896072372480), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record014_result⟩)
 (.leaf ⟨(30, 31896081801216), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record015_result⟩))
 (.branch 17
 (.leaf ⟨(30, 31930466762752), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record016_result⟩)
 (.branch 18
 (.leaf ⟨(30, 31938788261888), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record017_result⟩)
 (.leaf ⟨(30, 31940330143744), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(30, 31963709186048), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record019_result⟩)
 (.leaf ⟨(30, 31972294926336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record020_result⟩))
 (.branch 22
 (.leaf ⟨(30, 31973615600160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record021_result⟩)
 (.branch 23
 (.leaf ⟨(30, 31995635761152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record022_result⟩)
 (.leaf ⟨(30, 32010462625792), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(30, 32028125307136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record024_result⟩)
 (.leaf ⟨(30, 32041010208832), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record025_result⟩))
 (.branch 27
 (.leaf ⟨(30, 32041127383072), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record026_result⟩)
 (.branch 28
 (.leaf ⟨(30, 32043208032256), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record027_result⟩)
 (.leaf ⟨(30, 32076495585280), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(30, 32078179598336), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record029_result⟩)
 (.leaf ⟨(30, 32078708080640), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record030_result⟩))
 (.branch 32
 (.leaf ⟨(30, 32165295825152), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record031_result⟩)
 (.branch 33
 (.leaf ⟨(30, 32169859227712), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record032_result⟩)
 (.leaf ⟨(30, 32172057051136), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(30, 32198434553856), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record034_result⟩)
 (.leaf ⟨(30, 32199103479808), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record035_result⟩))
 (.branch 37
 (.leaf ⟨(30, 32205344604160), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record036_result⟩)
 (.branch 38
 (.leaf ⟨(30, 32301981368320), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record037_result⟩)
 (.leaf ⟨(30, 32334680227840), Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00053.record038_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (25241 + i))) 0 39 :=
  interval_of_check _ 0 39 (by decide +kernel)

public theorem complete : Block 25241 25280 :=
  block_of_table results 25241 39 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0781

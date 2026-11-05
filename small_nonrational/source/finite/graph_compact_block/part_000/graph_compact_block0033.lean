module
prelude
import GraphInputsRow16Part00033Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0033
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 30
 (.branch 15
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 31397453529344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 31397465038848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record001_result⟩)
 (.leaf ⟨(16, 31408329392384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(16, 31408333553920), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record003_result⟩)
 (.leaf ⟨(16, 31408333619200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record004_result⟩))
 (.branch 6
 (.leaf ⟨(16, 31414775980288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record005_result⟩)
 (.leaf ⟨(16, 31415040221440), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record006_result⟩))))
 (.branch 11
 (.branch 9
 (.branch 8
 (.leaf ⟨(16, 31415040286720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record007_result⟩)
 (.leaf ⟨(16, 31416716951808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record008_result⟩))
 (.branch 10
 (.leaf ⟨(16, 31416725340160), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record009_result⟩)
 (.leaf ⟨(16, 31416915132672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record010_result⟩)))
 (.branch 13
 (.branch 12
 (.leaf ⟨(16, 31416923521024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record011_result⟩)
 (.leaf ⟨(16, 31417183535360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record012_result⟩))
 (.branch 14
 (.leaf ⟨(16, 31417195044864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record013_result⟩)
 (.leaf ⟨(16, 31417253822464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record014_result⟩)))))
 (.branch 22
 (.branch 18
 (.branch 16
 (.leaf ⟨(16, 31417262145536), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 31417417867520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record016_result⟩)
 (.leaf ⟨(16, 31417452003328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record017_result⟩)))
 (.branch 20
 (.branch 19
 (.leaf ⟨(16, 31417460326400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record018_result⟩)
 (.leaf ⟨(16, 31425509261312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record019_result⟩))
 (.branch 21
 (.leaf ⟨(16, 31431746158848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record020_result⟩)
 (.leaf ⟨(16, 31431750385664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record021_result⟩))))
 (.branch 26
 (.branch 24
 (.branch 23
 (.leaf ⟨(16, 31431757668352), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record022_result⟩)
 (.leaf ⟨(16, 31431947460864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record023_result⟩))
 (.branch 25
 (.leaf ⟨(16, 31431955849216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record024_result⟩)
 (.leaf ⟨(16, 31431980491008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record025_result⟩)))
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 31432484331520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record026_result⟩)
 (.leaf ⟨(16, 31432517361664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 31432518402048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record028_result⟩)
 (.leaf ⟨(16, 31433029066752), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record029_result⟩))))))
 (.branch 45
 (.branch 37
 (.branch 33
 (.branch 31
 (.leaf ⟨(16, 31448308981760), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record030_result⟩)
 (.branch 32
 (.leaf ⟨(16, 31449449299968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record031_result⟩)
 (.leaf ⟨(16, 31449457623040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record032_result⟩)))
 (.branch 35
 (.branch 34
 (.leaf ⟨(16, 31451248787456), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record033_result⟩)
 (.leaf ⟨(16, 31464986050560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record034_result⟩))
 (.branch 36
 (.leaf ⟨(16, 31466075652096), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record035_result⟩)
 (.leaf ⟨(16, 31466281115648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record036_result⟩))))
 (.branch 41
 (.branch 39
 (.branch 38
 (.leaf ⟨(16, 31466282025984), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record037_result⟩)
 (.leaf ⟨(16, 31466876568064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record038_result⟩))
 (.branch 40
 (.leaf ⟨(16, 31476914651392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record039_result⟩)
 (.leaf ⟨(16, 31476918812928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record040_result⟩)))
 (.branch 43
 (.branch 42
 (.leaf ⟨(16, 31476918878208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record041_result⟩)
 (.leaf ⟨(16, 31479200555008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record042_result⟩))
 (.branch 44
 (.leaf ⟨(16, 31479233585152), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record043_result⟩)
 (.leaf ⟨(16, 31479464730880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record044_result⟩)))))
 (.branch 52
 (.branch 48
 (.branch 46
 (.leaf ⟨(16, 31481141461248), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record045_result⟩)
 (.branch 47
 (.leaf ⟨(16, 31481149849600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record046_result⟩)
 (.leaf ⟨(16, 31481348030464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(16, 31481381060608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record048_result⟩)
 (.leaf ⟨(16, 31481608044800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record049_result⟩))
 (.branch 51
 (.leaf ⟨(16, 31481619554304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record050_result⟩)
 (.leaf ⟨(16, 31481876512768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record051_result⟩))))
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf ⟨(16, 31481884835840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record052_result⟩)
 (.leaf ⟨(16, 31487589154816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record053_result⟩))
 (.branch 55
 (.leaf ⟨(16, 31488058859520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record054_result⟩)
 (.leaf ⟨(16, 31489132077056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record055_result⟩)))
 (.branch 58
 (.branch 57
 (.leaf ⟨(16, 31494024233216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record056_result⟩)
 (.leaf ⟨(16, 31494028460032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record057_result⟩))
 (.branch 59
 (.leaf ⟨(16, 31494090293504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record058_result⟩)
 (.leaf ⟨(16, 31494094520320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00033.record059_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1840 + i))) 0 60 :=
  interval_of_check _ 0 60 (by decide +kernel)

public theorem complete : Block 1840 1900 :=
  block_of_table results 1840 60 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0033

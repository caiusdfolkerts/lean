module
prelude
import GraphInputsRow24Part00012Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0128
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(24, 7576878620672), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record000_result⟩)
 (.leaf ⟨(24, 7577744195584), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record001_result⟩))
 (.branch 3
 (.leaf ⟨(24, 7585718083648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record002_result⟩)
 (.leaf ⟨(24, 7586055225600), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(24, 7586191572992), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record004_result⟩)
 (.leaf ⟨(24, 7586199896064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record005_result⟩))
 (.branch 7
 (.leaf ⟨(24, 7586323693568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record006_result⟩)
 (.branch 8
 (.leaf ⟨(24, 7586332016640), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record007_result⟩)
 (.leaf ⟨(24, 7586792357888), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(24, 7586860498944), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record009_result⟩)
 (.leaf ⟨(24, 7593661858048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record010_result⟩))
 (.branch 12
 (.leaf ⟨(24, 7593661923328), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record011_result⟩)
 (.branch 13
 (.leaf ⟨(24, 7593665759488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record012_result⟩)
 (.leaf ⟨(24, 7594064527360), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(24, 7594066315392), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record014_result⟩)
 (.leaf ⟨(24, 7598074104064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record015_result⟩))
 (.branch 17
 (.leaf ⟨(24, 7598074169344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record016_result⟩)
 (.branch 18
 (.leaf ⟨(24, 7598090813952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record017_result⟩)
 (.leaf ⟨(24, 7598095007744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(24, 7598346601480), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record019_result⟩)
 (.leaf ⟨(24, 7598363377665), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record020_result⟩))
 (.branch 22
 (.leaf ⟨(24, 7598602748160), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record021_result⟩)
 (.branch 23
 (.leaf ⟨(24, 7598615037952), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record022_result⟩)
 (.leaf ⟨(24, 7602658361344), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(24, 7602775787520), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record024_result⟩)
 (.leaf ⟨(24, 7602897699072), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record025_result⟩))
 (.branch 27
 (.leaf ⟨(24, 7607070752768), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record026_result⟩)
 (.branch 28
 (.leaf ⟨(24, 7610820593920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record027_result⟩)
 (.leaf ⟨(24, 7610824788096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(24, 7620077290048), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record029_result⟩)
 (.leaf ⟨(24, 7623567082752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record030_result⟩))
 (.branch 32
 (.leaf ⟨(24, 7623567114496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record031_result⟩)
 (.branch 33
 (.leaf ⟨(24, 7623575471104), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record032_result⟩)
 (.leaf ⟨(24, 7623705427968), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(24, 7623835582464), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record034_result⟩)
 (.leaf ⟨(24, 7623843905536), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record035_result⟩))
 (.branch 37
 (.leaf ⟨(24, 7623977992192), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record036_result⟩)
 (.branch 38
 (.leaf ⟨(24, 7624103821828), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record037_result⟩)
 (.leaf ⟨(24, 7624372257280), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record038_result⟩)))))))
 (.branch 59
 (.branch 49
 (.branch 44
 (.branch 41
 (.branch 40
 (.leaf ⟨(24, 7635113934848), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record039_result⟩)
 (.leaf ⟨(24, 7635122257920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record040_result⟩))
 (.branch 42
 (.leaf ⟨(24, 7639283007488), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record041_result⟩)
 (.branch 43
 (.leaf ⟨(24, 7641553240064), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record042_result⟩)
 (.leaf ⟨(24, 7647604506624), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record043_result⟩))))
 (.branch 46
 (.branch 45
 (.leaf ⟨(24, 7653700960512), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record044_result⟩)
 (.leaf ⟨(24, 7657998057472), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record045_result⟩))
 (.branch 47
 (.leaf ⟨(24, 7658270621696), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record046_result⟩)
 (.branch 48
 (.leaf ⟨(24, 7658733043712), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record047_result⟩)
 (.leaf ⟨(24, 7700383613056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record048_result⟩)))))
 (.branch 54
 (.branch 51
 (.branch 50
 (.leaf ⟨(24, 7736993546496), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record049_result⟩)
 (.leaf ⟨(24, 7736993611776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record050_result⟩))
 (.branch 52
 (.leaf ⟨(24, 7741286481920), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record051_result⟩)
 (.branch 53
 (.leaf ⟨(24, 7741288497408), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record052_result⟩)
 (.leaf ⟨(24, 7749607981056), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record053_result⟩))))
 (.branch 56
 (.branch 55
 (.leaf ⟨(24, 7753233862720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record054_result⟩)
 (.leaf ⟨(24, 7775579111424), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record055_result⟩))
 (.branch 57
 (.leaf ⟨(24, 7776721965312), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record056_result⟩)
 (.branch 58
 (.leaf ⟨(24, 7783900610560), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record057_result⟩)
 (.leaf ⟨(24, 7841146474752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record058_result⟩))))))
 (.branch 69
 (.branch 64
 (.branch 61
 (.branch 60
 (.leaf ⟨(24, 7852485869568), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record059_result⟩)
 (.leaf ⟨(24, 7852957638720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record060_result⟩))
 (.branch 62
 (.leaf ⟨(24, 7854031376448), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record061_result⟩)
 (.branch 63
 (.leaf ⟨(24, 7890538594305), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record062_result⟩)
 (.leaf ⟨(24, 7930197835776), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record063_result⟩))))
 (.branch 66
 (.branch 65
 (.leaf ⟨(24, 7994185121792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record064_result⟩)
 (.leaf ⟨(24, 8041408823552), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record065_result⟩))
 (.branch 67
 (.leaf ⟨(24, 8041412985088), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record066_result⟩)
 (.branch 68
 (.leaf ⟨(24, 8041413050368), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record067_result⟩)
 (.leaf ⟨(24, 8041466431744), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record068_result⟩)))))
 (.branch 74
 (.branch 71
 (.branch 70
 (.leaf ⟨(24, 8041809412096), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record069_result⟩)
 (.leaf ⟨(24, 8041866987648), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record070_result⟩))
 (.branch 72
 (.leaf ⟨(24, 8044785174784), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record071_result⟩)
 (.branch 73
 (.leaf ⟨(24, 8045032185856), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record072_result⟩)
 (.leaf ⟨(24, 8050648826112), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record073_result⟩))))
 (.branch 76
 (.branch 75
 (.leaf ⟨(24, 8067091562752), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record074_result⟩)
 (.leaf ⟨(24, 8067227910144), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record075_result⟩))
 (.branch 77
 (.leaf ⟨(24, 8067236233216), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record076_result⟩)
 (.branch 78
 (.leaf ⟨(24, 8067360030720), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record077_result⟩)
 (.leaf ⟨(24, 8067368353792), Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00012.record078_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (8383 + i))) 0 79 :=
  interval_of_check _ 0 79 (by decide +kernel)

public theorem complete : Block 8383 8462 :=
  block_of_table results 8383 79 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0128

module
prelude
import GraphInputsRow28Part00010Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0430
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 42
 (.branch 21
 (.branch 10
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨(28, 29280977354752), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record000_result⟩)
 (.leaf ⟨(28, 29281745371136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record001_result⟩))
 (.branch 3
 (.leaf ⟨(28, 29284370481152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record002_result⟩)
 (.branch 4
 (.leaf ⟨(28, 29285906120704), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record003_result⟩)
 (.leaf ⟨(28, 29292819939328), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record004_result⟩))))
 (.branch 7
 (.branch 6
 (.leaf ⟨(28, 29292956221440), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record005_result⟩)
 (.leaf ⟨(28, 29293860126720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record006_result⟩))
 (.branch 8
 (.leaf ⟨(28, 29413079023744), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record007_result⟩)
 (.branch 9
 (.leaf ⟨(28, 29418416275456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record008_result⟩)
 (.leaf ⟨(28, 29422709145600), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record009_result⟩)))))
 (.branch 15
 (.branch 12
 (.branch 11
 (.leaf ⟨(28, 29423076638720), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record010_result⟩)
 (.leaf ⟨(28, 29523626164224), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record011_result⟩))
 (.branch 13
 (.leaf ⟨(28, 29523890405376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record012_result⟩)
 (.branch 14
 (.leaf ⟨(28, 29549392838784), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record013_result⟩)
 (.leaf ⟨(28, 29550517977088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record014_result⟩))))
 (.branch 18
 (.branch 16
 (.leaf ⟨(28, 29552734633984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record015_result⟩)
 (.branch 17
 (.leaf ⟨(28, 29552998875136), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record016_result⟩)
 (.leaf ⟨(28, 29583753641984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record017_result⟩)))
 (.branch 19
 (.leaf ⟨(28, 29588050673664), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record018_result⟩)
 (.branch 20
 (.leaf ⟨(28, 29588314914816), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record019_result⟩)
 (.leaf ⟨(28, 29596619767808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record020_result⟩))))))
 (.branch 31
 (.branch 26
 (.branch 23
 (.branch 22
 (.leaf ⟨(28, 29727217680384), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record021_result⟩)
 (.leaf ⟨(28, 29761510309888), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record022_result⟩))
 (.branch 24
 (.leaf ⟨(28, 29762013691904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record023_result⟩)
 (.branch 25
 (.leaf ⟨(28, 29773992558592), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record024_result⟩)
 (.leaf ⟨(28, 29811368165376), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record025_result⟩))))
 (.branch 28
 (.branch 27
 (.leaf ⟨(28, 29871640150016), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record026_result⟩)
 (.leaf ⟨(28, 30237679190272), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record027_result⟩))
 (.branch 29
 (.leaf ⟨(28, 30241976287232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record028_result⟩)
 (.branch 30
 (.leaf ⟨(28, 30242248851456), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record029_result⟩)
 (.leaf ⟨(28, 30242513092608), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record030_result⟩)))))
 (.branch 36
 (.branch 33
 (.branch 32
 (.leaf ⟨(28, 30242744303616), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record031_result⟩)
 (.leaf ⟨(28, 30249488809984), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record032_result⟩))
 (.branch 34
 (.leaf ⟨(28, 30254859059200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record033_result⟩)
 (.branch 35
 (.leaf ⟨(28, 30255226552320), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record034_result⟩)
 (.leaf ⟨(28, 30258078711808), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record035_result⟩))))
 (.branch 39
 (.branch 37
 (.leaf ⟨(28, 30313896542208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record036_result⟩)
 (.branch 38
 (.leaf ⟨(28, 30314433347584), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record037_result⟩)
 (.leaf ⟨(28, 30314953113600), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(28, 30322486444032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record039_result⟩)
 (.branch 41
 (.leaf ⟨(28, 30323543015424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record040_result⟩)
 (.leaf ⟨(28, 30331059179520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record041_result⟩)))))))
 (.branch 63
 (.branch 52
 (.branch 47
 (.branch 44
 (.branch 43
 (.leaf ⟨(28, 30383815000064), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record042_result⟩)
 (.leaf ⟨(28, 30386935562240), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record043_result⟩))
 (.branch 45
 (.leaf ⟨(28, 30456149966848), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record044_result⟩)
 (.branch 46
 (.leaf ⟨(28, 30511464988800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record045_result⟩)
 (.leaf ⟨(28, 30516028375040), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record046_result⟩))))
 (.branch 49
 (.branch 48
 (.leaf ⟨(28, 30524332707840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record047_result⟩)
 (.leaf ⟨(28, 30717606234112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record048_result⟩))
 (.branch 50
 (.leaf ⟨(28, 30717623140352), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record049_result⟩)
 (.branch 51
 (.leaf ⟨(28, 30789649596672), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record050_result⟩)
 (.leaf ⟨(28, 30789653823488), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record051_result⟩)))))
 (.branch 57
 (.branch 54
 (.branch 53
 (.leaf ⟨(28, 30789715656960), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record052_result⟩)
 (.leaf ⟨(28, 30789719883776), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record053_result⟩))
 (.branch 55
 (.leaf ⟨(28, 30789727166464), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record054_result⟩)
 (.branch 56
 (.leaf ⟨(28, 30789949989120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record055_result⟩)
 (.leaf ⟨(28, 30791997333760), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record056_result⟩))))
 (.branch 60
 (.branch 58
 (.leaf ⟨(28, 30792005722112), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record057_result⟩)
 (.branch 59
 (.leaf ⟨(28, 30792030363904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record058_result⟩)
 (.leaf ⟨(28, 30792500125728), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record059_result⟩)))
 (.branch 61
 (.leaf ⟨(28, 30824045150208), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record060_result⟩)
 (.branch 62
 (.leaf ⟨(28, 30824590213120), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record061_result⟩)
 (.leaf ⟨(28, 30825266028800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record062_result⟩))))))
 (.branch 74
 (.branch 68
 (.branch 65
 (.branch 64
 (.leaf ⟨(28, 30825274417152), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record063_result⟩)
 (.leaf ⟨(28, 30825785856032), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record064_result⟩))
 (.branch 66
 (.leaf ⟨(28, 30826389570304), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record065_result⟩)
 (.branch 67
 (.leaf ⟨(28, 30826398023680), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record066_result⟩)
 (.leaf ⟨(28, 30826662264832), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(28, 30826670587904), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record068_result⟩)
 (.branch 70
 (.leaf ⟨(28, 30826859332128), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record069_result⟩)
 (.leaf ⟨(28, 30826860445696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record070_result⟩)))
 (.branch 72
 (.leaf ⟨(28, 30839008166144), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record071_result⟩)
 (.branch 73
 (.leaf ⟨(28, 30839342694400), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record072_result⟩)
 (.leaf ⟨(28, 30839545036800), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record073_result⟩)))))
 (.branch 79
 (.branch 76
 (.branch 75
 (.leaf ⟨(28, 30839549198336), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record074_result⟩)
 (.leaf ⟨(28, 30839611097088), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record075_result⟩))
 (.branch 77
 (.leaf ⟨(28, 30842965991424), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record076_result⟩)
 (.branch 78
 (.leaf ⟨(28, 30857478283520), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record077_result⟩)
 (.leaf ⟨(28, 30864189169696), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record078_result⟩))))
 (.branch 82
 (.branch 80
 (.leaf ⟨(28, 30864239235104), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record079_result⟩)
 (.branch 81
 (.leaf ⟨(28, 30865312711200), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record080_result⟩)
 (.leaf ⟨(28, 30865313824768), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(28, 30865322147840), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record082_result⟩)
 (.branch 84
 (.leaf ⟨(28, 30866354012160), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record083_result⟩)
 (.leaf ⟨(28, 30866362335232), Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00010.record084_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (20215 + i))) 0 85 :=
  interval_of_check _ 0 85 (by decide +kernel)

public theorem complete : Block 20215 20300 :=
  block_of_table results 20215 85 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0430

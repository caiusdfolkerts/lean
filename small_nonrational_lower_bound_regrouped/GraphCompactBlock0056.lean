module
prelude
import GraphInputsRow19Part00016Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0056
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 19128213577792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 19128576909376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record001_result⟩)
 (.leaf ⟨(19, 19128577966080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 19134183129344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 19134190460992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record004_result⟩)
 (.leaf ⟨(19, 19134250295296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 19134256521280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 19134283845632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record007_result⟩)
 (.leaf ⟨(19, 19168508461056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 19168581804032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 19175438336256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record010_result⟩)
 (.leaf ⟨(19, 19181534789640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 19181880762624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 19284961608000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record013_result⟩)
 (.leaf ⟨(19, 19319321338176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 19401614098688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 19401618260224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record016_result⟩)
 (.leaf ⟨(19, 19401618325504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 19402159292416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 19402289332224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record019_result⟩)
 (.leaf ⟨(19, 19405913276416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 19448980390144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record021_result⟩)
 (.leaf ⟨(19, 19456781795336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 19470902951936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record023_result⟩)
 (.leaf ⟨(19, 19470911275008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 19471041298944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 19473441570816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record026_result⟩)
 (.leaf ⟨(19, 19473491116032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 19474531172352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 19474533057792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record029_result⟩)
 (.leaf ⟨(19, 19475069927425), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 19504138616832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 19504146939904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record032_result⟩)
 (.leaf ⟨(19, 19506269323264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 19512045011968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 19531008311296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record035_result⟩)
 (.leaf ⟨(19, 19543348035584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 19586415149312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 19586419310848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record038_result⟩)
 (.leaf ⟨(19, 19586419359808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 19589632721152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 19589635842304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record041_result⟩)
 (.leaf ⟨(19, 19589904244992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 19593952313352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 19594199244864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record044_result⟩)
 (.leaf ⟨(19, 19594220716040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 19607941349376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record046_result⟩)
 (.leaf ⟨(19, 19610876329984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 19610925875200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record048_result⟩)
 (.leaf ⟨(19, 19610973274368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 19610973339648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 19610976460800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record051_result⟩)
 (.leaf ⟨(19, 19610992975872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 19611644346368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 19611963785472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record054_result⟩)
 (.leaf ⟨(19, 19611963850752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 19611965866240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 19611965931520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record057_result⟩)
 (.leaf ⟨(19, 19611967816960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 19612033032192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 19612171395072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record060_result⟩)
 (.leaf ⟨(19, 19612172289088), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 19612504686593), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 19612768928256), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record063_result⟩)
 (.leaf ⟨(19, 19619700359424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 19628277565504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 19628277579784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record066_result⟩)
 (.leaf ⟨(19, 19649479771136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 19649680965632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 19649752203780), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record069_result⟩)
 (.leaf ⟨(19, 19655138820160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 19656205746432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record071_result⟩)
 (.leaf ⟨(19, 19658352181504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 19662471512072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record073_result⟩)
 (.leaf ⟨(19, 19662537572360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 19676067799104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 19676068855808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record076_result⟩)
 (.leaf ⟨(19, 19679593709568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 19679626739712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 19683869868288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record079_result⟩)
 (.leaf ⟨(19, 19683869933568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 19683870973952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 19683878110272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record082_result⟩)
 (.leaf ⟨(19, 19683904524288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 19683904849152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 19683910766592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record085_result⟩)
 (.leaf ⟨(19, 19683946266625), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 19683970909440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 19683977867264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record088_result⟩)
 (.leaf ⟨(19, 19684012326913), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 19718197150720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 19724775917824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record091_result⟩)
 (.leaf ⟨(19, 19724914343944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 19731155468296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 19731222568968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record094_result⟩)
 (.leaf ⟨(19, 19739741208584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 19763967361024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record096_result⟩)
 (.leaf ⟨(19, 19840235503872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 19872447758592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record098_result⟩)
 (.leaf ⟨(19, 19881039806464), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00016.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (3665 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 3665 3765 :=
  block_of_table results 3665 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0056

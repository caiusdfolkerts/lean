module
prelude
import GraphInputsSix0Part00041Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1006
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 16632424435968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 16632556556544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record001_result⟩)
 (.leaf ⟨(32, 16632820797696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 16632827088960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 16636959064320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record004_result⟩)
 (.leaf ⟨(32, 16637227467008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 16637239496704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 16639260102912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record007_result⟩)
 (.leaf ⟨(32, 16639265873984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 16639265890304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 16639266394176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record010_result⟩)
 (.leaf ⟨(32, 16639317772304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 16639988924416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 16640322445376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record013_result⟩)
 (.leaf ⟨(32, 16640322461696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 16640348537088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 16640391512065), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record016_result⟩)
 (.leaf ⟨(32, 16640458629120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 16641532366848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 16643669893376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record019_result⟩)
 (.leaf ⟨(32, 16647507150864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 16647639271440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record021_result⟩)
 (.leaf ⟨(32, 16648570437888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 16648574664704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record023_result⟩)
 (.leaf ⟨(32, 16648580890625), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 16648713011201), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 16648780128256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record026_result⟩)
 (.leaf ⟨(32, 16649853865984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 16657528406016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 16678029099776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record029_result⟩)
 (.leaf ⟨(32, 16704272924928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 16705007976448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 16709168726016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record032_result⟩)
 (.leaf ⟨(32, 16712867053568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 16713403858944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 16717155696896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record035_result⟩)
 (.leaf ⟨(32, 16717490225152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 16721112990240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 16721452793856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record038_result⟩)
 (.leaf ⟨(32, 16721725358080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 16722187780096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 16729469091840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record041_result⟩)
 (.leaf ⟨(32, 16735478546688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 16739911925760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 16740448731136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record044_result⟩)
 (.leaf ⟨(32, 16744609480704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 16748770230272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record046_result⟩)
 (.leaf ⟨(32, 16752658415616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 16757091729408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record048_result⟩)
 (.leaf ⟨(32, 16757620211712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 16767638667280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 16767640748048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record051_result⟩)
 (.leaf ⟨(32, 16767644909584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 16767846211600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 16769838417936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record054_result⟩)
 (.leaf ⟨(32, 16769991315712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 16776211662864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 16776430620928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record057_result⟩)
 (.leaf ⟨(32, 16776436912192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 16777519055104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 16780840411392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record060_result⟩)
 (.leaf ⟨(32, 16785857331328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 16815199617792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 16846339244032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record063_result⟩)
 (.leaf ⟨(32, 16881779998720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 16906151035136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 16906155261952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record066_result⟩)
 (.leaf ⟨(32, 16906161504256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 16906266640640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 16906278930432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record069_result⟩)
 (.leaf ⟨(32, 16906351296768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 16906353442816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record071_result⟩)
 (.leaf ⟨(32, 16906359685120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 16906400841984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record073_result⟩)
 (.leaf ⟨(32, 16906411051008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 16906870595648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 16908615156480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record076_result⟩)
 (.leaf ⟨(32, 16909017809472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 16910565572608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 16913682153728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record079_result⟩)
 (.leaf ⟨(32, 16913692362752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 16914135392320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 16914136449024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record082_result⟩)
 (.leaf ⟨(32, 16914151907392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 16915258933824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 16930778390592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record085_result⟩)
 (.leaf ⟨(32, 16930812477440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 16930814558208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 16931834961984), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record088_result⟩)
 (.leaf ⟨(32, 16931902078976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 16931904159744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 16932036149760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record091_result⟩)
 (.leaf ⟨(32, 16939502305536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 16939506532352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 16939514595328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record094_result⟩)
 (.leaf ⟨(32, 16939636506880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 16939644895232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record096_result⟩)
 (.leaf ⟨(32, 16939646715904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 16939753933056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record098_result⟩)
 (.leaf ⟨(32, 16940156586048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00041.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (30886 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 30886 30986 :=
  block_of_table results 30886 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1006

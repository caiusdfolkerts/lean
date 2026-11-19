module
prelude
import GraphInputsSix0Part00067Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1032
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 25125961662464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 25128117207040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record001_result⟩)
 (.leaf ⟨(32, 25152488243456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 25152492470272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 25152498712576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record004_result⟩)
 (.leaf ⟨(32, 25152603848960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 25152616138752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 25152688505088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record007_result⟩)
 (.leaf ⟨(32, 25152690651136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 25152696893440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 25152738050304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record010_result⟩)
 (.leaf ⟨(32, 25152748259328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 25153207803968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 25153631748096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record013_result⟩)
 (.leaf ⟨(32, 25153644036352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 25153656326144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 25153763868672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record016_result⟩)
 (.leaf ⟨(32, 25153770110976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 25153778237696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 25153788446720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record019_result⟩)
 (.leaf ⟨(32, 25154952364800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 25155355017792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record021_result⟩)
 (.leaf ⟨(32, 25156902780928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 25158072926976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record023_result⟩)
 (.leaf ⟨(32, 25160019362048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 25160029571072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 25160128661504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record026_result⟩)
 (.leaf ⟨(32, 25160472600640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 25160473657344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 25160489115712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record029_result⟩)
 (.leaf ⟨(32, 25161596142144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 25169917641280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 25177115598912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record032_result⟩)
 (.leaf ⟨(32, 25177149685760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 25177151766528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 25177184796672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record035_result⟩)
 (.leaf ⟨(32, 25178172170304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 25178239287296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 25178241368064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record038_result⟩)
 (.leaf ⟨(32, 25178373358080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 25185839513856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 25185843740672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record041_result⟩)
 (.leaf ⟨(32, 25185851803648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 25185973715200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 25185982103552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record044_result⟩)
 (.leaf ⟨(32, 25185983924224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 25186091141376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record046_result⟩)
 (.leaf ⟨(32, 25186493794368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 25190138445824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record048_result⟩)
 (.leaf ⟨(32, 25190251759872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 25190260148224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 25190268404480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record051_result⟩)
 (.leaf ⟨(32, 25190788497928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 25194420897792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 25194815162432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record054_result⟩)
 (.leaf ⟨(32, 25194831807040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 25194949247496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 25215752995332), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record057_result⟩)
 (.leaf ⟨(32, 25215753126912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 25222350700544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 25224360788224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record060_result⟩)
 (.leaf ⟨(32, 25226490577152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 25261126975488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 25261655457792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record063_result⟩)
 (.leaf ⟨(32, 25292162793728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 25292166955264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 25292167020544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record066_result⟩)
 (.leaf ⟨(32, 25292169036032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 25292301156608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 25292301221888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record069_result⟩)
 (.leaf ⟨(32, 25292401807616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 25292565397760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record071_result⟩)
 (.leaf ⟨(32, 25292565463040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 25292571689024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record073_result⟩)
 (.leaf ⟨(32, 25292672340032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 25294309228800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 25294313390336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record076_result⟩)
 (.leaf ⟨(32, 25294313455616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 25294350061824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 25294441349376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record079_result⟩)
 (.leaf ⟨(32, 25294447591680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 25294447656960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 25294482182400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record082_result⟩)
 (.leaf ⟨(32, 25294709752064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 25294709817344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 25294711832832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record085_result⟩)
 (.leaf ⟨(32, 25294711898112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 25294716059648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 25294719164480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record088_result⟩)
 (.leaf ⟨(32, 25294746423552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 25294752714816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 25295893565456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record091_result⟩)
 (.leaf ⟨(32, 25298642931968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 25299004702976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 25299004768256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record094_result⟩)
 (.leaf ⟨(32, 25299010994240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 25299012034624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record096_result⟩)
 (.leaf ⟨(32, 25299045584960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 25300186435600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record098_result⟩)
 (.leaf ⟨(32, 25307228672256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00067.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (33339 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 33339 33439 :=
  block_of_table results 33339 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1032

module
prelude
import GraphInputsSix0Part00030Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0995
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 11446244114688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 11446244179968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record001_result⟩)
 (.leaf ⟨(32, 11446248308864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 11446301755520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 11446376235264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record004_result⟩)
 (.leaf ⟨(32, 11446376300544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 11446378381312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 11446379421696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record007_result⟩)
 (.leaf ⟨(32, 11446382510208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 11446429681920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 11446433876096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record010_result⟩)
 (.leaf ⟨(32, 11446499936384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 11446644670592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 11446646751360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record013_result⟩)
 (.leaf ⟨(32, 11446646784000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 11448650563585), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 11450590431488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record016_result⟩)
 (.leaf ⟨(32, 11450594625664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 11450671251456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 11450939621504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record019_result⟩)
 (.leaf ⟨(32, 11450939654144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 11452939304960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record021_result⟩)
 (.leaf ⟨(32, 11452943433729), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 11455089868801), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record023_result⟩)
 (.leaf ⟨(32, 11459180365952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 11469846642688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 11471924904064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record026_result⟩)
 (.leaf ⟨(32, 11471927017472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 11471931048960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 11472058974848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record029_result⟩)
 (.leaf ⟨(32, 11472129229824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 11478396584064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 11478594764928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record032_result⟩)
 (.leaf ⟨(32, 11478859006080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 11548273770624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 11548401697024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record035_result⟩)
 (.leaf ⟨(32, 11548405891200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 11548508651536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 11548670132352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record038_result⟩)
 (.leaf ⟨(32, 11554749775888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 11554841002240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 11554843083008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record041_result⟩)
 (.leaf ⟨(32, 11554847277184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 11554881896464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 11555109437568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record044_result⟩)
 (.leaf ⟨(32, 11555111485696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 11555111518336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record046_result⟩)
 (.leaf ⟨(32, 11563467636752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 11563701420160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record048_result⟩)
 (.leaf ⟨(32, 11583816827136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 11583821021312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 11583824691216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record051_result⟩)
 (.leaf ⟨(32, 11584873398528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 11588111778048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 11588115939584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record054_result⟩)
 (.leaf ⟨(32, 11588115972224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 11588117561360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 11588381802512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record057_result⟩)
 (.leaf ⟨(32, 11588384374912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 11589440946304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 11684618535040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record060_result⟩)
 (.leaf ⟨(32, 11684622204944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 11684752703744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 11684752736384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record063_result⟩)
 (.leaf ⟨(32, 11684754325520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 11685018566672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 11691195130112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record066_result⟩)
 (.leaf ⟨(32, 11691195711504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 11691457871888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 11691459952656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record069_result⟩)
 (.leaf ⟨(32, 11691463565440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 11692316623104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record071_result⟩)
 (.leaf ⟨(32, 11692322865408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 11692520136832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record073_result⟩)
 (.leaf ⟨(32, 11693463703808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 11700049854480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 11709726081152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record076_result⟩)
 (.leaf ⟨(32, 11729962598656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 11729970987008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 11822189084688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record079_result⟩)
 (.leaf ⟨(32, 11828628389904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 11828630470672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 11828898873360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record082_result⟩)
 (.leaf ⟨(32, 11846896599168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 11923118915840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 11923118981120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record085_result⟩)
 (.leaf ⟨(32, 11923123110016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 11923127011456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 11931691911424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record088_result⟩)
 (.leaf ⟨(32, 11931691976704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 11931696105600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 11931700167688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record091_result⟩)
 (.leaf ⟨(32, 11931716943873), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 11940281845888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 11958352904448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record094_result⟩)
 (.leaf ⟨(32, 11958352969728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 11958357098624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record096_result⟩)
 (.leaf ⟨(32, 11958359179392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 11958476605568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record098_result⟩)
 (.leaf ⟨(32, 11958551085312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00030.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29786 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29786 29886 :=
  block_of_table results 29786 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0995

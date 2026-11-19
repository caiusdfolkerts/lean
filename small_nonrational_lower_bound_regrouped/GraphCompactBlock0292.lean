module
prelude
import GraphInputsRow25Part00002Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0292
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(25, 3164726165504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record000_result⟩)
 (.branch 2
 (.leaf ⟨(25, 3166806540288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record001_result⟩)
 (.leaf ⟨(25, 3200042205184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(25, 3208479047936), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record003_result⟩)
 (.branch 5
 (.leaf ⟨(25, 3208743224064), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record004_result⟩)
 (.leaf ⟨(25, 3209015918592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(25, 3209024241664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record006_result⟩)
 (.branch 8
 (.leaf ⟨(25, 3217068949760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record007_result⟩)
 (.leaf ⟨(25, 3217737940992), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(25, 3225658916864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record009_result⟩)
 (.branch 11
 (.leaf ⟨(25, 3225931481088), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record010_result⟩)
 (.leaf ⟨(25, 3226195722240), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(25, 3232254459904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record012_result⟩)
 (.branch 14
 (.leaf ⟨(25, 3237075746816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record013_result⟩)
 (.leaf ⟨(25, 3240955478784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(25, 3241236496384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record015_result⟩)
 (.branch 17
 (.leaf ⟨(25, 3243308548096), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record016_result⟩)
 (.leaf ⟨(25, 3243316871168), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(25, 3249281204480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record018_result⟩)
 (.branch 20
 (.leaf ⟨(25, 3249818075136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record019_result⟩)
 (.leaf ⟨(25, 3249950195712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(25, 3338676502784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record021_result⟩)
 (.branch 23
 (.leaf ⟨(25, 3377129881856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record022_result⟩)
 (.leaf ⟨(25, 3423764250880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(25, 3423772639232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record024_result⟩)
 (.branch 26
 (.leaf ⟨(25, 3492490018816), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record025_result⟩)
 (.leaf ⟨(25, 3524702273536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(25, 3527447478272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record027_result⟩)
 (.branch 29
 (.leaf ⟨(25, 3629920583808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record028_result⟩)
 (.leaf ⟨(25, 3647842877440), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(25, 3784067809536), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record030_result⟩)
 (.branch 32
 (.leaf ⟨(25, 3786689019904), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record031_result⟩)
 (.leaf ⟨(25, 3853839794432), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(25, 3853967753472), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record033_result⟩)
 (.branch 35
 (.leaf ⟨(25, 3853971915008), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record034_result⟩)
 (.leaf ⟨(25, 3853971980288), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(25, 3854074646784), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record036_result⟩)
 (.branch 38
 (.leaf ⟨(25, 3861859274768), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record037_result⟩)
 (.leaf ⟨(25, 3866953257216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(25, 3921595138304), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record039_result⟩)
 (.branch 41
 (.leaf ⟨(25, 3921599299840), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record040_result⟩)
 (.leaf ⟨(25, 3921599365120), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(25, 3921602941184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record042_result⟩)
 (.branch 44
 (.leaf ⟨(25, 3922123032592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record043_result⟩)
 (.leaf ⟨(25, 3922655871232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(25, 3922655936512), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record045_result⟩)
 (.leaf ⟨(25, 3923196772353), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record046_result⟩))
 (.branch 48
 (.leaf ⟨(25, 3926160052480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record047_result⟩)
 (.leaf ⟨(25, 3926283782160), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record048_result⟩)))))))
 (.branch 74
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(25, 3927357521921), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record049_result⟩)
 (.branch 51
 (.leaf ⟨(25, 3935679086592), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record050_result⟩)
 (.leaf ⟨(25, 3935939100928), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(25, 3935947489280), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record052_result⟩)
 (.branch 54
 (.leaf ⟨(25, 3936071221504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record053_result⟩)
 (.leaf ⟨(25, 3990188200192), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(25, 4004664868864), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record055_result⟩)
 (.branch 57
 (.leaf ⟨(25, 4076733530112), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record056_result⟩)
 (.leaf ⟨(25, 4076741853184), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(25, 4080357409024), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record058_result⟩)
 (.branch 60
 (.leaf ⟨(25, 4081026400256), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record059_result⟩)
 (.leaf ⟨(25, 4136737181696), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(25, 4141826998528), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record061_result⟩)
 (.branch 63
 (.leaf ⟨(25, 4141831225344), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record062_result⟩)
 (.leaf ⟨(25, 4141835386880), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(25, 4142095433856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record064_result⟩)
 (.branch 66
 (.leaf ⟨(25, 4145315086464), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record065_result⟩)
 (.leaf ⟨(25, 4145449287808), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(25, 4286513709312), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record067_result⟩)
 (.branch 69
 (.leaf ⟨(25, 4329478324480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record068_result⟩)
 (.leaf ⟨(25, 4329482551296), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record069_result⟩)))
 (.branch 72
 (.branch 71
 (.leaf ⟨(25, 4329490614272), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record070_result⟩)
 (.leaf ⟨(25, 4329729952000), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record071_result⟩))
 (.branch 73
 (.leaf ⟨(25, 4333890570496), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record072_result⟩)
 (.leaf ⟨(25, 4333894697216), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record073_result⟩))))))
 (.branch 86
 (.branch 80
 (.branch 77
 (.branch 75
 (.leaf ⟨(25, 4333898958848), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record074_result⟩)
 (.branch 76
 (.leaf ⟨(25, 4333907215104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record075_result⟩)
 (.leaf ⟨(25, 4334179909632), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record076_result⟩)))
 (.branch 78
 (.leaf ⟨(25, 4334188232704), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record077_result⟩)
 (.branch 79
 (.leaf ⟨(25, 4334427308552), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record078_result⟩)
 (.leaf ⟨(25, 4342488825856), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record079_result⟩))))
 (.branch 83
 (.branch 81
 (.leaf ⟨(25, 4343025631232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record080_result⟩)
 (.branch 82
 (.leaf ⟨(25, 4346525810944), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record081_result⟩)
 (.leaf ⟨(25, 4346909884416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record082_result⟩)))
 (.branch 84
 (.leaf ⟨(25, 4347062681600), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record083_result⟩)
 (.branch 85
 (.leaf ⟨(25, 4347066843136), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record084_result⟩)
 (.leaf ⟨(25, 4347178287104), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record085_result⟩)))))
 (.branch 92
 (.branch 89
 (.branch 87
 (.leaf ⟨(25, 4355235315712), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record086_result⟩)
 (.branch 88
 (.leaf ⟨(25, 4355904241664), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record087_result⟩)
 (.leaf ⟨(25, 4359391805956), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record088_result⟩)))
 (.branch 90
 (.leaf ⟨(25, 4359668629504), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record089_result⟩)
 (.branch 91
 (.leaf ⟨(25, 4359928807424), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record090_result⟩)
 (.leaf ⟨(25, 4438121087232), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record091_result⟩))))
 (.branch 95
 (.branch 93
 (.leaf ⟨(25, 4438385328384), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record092_result⟩)
 (.branch 94
 (.leaf ⟨(25, 4438458728480), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record093_result⟩)
 (.leaf ⟨(25, 4451073097760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record094_result⟩)))
 (.branch 97
 (.branch 96
 (.leaf ⟨(25, 4485233606688), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record095_result⟩)
 (.leaf ⟨(25, 4485364629760), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record096_result⟩))
 (.branch 98
 (.leaf ⟨(25, 4485365727264), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record097_result⟩)
 (.leaf ⟨(25, 4485629968416), Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00002.record098_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (12312 + i))) 0 99 :=
  interval_of_check _ 0 99 (by decide +kernel)

public theorem complete : Block 12312 12411 :=
  block_of_table results 12312 99 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0292

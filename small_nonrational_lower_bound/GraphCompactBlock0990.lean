module
prelude
import GraphInputsSix0Part00025Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0990
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 9064601879808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 9065134588160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record001_result⟩)
 (.leaf ⟨(32, 9185404141696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 9202305106176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 9202573541504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record004_result⟩)
 (.leaf ⟨(32, 9202841976832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 9202846138368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 9245007331584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record007_result⟩)
 (.leaf ⟨(32, 9249828651136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 9254121521280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 9256267956352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record010_result⟩)
 (.leaf ⟨(32, 9270898753536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 9288480211072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 9423452447104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record013_result⟩)
 (.leaf ⟨(32, 9424575988608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 9424580215040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 9457811653504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record016_result⟩)
 (.leaf ⟨(32, 9457815879936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 9487876956544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 9492171923776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record019_result⟩)
 (.leaf ⟨(32, 9492440359104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 9493295465280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record021_result⟩)
 (.leaf ⟨(32, 9493297594624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 9493496930496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record023_result⟩)
 (.leaf ⟨(32, 9493561835776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 9495742840832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 9501883334912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record026_result⟩)
 (.leaf ⟨(32, 9518811545856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 9529202852096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 9529597296896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record029_result⟩)
 (.leaf ⟨(32, 9529601458432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 9529601523712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 9529605489920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record032_result⟩)
 (.leaf ⟨(32, 9529869795584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 9530001851648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 9530004127744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record035_result⟩)
 (.leaf ⟨(32, 9530134036736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 9530142359553), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 9530142425088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record038_result⟩)
 (.leaf ⟨(32, 9530947731712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 9536517718144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 9538323350784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record041_result⟩)
 (.leaf ⟨(32, 9538455535872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 9538463924224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 9538723938560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record044_result⟩)
 (.leaf ⟨(32, 9538732326912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 9538856059136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record046_result⟩)
 (.leaf ⟨(32, 9544564475136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 9545097183488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record048_result⟩)
 (.leaf ⟨(32, 9565710065920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 9659125612672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 9665366737024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record051_result⟩)
 (.leaf ⟨(32, 9666406924416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 9675894456576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 9675902844928), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record054_result⟩)
 (.leaf ⟨(32, 9676162891904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 9676295012480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 9682267701504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record057_result⟩)
 (.leaf ⟨(32, 9682536136832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 9682804572160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 9682808733696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record060_result⟩)
 (.leaf ⟨(32, 9762003501184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 9768442806400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 9769482993792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record063_result⟩)
 (.leaf ⟨(32, 9786185777408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 9792613826816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 9795239166080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record066_result⟩)
 (.leaf ⟨(32, 9801678471296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 9810264211584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 9820577104128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record069_result⟩)
 (.leaf ⟨(32, 9820581330944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 9820585492480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record071_result⟩)
 (.leaf ⟨(32, 9820589523968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 9820721644544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record073_result⟩)
 (.leaf ⟨(32, 9820845376256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 9820979740800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 9820985885696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record076_result⟩)
 (.leaf ⟨(32, 9821113811584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 9898998972800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 9932267667840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record079_result⟩)
 (.leaf ⟨(32, 9933324239232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 9934553506176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 9974533267648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record082_result⟩)
 (.leaf ⟨(32, 10000103735304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 10010105053184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 10010239189248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record085_result⟩)
 (.leaf ⟨(32, 10025600812288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 10026133520640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 10037498552704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record088_result⟩)
 (.leaf ⟨(32, 10037632770368), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 10041203687424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 10043053392128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record091_result⟩)
 (.leaf ⟨(32, 10043317633280), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 10051907535104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 10053615649024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record094_result⟩)
 (.leaf ⟨(32, 10071306174720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 10073386549504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record096_result⟩)
 (.leaf ⟨(32, 10078824448256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 10080701448448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record098_result⟩)
 (.leaf ⟨(32, 10085143200000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00025.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (29286 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 29286 29386 :=
  block_of_table results 29286 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0990

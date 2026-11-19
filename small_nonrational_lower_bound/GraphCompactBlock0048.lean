module
prelude
import GraphInputsRow19Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0048
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 14701941629184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 14701950017536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record001_result⟩)
 (.leaf ⟨(19, 14701950927872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 14702478361120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 14707336486976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record004_result⟩)
 (.leaf ⟨(19, 14708409704512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 14715113250880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 14726119047168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record007_result⟩)
 (.leaf ⟨(19, 14729697361920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 14730530398208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 14730531438592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record010_result⟩)
 (.leaf ⟨(19, 14732888114240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 14742752266304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 14776995447040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record013_result⟩)
 (.leaf ⟨(19, 14776995512320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 14777129713664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 14777398116352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record016_result⟩)
 (.leaf ⟨(19, 14777445255424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 14779277123840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 14779277189120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record019_result⟩)
 (.leaf ⟨(19, 14779541430272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(19, 14779599030304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record021_result⟩)
 (.leaf ⟨(19, 14783488198912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record022_result⟩))
 (.branch 24
 (.leaf ⟨(19, 14783834300416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record023_result⟩)
 (.leaf ⟨(19, 14783891900448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(19, 14794625122305), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 14804828816384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record026_result⟩)
 (.leaf ⟨(19, 14805356249632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(19, 14849087209728), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record028_result⟩)
 (.branch 30
 (.leaf ⟨(19, 14862270955536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record029_result⟩)
 (.leaf ⟨(19, 14886913016064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(19, 14914840264720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record031_result⟩)
 (.branch 33
 (.leaf ⟨(19, 14921279569936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record032_result⟩)
 (.leaf ⟨(19, 14939273101568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(19, 14939553013760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(19, 14939818295296), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record035_result⟩)
 (.leaf ⟨(19, 14986797654272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(19, 15003977523200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record037_result⟩)
 (.branch 39
 (.leaf ⟨(19, 15004234481664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record038_result⟩)
 (.leaf ⟨(19, 15004242804736), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(19, 15011490045952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record040_result⟩)
 (.branch 42
 (.leaf ⟨(19, 15036290433024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record041_result⟩)
 (.leaf ⟨(19, 15051202330624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(19, 15051255712000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record043_result⟩)
 (.branch 45
 (.leaf ⟨(19, 15068435578881), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record044_result⟩)
 (.leaf ⟨(19, 15075386654976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(19, 15075395043328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record046_result⟩)
 (.leaf ⟨(19, 15075889389824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record047_result⟩))
 (.branch 49
 (.leaf ⟨(19, 15075897778176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record048_result⟩)
 (.leaf ⟨(19, 15076476256512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(19, 15076484644864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record050_result⟩)
 (.branch 52
 (.leaf ⟨(19, 15076955259904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record051_result⟩)
 (.leaf ⟨(19, 15077012931328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(19, 15132826542080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record053_result⟩)
 (.branch 55
 (.leaf ⟨(19, 15133083500544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record054_result⟩)
 (.leaf ⟨(19, 15133091823616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(19, 15145308790784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record056_result⟩)
 (.branch 58
 (.leaf ⟨(19, 15145440911360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record057_result⟩)
 (.leaf ⟨(19, 15148660563968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(19, 15180733939712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record059_result⟩)
 (.branch 61
 (.leaf ⟨(19, 15180742262784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record060_result⟩)
 (.leaf ⟨(19, 15180874383360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(19, 15180965150720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record062_result⟩)
 (.branch 64
 (.leaf ⟨(19, 15181138624512), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record063_result⟩)
 (.leaf ⟨(19, 15188372848640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(19, 15191043473409), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record065_result⟩)
 (.branch 67
 (.leaf ⟨(19, 15196149612544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record066_result⟩)
 (.leaf ⟨(19, 15196160528416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(19, 15197284597761), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 15212829802496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record069_result⟩)
 (.leaf ⟨(19, 15212837085184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 15213068296192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record071_result⟩)
 (.leaf ⟨(19, 15213332537344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 15213579735072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record073_result⟩)
 (.leaf ⟨(19, 15213596778496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(19, 15213597818880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 15213919404032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record076_result⟩)
 (.leaf ⟨(19, 15214116479232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(19, 15214124867584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 15214125777920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record079_result⟩)
 (.leaf ⟨(19, 15221658058752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(19, 15230520262657), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 15247955984896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record082_result⟩)
 (.leaf ⟨(19, 15256887820544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(19, 15256958042368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 15256958107648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record085_result⟩)
 (.leaf ⟨(19, 15256961163520), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(19, 15257086001408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 15257092308992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record088_result⟩)
 (.leaf ⟨(19, 15257093284096), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(19, 15257360711680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 15257407850752), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record091_result⟩)
 (.leaf ⟨(19, 15259551170816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(19, 15260305654016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record093_result⟩)
 (.branch 95
 (.leaf ⟨(19, 15260312936704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record094_result⟩)
 (.leaf ⟨(19, 15260313001984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(19, 15260330232064), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record096_result⟩)
 (.leaf ⟨(19, 15260574121984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record097_result⟩))
 (.branch 99
 (.leaf ⟨(19, 15260577243136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record098_result⟩)
 (.leaf ⟨(19, 15260601813024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00008.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2898 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 2898 2998 :=
  block_of_table results 2898 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0048

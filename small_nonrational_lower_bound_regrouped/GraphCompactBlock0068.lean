module
prelude
import GraphInputsRow19Part00028Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0068
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(19, 30241152602368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record000_result⟩)
 (.leaf ⟨(19, 30275515977984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record001_result⟩))
 (.branch 3
 (.leaf ⟨(19, 30276606558208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record002_result⟩)
 (.leaf ⟨(19, 30284217585920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(19, 30285291388928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record004_result⟩)
 (.leaf ⟨(19, 30285332742144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record005_result⟩))
 (.branch 7
 (.leaf ⟨(19, 30308818812928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 30309874667776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record007_result⟩)
 (.leaf ⟨(19, 30310965248000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(19, 30315258118144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record009_result⟩)
 (.leaf ⟨(19, 30317503643648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record010_result⟩))
 (.branch 12
 (.leaf ⟨(19, 30317544996864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record011_result⟩)
 (.branch 13
 (.leaf ⟨(19, 30320624205824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record012_result⟩)
 (.leaf ⟨(19, 30341014290432), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(19, 30344233943040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record014_result⟩)
 (.leaf ⟨(19, 30348526813184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record015_result⟩))
 (.branch 17
 (.leaf ⟨(19, 30348641833216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record016_result⟩)
 (.branch 18
 (.leaf ⟨(19, 30352819683328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record017_result⟩)
 (.leaf ⟨(19, 30353876254720), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(19, 30443892178944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record019_result⟩)
 (.leaf ⟨(19, 30443958239232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record020_result⟩))
 (.branch 22
 (.leaf ⟨(19, 30445031456768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record021_result⟩)
 (.leaf ⟨(19, 30447310012416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(19, 30447358972160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record023_result⟩)
 (.leaf ⟨(19, 30449456447488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record024_result⟩))
 (.branch 26
 (.leaf ⟨(19, 30457794330624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record025_result⟩)
 (.branch 27
 (.leaf ⟨(19, 30457802653696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record026_result⟩)
 (.leaf ⟨(19, 30458297585664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(19, 30477243449344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record028_result⟩)
 (.leaf ⟨(19, 30477490850048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record029_result⟩))
 (.branch 31
 (.leaf ⟨(19, 30481651468544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 30481668113152), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record031_result⟩)
 (.leaf ⟨(19, 30833140367360), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(19, 30833146609664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record033_result⟩)
 (.leaf ⟨(19, 30833344790528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record034_result⟩))
 (.branch 36
 (.leaf ⟨(19, 30848402866176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record035_result⟩)
 (.branch 37
 (.leaf ⟨(19, 30859630027040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record036_result⟩)
 (.leaf ⟨(19, 30859634188576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record037_result⟩)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(19, 30861832585232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record038_result⟩)
 (.leaf ⟨(19, 30897797660672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record039_result⟩))
 (.branch 41
 (.leaf ⟨(19, 30897805983744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record040_result⟩)
 (.leaf ⟨(19, 30899413532672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(19, 30901826289664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record042_result⟩)
 (.leaf ⟨(19, 30901958410240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record043_result⟩))
 (.branch 45
 (.leaf ⟨(19, 30901966733312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record044_result⟩)
 (.branch 46
 (.leaf ⟨(19, 30902164914176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record045_result⟩)
 (.leaf ⟨(19, 30903708483584), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record046_result⟩)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(19, 30904236965888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record047_result⟩)
 (.leaf ⟨(19, 30904245288960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record048_result⟩))
 (.branch 50
 (.leaf ⟨(19, 30904748670976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record049_result⟩)
 (.branch 51
 (.leaf ⟨(19, 30910147788800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record050_result⟩)
 (.leaf ⟨(19, 30913334411264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record051_result⟩))))
 (.branch 54
 (.branch 53
 (.leaf ⟨(19, 30916727537664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record052_result⟩)
 (.leaf ⟨(19, 30917429100544), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record053_result⟩))
 (.branch 55
 (.leaf ⟨(19, 30917495160832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record054_result⟩)
 (.branch 56
 (.leaf ⟨(19, 30917627281408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record055_result⟩)
 (.leaf ⟨(19, 30918262136832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record056_result⟩))))))
 (.branch 66
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(19, 30918263177216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record057_result⟩)
 (.leaf ⟨(19, 30936222679040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record058_result⟩))
 (.branch 60
 (.leaf ⟨(19, 30944271548672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record059_result⟩)
 (.leaf ⟨(19, 30945039630336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(19, 30951784071424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record061_result⟩)
 (.leaf ⟨(19, 30959492735040), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record062_result⟩))
 (.branch 64
 (.leaf ⟨(19, 30959756976192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record063_result⟩)
 (.branch 65
 (.leaf ⟨(19, 30960565952576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record064_result⟩)
 (.leaf ⟨(19, 30977507213568), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record065_result⟩)))))
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf ⟨(19, 30978275295232), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record066_result⟩)
 (.leaf ⟨(19, 30978803237952), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record067_result⟩))
 (.branch 69
 (.leaf ⟨(19, 30979397780032), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record068_result⟩)
 (.branch 70
 (.leaf ⟨(19, 30979399877120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record069_result⟩)
 (.leaf ⟨(19, 30981915443456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record070_result⟩))))
 (.branch 73
 (.branch 72
 (.leaf ⟨(19, 30981926952960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record071_result⟩)
 (.leaf ⟨(19, 30986076307712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record072_result⟩))
 (.branch 74
 (.leaf ⟨(19, 30986084549696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record073_result⟩)
 (.branch 75
 (.leaf ⟨(19, 30986117579840), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record074_result⟩)
 (.leaf ⟨(19, 31007626559488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00028.record075_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4839 + i))) 0 76 :=
  interval_of_check _ 0 76 (by decide +kernel)

public theorem complete : Block 4839 4915 :=
  block_of_table results 4839 76 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0068

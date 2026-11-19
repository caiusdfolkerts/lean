module
prelude
import GraphInputsSix0Part00088Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1053
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 33
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 34087171526672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record000_result⟩)
 (.leaf ⟨(32, 34087180177664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 34087180242944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record002_result⟩)
 (.leaf ⟨(32, 34087188301840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 34087302074432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record004_result⟩)
 (.leaf ⟨(32, 34087303647248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 34087320422416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record006_result⟩)
 (.leaf ⟨(32, 34088253719040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(32, 34088262041601), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record008_result⟩)
 (.leaf ⟨(32, 34088358645824), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record009_result⟩))
 (.branch 11
 (.leaf ⟨(32, 34088394162177), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record010_result⟩)
 (.leaf ⟨(32, 34090398023936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(32, 34090431054080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record012_result⟩)
 (.leaf ⟨(32, 34093561546768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record013_result⟩))
 (.branch 15
 (.leaf ⟨(32, 34094007193616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record014_result⟩)
 (.leaf ⟨(32, 34094023968784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(32, 34095097708545), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record016_result⟩)
 (.leaf ⟨(32, 34119375655168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record017_result⟩))
 (.branch 19
 (.leaf ⟨(32, 34119514067008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record018_result⟩)
 (.leaf ⟨(32, 34123666718976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(32, 34123792123920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record020_result⟩)
 (.leaf ⟨(32, 34123809292289), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record021_result⟩))
 (.branch 23
 (.leaf ⟨(32, 34124794494976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record022_result⟩)
 (.leaf ⟨(32, 34124865863681), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(32, 34127952873488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record024_result⟩)
 (.leaf ⟨(32, 34155878973696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record025_result⟩))
 (.branch 27
 (.leaf ⟨(32, 34194382291200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record026_result⟩)
 (.leaf ⟨(32, 34194419941376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(32, 34195732692992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record028_result⟩)
 (.leaf ⟨(32, 34196261175296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record029_result⟩))
 (.branch 31
 (.leaf ⟨(32, 34222385664256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record030_result⟩)
 (.branch 32
 (.leaf ⟨(32, 34222391955520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record031_result⟩)
 (.leaf ⟨(32, 34223424553216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record032_result⟩)))))))
 (.branch 50
 (.branch 41
 (.branch 37
 (.branch 35
 (.branch 34
 (.leaf ⟨(32, 34223943852096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record033_result⟩)
 (.leaf ⟨(32, 34239548622864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record034_result⟩))
 (.branch 36
 (.leaf ⟨(32, 34240604422144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record035_result⟩)
 (.leaf ⟨(32, 34497227923520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record036_result⟩)))
 (.branch 39
 (.branch 38
 (.leaf ⟨(32, 34497228980224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record037_result⟩)
 (.leaf ⟨(32, 34497230800896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record038_result⟩))
 (.branch 40
 (.leaf ⟨(32, 34497278249024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record039_result⟩)
 (.leaf ⟨(32, 34498318305344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record040_result⟩))))
 (.branch 45
 (.branch 43
 (.branch 42
 (.leaf ⟨(32, 34498320402432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record041_result⟩)
 (.leaf ⟨(32, 34498334949952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record042_result⟩))
 (.branch 44
 (.leaf ⟨(32, 34498452390408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record043_result⟩)
 (.leaf ⟨(32, 34531553970240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(32, 34531554246656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record045_result⟩)
 (.leaf ⟨(32, 34531556067328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record046_result⟩))
 (.branch 48
 (.leaf ⟨(32, 34531671410696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record047_result⟩)
 (.branch 49
 (.leaf ⟨(32, 34531688055304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record048_result⟩)
 (.leaf ⟨(32, 34634633713920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record049_result⟩))))))
 (.branch 58
 (.branch 54
 (.branch 52
 (.branch 51
 (.leaf ⟨(32, 34634633775120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record050_result⟩)
 (.leaf ⟨(32, 34634667426048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record051_result⟩))
 (.branch 53
 (.leaf ⟨(32, 34634667491328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record052_result⟩)
 (.leaf ⟨(32, 34634671067392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record053_result⟩)))
 (.branch 56
 (.branch 55
 (.leaf ⟨(32, 34634671132672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record054_result⟩)
 (.leaf ⟨(32, 34634679191568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record055_result⟩))
 (.branch 57
 (.leaf ⟨(32, 34634910142480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record056_result⟩)
 (.leaf ⟨(32, 34634910402576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record057_result⟩))))
 (.branch 62
 (.branch 60
 (.branch 59
 (.leaf ⟨(32, 34635742478592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record058_result⟩)
 (.leaf ⟨(32, 34635744608768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record059_result⟩))
 (.branch 61
 (.leaf ⟨(32, 34635746705408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record060_result⟩)
 (.leaf ⟨(32, 34635752931329), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record061_result⟩)))
 (.branch 64
 (.branch 63
 (.leaf ⟨(32, 34635841569024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record062_result⟩)
 (.leaf ⟨(32, 34635845795840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record063_result⟩))
 (.branch 65
 (.leaf ⟨(32, 34635853598720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record064_result⟩)
 (.branch 66
 (.leaf ⟨(32, 34635966973968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record065_result⟩)
 (.leaf ⟨(32, 34635984142337), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00088.record066_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34996 + i))) 0 67 :=
  interval_of_check _ 0 67 (by decide +kernel)

public theorem complete : Block 34996 35063 :=
  block_of_table results 34996 67 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1053

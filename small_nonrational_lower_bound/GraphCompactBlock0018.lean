module
prelude
import GraphInputsRow16Part00018Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0018
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 34
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 19015776878592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record000_result⟩)
 (.leaf ⟨(16, 19015834550528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 19015836696576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record002_result⟩)
 (.leaf ⟨(16, 19016678703104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 19050638950400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record004_result⟩)
 (.leaf ⟨(16, 19093551842560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 19099858182144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record006_result⟩)
 (.leaf ⟨(16, 19099996545024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 19127743889408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record008_result⟩)
 (.leaf ⟨(16, 19127814111232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 19128577966080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record010_result⟩)
 (.leaf ⟨(16, 19401618260224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 19401618325504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record012_result⟩)
 (.leaf ⟨(16, 19402159292416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 19402289332224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 19451514749184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record015_result⟩)
 (.leaf ⟨(16, 19470832664832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record016_result⟩))))))
 (.branch 25
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 19470902951936), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record017_result⟩)
 (.leaf ⟨(16, 19470911275008), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 19473441570816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record019_result⟩)
 (.leaf ⟨(16, 19504138616832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 19504146939904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record021_result⟩)
 (.leaf ⟨(16, 19506269323264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 19531008311296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record023_result⟩)
 (.leaf ⟨(16, 19588685267200), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record024_result⟩))))
 (.branch 29
 (.branch 27
 (.branch 26
 (.leaf ⟨(16, 19607941349376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record025_result⟩)
 (.leaf ⟨(16, 19610976460800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record026_result⟩))
 (.branch 28
 (.leaf ⟨(16, 19649680965632), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record027_result⟩)
 (.leaf ⟨(16, 19724798820608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record028_result⟩)))
 (.branch 31
 (.branch 30
 (.leaf ⟨(16, 19763967361024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record029_result⟩)
 (.leaf ⟨(16, 19977312747520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record030_result⟩))
 (.branch 32
 (.leaf ⟨(16, 19977719513088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 19977909370880), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record032_result⟩)
 (.leaf ⟨(16, 19985898422528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record033_result⟩)))))))
 (.branch 51
 (.branch 42
 (.branch 38
 (.branch 36
 (.branch 35
 (.leaf ⟨(16, 19993245859840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record034_result⟩)
 (.leaf ⟨(16, 20012511297792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record035_result⟩))
 (.branch 37
 (.leaf ⟨(16, 20012511363072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record036_result⟩)
 (.leaf ⟨(16, 20012744654848), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(16, 20047036891136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record038_result⟩)
 (.leaf ⟨(16, 20047038776576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record039_result⟩))
 (.branch 41
 (.leaf ⟨(16, 20047707767296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record040_result⟩)
 (.leaf ⟨(16, 20061863755776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record041_result⟩))))
 (.branch 46
 (.branch 44
 (.branch 43
 (.leaf ⟨(16, 20150146318592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record042_result⟩)
 (.leaf ⟨(16, 20561754358016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record043_result⟩))
 (.branch 45
 (.leaf ⟨(16, 20570014023680), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record044_result⟩)
 (.leaf ⟨(16, 20572949004288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(16, 20597191016448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record046_result⟩)
 (.leaf ⟨(16, 20694635127040), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record047_result⟩))
 (.branch 49
 (.leaf ⟨(16, 20730068664320), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record048_result⟩)
 (.branch 50
 (.leaf ⟨(16, 21042826379264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record049_result⟩)
 (.leaf ⟨(16, 21480618361088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record050_result⟩))))))
 (.branch 60
 (.branch 55
 (.branch 53
 (.branch 52
 (.leaf ⟨(16, 21557112504576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record051_result⟩)
 (.leaf ⟨(16, 21558189948928), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record052_result⟩))
 (.branch 54
 (.leaf ⟨(16, 21573792759808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record053_result⟩)
 (.leaf ⟨(16, 21653749268736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record054_result⟩)))
 (.branch 57
 (.branch 56
 (.leaf ⟨(16, 21669389336576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record055_result⟩)
 (.leaf ⟨(16, 21670429523968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record056_result⟩))
 (.branch 58
 (.leaf ⟨(16, 21685961261312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record057_result⟩)
 (.branch 59
 (.leaf ⟨(16, 21927087374336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record058_result⟩)
 (.leaf ⟨(16, 21960323039232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record059_result⟩)))))
 (.branch 64
 (.branch 62
 (.branch 61
 (.leaf ⟨(16, 22121037185024), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record060_result⟩)
 (.leaf ⟨(16, 22174591156224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record061_result⟩))
 (.branch 63
 (.leaf ⟨(16, 22182778454016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record062_result⟩)
 (.leaf ⟨(16, 22182912655360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record063_result⟩)))
 (.branch 66
 (.branch 65
 (.leaf ⟨(16, 22183172669696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record064_result⟩)
 (.leaf ⟨(16, 22183176896512), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record065_result⟩))
 (.branch 67
 (.leaf ⟨(16, 22183183138816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record066_result⟩)
 (.branch 68
 (.leaf ⟨(16, 22183315259392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record067_result⟩)
 (.leaf ⟨(16, 22184924823808), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00018.record068_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1127 + i))) 0 69 :=
  interval_of_check _ 0 69 (by decide +kernel)

public theorem complete : Block 1127 1196 :=
  block_of_table results 1127 69 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0018

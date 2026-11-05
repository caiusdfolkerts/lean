module
prelude
import GraphInputsRow16Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0017
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 35
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(16, 17489262346240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record000_result⟩)
 (.leaf ⟨(16, 17489270409216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record001_result⟩))
 (.branch 3
 (.leaf ⟨(16, 17493678753792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record002_result⟩)
 (.leaf ⟨(16, 17497839503360), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(16, 17558120169472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record004_result⟩)
 (.leaf ⟨(16, 17566970150912), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record005_result⟩))
 (.branch 7
 (.leaf ⟨(16, 17583596242944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record006_result⟩)
 (.leaf ⟨(16, 17583613018112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(16, 17787283079168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record008_result⟩)
 (.leaf ⟨(16, 17848351097088), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record009_result⟩))
 (.branch 11
 (.leaf ⟨(16, 17848351162368), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record010_result⟩)
 (.leaf ⟨(16, 17848479056128), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(16, 17848487444480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record012_result⟩)
 (.leaf ⟨(16, 17848619565056), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record013_result⟩))
 (.branch 15
 (.leaf ⟨(16, 17852730998784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record014_result⟩)
 (.branch 16
 (.leaf ⟨(16, 17856668434688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record015_result⟩)
 (.leaf ⟨(16, 17856672596224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(16, 17856672661504), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record017_result⟩)
 (.leaf ⟨(16, 17857201078528), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record018_result⟩))
 (.branch 20
 (.leaf ⟨(16, 17857205305344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record019_result⟩)
 (.leaf ⟨(16, 17857211547648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 17857213628416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record021_result⟩)
 (.leaf ⟨(16, 17860967612416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 17861231853568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record023_result⟩)
 (.branch 25
 (.leaf ⟨(16, 17861504417792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record024_result⟩)
 (.leaf ⟨(16, 17861564235776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(16, 17861570478080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record026_result⟩)
 (.leaf ⟨(16, 18272751714304), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record027_result⟩))
 (.branch 29
 (.leaf ⟨(16, 18300498116608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record028_result⟩)
 (.leaf ⟨(16, 18328582160384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(16, 18333766811648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record030_result⟩)
 (.leaf ⟨(16, 18335087525888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record031_result⟩))
 (.branch 33
 (.leaf ⟨(16, 18335095848960), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record032_result⟩)
 (.branch 34
 (.leaf ⟨(16, 18337167900672), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record033_result⟩)
 (.leaf ⟨(16, 18337176223744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record034_result⟩)))))))
 (.branch 53
 (.branch 44
 (.branch 39
 (.branch 37
 (.branch 36
 (.leaf ⟨(16, 18338216411136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record035_result⟩)
 (.leaf ⟨(16, 18344382111744), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record036_result⟩))
 (.branch 38
 (.leaf ⟨(16, 18368847446272), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record037_result⟩)
 (.leaf ⟨(16, 18407026130944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record038_result⟩)))
 (.branch 41
 (.branch 40
 (.leaf ⟨(16, 18407034454016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record039_result⟩)
 (.leaf ⟨(16, 18465484275712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record040_result⟩))
 (.branch 42
 (.leaf ⟨(16, 18550305652736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record041_result⟩)
 (.branch 43
 (.leaf ⟨(16, 18822230786048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record042_result⟩)
 (.leaf ⟨(16, 18822563168256), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record043_result⟩)))))
 (.branch 48
 (.branch 46
 (.branch 45
 (.leaf ⟨(16, 18822569410560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record044_result⟩)
 (.leaf ⟨(16, 18878203756544), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record045_result⟩))
 (.branch 47
 (.leaf ⟨(16, 18886655295488), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record046_result⟩)
 (.leaf ⟨(16, 18886789496832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record047_result⟩)))
 (.branch 50
 (.branch 49
 (.leaf ⟨(16, 18886797819904), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record048_result⟩)
 (.leaf ⟨(16, 18886987677696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record049_result⟩))
 (.branch 51
 (.leaf ⟨(16, 18886993920000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record050_result⟩)
 (.branch 52
 (.leaf ⟨(16, 18913468432384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record051_result⟩)
 (.leaf ⟨(16, 18921156509696), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record052_result⟩))))))
 (.branch 62
 (.branch 57
 (.branch 55
 (.branch 54
 (.leaf ⟨(16, 18921585443072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record053_result⟩)
 (.leaf ⟨(16, 18921589604608), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record054_result⟩))
 (.branch 56
 (.leaf ⟨(16, 18921589669888), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record055_result⟩)
 (.leaf ⟨(16, 18921789931520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record056_result⟩)))
 (.branch 59
 (.branch 58
 (.leaf ⟨(16, 18921822961664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record057_result⟩)
 (.leaf ⟨(16, 18922058334208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record058_result⟩))
 (.branch 60
 (.leaf ⟨(16, 18922320494592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record059_result⟩)
 (.branch 61
 (.leaf ⟨(16, 18922326736896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record060_result⟩)
 (.leaf ⟨(16, 18956115197952), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record061_result⟩)))))
 (.branch 66
 (.branch 64
 (.branch 63
 (.leaf ⟨(16, 18956786074112), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record062_result⟩)
 (.leaf ⟨(16, 19015105806592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record063_result⟩))
 (.branch 65
 (.leaf ⟨(16, 19015105871872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record064_result⟩)
 (.leaf ⟨(16, 19015240073216), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record065_result⟩)))
 (.branch 68
 (.branch 67
 (.leaf ⟨(16, 19015374274560), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record066_result⟩)
 (.leaf ⟨(16, 19015634288896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record067_result⟩))
 (.branch 69
 (.leaf ⟨(16, 19015638515712), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record068_result⟩)
 (.branch 70
 (.leaf ⟨(16, 19015644758016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record069_result⟩)
 (.leaf ⟨(16, 19015646838784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00017.record070_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (1056 + i))) 0 71 :=
  interval_of_check _ 0 71 (by decide +kernel)

public theorem complete : Block 1056 1127 :=
  block_of_table results 1056 71 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0017

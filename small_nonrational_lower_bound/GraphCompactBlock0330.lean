module
prelude
import GraphInputsRow26Part00014Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0330
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 8654635925504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record000_result⟩)
 (.leaf ⟨(26, 8729659506944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 8732226420736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record002_result⟩)
 (.leaf ⟨(26, 8732234743808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 8734092886016), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record004_result⟩)
 (.leaf ⟨(26, 8734629691392), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 8744830371840), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record006_result⟩)
 (.leaf ⟨(26, 8744956395520), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(26, 8745113354240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record008_result⟩)
 (.leaf ⟨(26, 8746839375872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record009_result⟩))
 (.branch 11
 (.leaf ⟨(26, 8747111940096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record010_result⟩)
 (.leaf ⟨(26, 8757975318528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(26, 8766305140736), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record012_result⟩)
 (.leaf ⟨(26, 8775163445248), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record013_result⟩))
 (.branch 15
 (.leaf ⟨(26, 8783484944384), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record014_result⟩)
 (.leaf ⟨(26, 8836431839616), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record015_result⟩)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ⟨(26, 8870526288256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record016_result⟩)
 (.leaf ⟨(26, 8910455095680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record017_result⟩))
 (.branch 19
 (.leaf ⟨(26, 8911862169600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record018_result⟩)
 (.leaf ⟨(26, 8980447428608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record019_result⟩)))
 (.branch 22
 (.branch 21
 (.leaf ⟨(26, 8988768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record020_result⟩)
 (.leaf ⟨(26, 9056555122816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record021_result⟩))
 (.branch 23
 (.leaf ⟨(26, 9064601879808), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record022_result⟩)
 (.leaf ⟨(26, 9065134588160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record023_result⟩))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 9185404141696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record024_result⟩)
 (.leaf ⟨(26, 9202305106176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 9202573541504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record026_result⟩)
 (.leaf ⟨(26, 9202841976832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record027_result⟩)))
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 9202846138368), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record028_result⟩)
 (.leaf ⟨(26, 9245007331584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 9249828651136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record030_result⟩)
 (.leaf ⟨(26, 9254121521280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record031_result⟩))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf ⟨(26, 9256267956352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record032_result⟩)
 (.leaf ⟨(26, 9270898753536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record033_result⟩))
 (.branch 35
 (.leaf ⟨(26, 9288480211072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record034_result⟩)
 (.leaf ⟨(26, 9424575988608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record035_result⟩)))
 (.branch 38
 (.branch 37
 (.leaf ⟨(26, 9495742840832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record036_result⟩)
 (.leaf ⟨(26, 9518811545856), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record037_result⟩))
 (.branch 39
 (.leaf ⟨(26, 9529597296896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record038_result⟩)
 (.leaf ⟨(26, 9529601523712), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record039_result⟩))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf ⟨(26, 9529605489920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record040_result⟩)
 (.leaf ⟨(26, 9530004127744), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record041_result⟩))
 (.branch 43
 (.leaf ⟨(26, 9544564475136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record042_result⟩)
 (.leaf ⟨(26, 9545097183488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record043_result⟩)))
 (.branch 46
 (.branch 45
 (.leaf ⟨(26, 9565710065920), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record044_result⟩)
 (.leaf ⟨(26, 9666406924416), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record045_result⟩))
 (.branch 47
 (.leaf ⟨(26, 9675902844928), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record046_result⟩)
 (.leaf ⟨(26, 9676295012480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record047_result⟩)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf ⟨(26, 9682267701504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record048_result⟩)
 (.leaf ⟨(26, 9682804572160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record049_result⟩))
 (.branch 51
 (.leaf ⟨(26, 9682808733696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record050_result⟩)
 (.leaf ⟨(26, 9786185777408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 9792613826816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record052_result⟩)
 (.leaf ⟨(26, 9795239166080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 9810264211584), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record054_result⟩)
 (.leaf ⟨(26, 9820585492480), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record055_result⟩))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf ⟨(26, 9820979740800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record056_result⟩)
 (.leaf ⟨(26, 9820985885696), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record057_result⟩))
 (.branch 59
 (.leaf ⟨(26, 10025600812288), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record058_result⟩)
 (.leaf ⟨(26, 10037498552704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record059_result⟩)))
 (.branch 62
 (.branch 61
 (.leaf ⟨(26, 10041203687424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record060_result⟩)
 (.leaf ⟨(26, 10088931753984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record061_result⟩))
 (.branch 63
 (.leaf ⟨(26, 10090025321728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record062_result⟩)
 (.leaf ⟨(26, 10090165829633), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00014.record063_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (14771 + i))) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)

public theorem complete : Block 14771 14835 :=
  block_of_table results 14771 64 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0330

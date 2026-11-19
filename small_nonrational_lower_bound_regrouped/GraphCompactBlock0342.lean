module
prelude
import GraphInputsRow26Part00026Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0342
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 28
 (.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ⟨(26, 16976153935872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record000_result⟩)
 (.branch 2
 (.leaf ⟨(26, 16976261218304), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record001_result⟩)
 (.leaf ⟨(26, 16978292047872), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record002_result⟩)))
 (.branch 5
 (.branch 4
 (.leaf ⟨(26, 16978300370944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record003_result⟩)
 (.leaf ⟨(26, 16978341593088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record004_result⟩))
 (.branch 6
 (.leaf ⟨(26, 16982857482240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record005_result⟩)
 (.leaf ⟨(26, 16982972047360), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record006_result⟩))))
 (.branch 10
 (.branch 8
 (.leaf ⟨(26, 17003842764800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record007_result⟩)
 (.branch 9
 (.leaf ⟨(26, 17010356453376), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record008_result⟩)
 (.leaf ⟨(26, 17042489282688), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record009_result⟩)))
 (.branch 12
 (.branch 11
 (.leaf ⟨(26, 17042724163600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record010_result⟩)
 (.leaf ⟨(26, 17043780995088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record011_result⟩))
 (.branch 13
 (.leaf ⟨(26, 17043798196224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record012_result⟩)
 (.leaf ⟨(26, 17048105189632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record013_result⟩)))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ⟨(26, 17048113577984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record014_result⟩)
 (.branch 16
 (.leaf ⟨(26, 17051578536192), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record015_result⟩)
 (.leaf ⟨(26, 17051578601472), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record016_result⟩)))
 (.branch 19
 (.branch 18
 (.leaf ⟨(26, 17051603175440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record017_result⟩)
 (.leaf ⟨(26, 17052406448128), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record018_result⟩))
 (.branch 20
 (.leaf ⟨(26, 17052497150208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record019_result⟩)
 (.leaf ⟨(26, 17052670689280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record020_result⟩))))
 (.branch 24
 (.branch 22
 (.leaf ⟨(26, 17052676915201), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record021_result⟩)
 (.branch 23
 (.leaf ⟨(26, 17052765552896), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record022_result⟩)
 (.leaf ⟨(26, 17052777582592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record023_result⟩)))
 (.branch 26
 (.branch 25
 (.leaf ⟨(26, 17056120967424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record024_result⟩)
 (.leaf ⟨(26, 17082431373568), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record025_result⟩))
 (.branch 27
 (.leaf ⟨(26, 17082968244224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record026_result⟩)
 (.leaf ⟨(26, 17082976567296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record027_result⟩))))))
 (.branch 42
 (.branch 35
 (.branch 31
 (.branch 29
 (.leaf ⟨(26, 17086592123136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record028_result⟩)
 (.branch 30
 (.leaf ⟨(26, 17086864752640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record029_result⟩)
 (.leaf ⟨(26, 17087128993792), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record030_result⟩)))
 (.branch 33
 (.branch 32
 (.leaf ⟨(26, 17087137316864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record031_result⟩)
 (.leaf ⟨(26, 17089712685312), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record032_result⟩))
 (.branch 34
 (.leaf ⟨(26, 17090480766976), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record033_result⟩)
 (.leaf ⟨(26, 17120050348032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record034_result⟩))))
 (.branch 38
 (.branch 36
 (.leaf ⟨(26, 17120293847296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 17120305876992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record036_result⟩)
 (.leaf ⟨(26, 17120545214720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record037_result⟩)))
 (.branch 40
 (.branch 39
 (.leaf ⟨(26, 17146855883008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record038_result⟩)
 (.leaf ⟨(26, 17155450011648), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record039_result⟩))
 (.branch 41
 (.leaf ⟨(26, 17155986817024), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record040_result⟩)
 (.leaf ⟨(26, 17171317063680), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record041_result⟩)))))
 (.branch 49
 (.branch 45
 (.branch 43
 (.leaf ⟨(26, 17172085080064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record042_result⟩)
 (.branch 44
 (.leaf ⟨(26, 17179894548496), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record043_result⟩)
 (.leaf ⟨(26, 17184449954048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(26, 17184730386432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record045_result⟩)
 (.leaf ⟨(26, 17189021679617), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record046_result⟩))
 (.branch 48
 (.leaf ⟨(26, 17189023256576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record047_result⟩)
 (.leaf ⟨(26, 17189130473728), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record048_result⟩))))
 (.branch 52
 (.branch 50
 (.leaf ⟨(26, 17190147325952), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record049_result⟩)
 (.branch 51
 (.leaf ⟨(26, 17191278280704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record050_result⟩)
 (.leaf ⟨(26, 17198192034048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record051_result⟩)))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 17198328381440), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record052_result⟩)
 (.leaf ⟨(26, 17198336704512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 17198468825088), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record054_result⟩)
 (.leaf ⟨(26, 17198525448960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00026.record055_result⟩)))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15440 + i))) 0 56 :=
  interval_of_check _ 0 56 (by decide +kernel)

public theorem complete : Block 15440 15496 :=
  block_of_table results 15440 56 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0342

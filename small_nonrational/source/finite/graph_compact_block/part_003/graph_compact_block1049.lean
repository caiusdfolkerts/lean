module
prelude
import GraphInputsSix0Part00084Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1049
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 39
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 32332606357504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record000_result⟩)
 (.leaf ⟨(32, 32333118048320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 32335198292032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record002_result⟩)
 (.leaf ⟨(32, 32335214936640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 32438986277120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record004_result⟩)
 (.leaf ⟨(32, 32438994665472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 32439217488128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 32439386800384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record007_result⟩)
 (.leaf ⟨(32, 32439391027200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(32, 32439485890816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record009_result⟩)
 (.leaf ⟨(32, 32439497920512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record010_result⟩))
 (.branch 12
 (.leaf ⟨(32, 32441264832768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record011_result⟩)
 (.branch 13
 (.leaf ⟨(32, 32441273221120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record012_result⟩)
 (.leaf ⟨(32, 32441297862912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(32, 32441533235456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record014_result⟩)
 (.leaf ⟨(32, 32441537462272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record015_result⟩))
 (.branch 17
 (.leaf ⟨(32, 32441544744960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record016_result⟩)
 (.branch 18
 (.leaf ⟨(32, 32441566265600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record017_result⟩)
 (.leaf ⟨(32, 32441578295296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record018_result⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(32, 32441767567616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record019_result⟩)
 (.leaf ⟨(32, 32442841305344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record020_result⟩))
 (.branch 22
 (.leaf ⟨(32, 32454048514304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record021_result⟩)
 (.branch 23
 (.leaf ⟨(32, 32454060544000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record022_result⟩)
 (.leaf ⟨(32, 32454249816320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record023_result⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(32, 32454423355392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record024_result⟩)
 (.leaf ⟨(32, 32454456905728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record025_result⟩))
 (.branch 27
 (.leaf ⟨(32, 32455323554048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record026_result⟩)
 (.branch 28
 (.leaf ⟨(32, 32457873690656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record027_result⟩)
 (.leaf ⟨(32, 32473312461056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record028_result⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(32, 32474533527808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record029_result⟩)
 (.leaf ⟨(32, 32474541916160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record030_result⟩))
 (.branch 32
 (.leaf ⟨(32, 32474801930496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 32474806157312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record032_result⟩)
 (.leaf ⟨(32, 32474813960192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record033_result⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(32, 32475053297920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record034_result⟩)
 (.leaf ⟨(32, 32476126774016), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record035_result⟩))
 (.branch 37
 (.leaf ⟨(32, 32487535546624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record036_result⟩)
 (.branch 38
 (.leaf ⟨(32, 32487692570624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record037_result⟩)
 (.leaf ⟨(32, 32488609022720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record038_result⟩)))))))
 (.branch 58
 (.branch 48
 (.branch 43
 (.branch 41
 (.branch 40
 (.leaf ⟨(32, 32489315795200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record039_result⟩)
 (.leaf ⟨(32, 32492232901136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record040_result⟩))
 (.branch 42
 (.leaf ⟨(32, 32506745782528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record041_result⟩)
 (.leaf ⟨(32, 32507014185216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record042_result⟩)))
 (.branch 45
 (.branch 44
 (.leaf ⟨(32, 32507026214912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record043_result⟩)
 (.leaf ⟨(32, 32513456611584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record044_result⟩))
 (.branch 46
 (.leaf ⟨(32, 32513464999936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record045_result⟩)
 (.branch 47
 (.leaf ⟨(32, 32513465520128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record046_result⟩)
 (.leaf ⟨(32, 32513506676992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record047_result⟩)))))
 (.branch 53
 (.branch 50
 (.branch 49
 (.leaf ⟨(32, 32514521571328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record048_result⟩)
 (.leaf ⟨(32, 32514547712000), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record049_result⟩))
 (.branch 51
 (.leaf ⟨(32, 32514580153088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 32521828176128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record051_result⟩)
 (.leaf ⟨(32, 32522051260416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record052_result⟩))))
 (.branch 55
 (.branch 54
 (.leaf ⟨(32, 32522297937952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record053_result⟩)
 (.leaf ⟨(32, 32522901652224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record054_result⟩))
 (.branch 56
 (.leaf ⟨(32, 32523371414048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record055_result⟩)
 (.branch 57
 (.leaf ⟨(32, 32524445155856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record056_result⟩)
 (.leaf ⟨(32, 32531727515648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record057_result⟩))))))
 (.branch 68
 (.branch 63
 (.branch 60
 (.branch 59
 (.leaf ⟨(32, 32642843083008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record058_result⟩)
 (.leaf ⟨(32, 32642917531648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record059_result⟩))
 (.branch 61
 (.leaf ⟨(32, 32643379953664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record060_result⟩)
 (.branch 62
 (.leaf ⟨(32, 32643388276736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record061_result⟩)
 (.leaf ⟨(32, 32643429498880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record062_result⟩))))
 (.branch 65
 (.branch 64
 (.leaf ⟨(32, 32644972871936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record063_result⟩)
 (.leaf ⟨(32, 32658948628736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record064_result⟩))
 (.branch 66
 (.leaf ⟨(32, 32659032309760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 32659485499392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record066_result⟩)
 (.leaf ⟨(32, 32659486539776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record067_result⟩)))))
 (.branch 73
 (.branch 70
 (.branch 69
 (.leaf ⟨(32, 32659502014464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record068_result⟩)
 (.leaf ⟨(32, 32660005200128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record069_result⟩))
 (.branch 71
 (.leaf ⟨(32, 32660609040896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record070_result⟩)
 (.branch 72
 (.leaf ⟨(32, 32676128293120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record071_result⟩)
 (.leaf ⟨(32, 32676665163776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record072_result⟩))))
 (.branch 75
 (.branch 74
 (.leaf ⟨(32, 32676673486848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record073_result⟩)
 (.leaf ⟨(32, 32693291190528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record074_result⟩))
 (.branch 76
 (.leaf ⟨(32, 32693828061184), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 32693844705792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record076_result⟩)
 (.leaf ⟨(32, 32712769962240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00084.record077_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (34782 + i))) 0 78 :=
  interval_of_check _ 0 78 (by decide +kernel)

public theorem complete : Block 34782 34860 :=
  block_of_table results 34782 78 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1049

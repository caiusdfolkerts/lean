module
prelude
import GraphInputsSix0Part00055Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1020
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 35
 (.branch 17
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(32, 21123926392832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record000_result⟩)
 (.leaf ⟨(32, 21123934715904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record001_result⟩))
 (.branch 3
 (.leaf ⟨(32, 21124328996864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record002_result⟩)
 (.leaf ⟨(32, 21124395057152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(32, 21127515619328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record004_result⟩)
 (.leaf ⟨(32, 21172450234624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record005_result⟩))
 (.branch 7
 (.leaf ⟨(32, 21235546226944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record006_result⟩)
 (.leaf ⟨(32, 21235603867776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record007_result⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(32, 21238790490240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record008_result⟩)
 (.leaf ⟨(32, 21244385706240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record009_result⟩))
 (.branch 11
 (.leaf ⟨(32, 21256936259584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record010_result⟩)
 (.leaf ⟨(32, 21257068216960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record011_result⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(32, 21306663780608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record012_result⟩)
 (.leaf ⟨(32, 21306672168960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record013_result⟩))
 (.branch 15
 (.leaf ⟨(32, 21307066433600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record014_result⟩)
 (.branch 16
 (.leaf ⟨(32, 21308609954048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record015_result⟩)
 (.leaf ⟨(32, 21308614180864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record016_result⟩))))))
 (.branch 26
 (.branch 21
 (.branch 19
 (.branch 18
 (.leaf ⟨(32, 21308620423168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record017_result⟩)
 (.leaf ⟨(32, 21308744155392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record018_result⟩))
 (.branch 20
 (.leaf ⟨(32, 21308752543744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record019_result⟩)
 (.leaf ⟨(32, 21308810215680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 21309212868672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record021_result⟩)
 (.leaf ⟨(32, 21313307557952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 21313373618240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record023_result⟩)
 (.branch 25
 (.leaf ⟨(32, 21316594311232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record024_result⟩)
 (.leaf ⟨(32, 21329950556224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record025_result⟩)))))
 (.branch 30
 (.branch 28
 (.branch 27
 (.leaf ⟨(32, 21330084773888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record026_result⟩)
 (.leaf ⟨(32, 21333137178688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record027_result⟩))
 (.branch 29
 (.leaf ⟨(32, 21333205336064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record028_result⟩)
 (.leaf ⟨(32, 21333271396352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record029_result⟩)))
 (.branch 32
 (.branch 31
 (.leaf ⟨(32, 21333273477120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record030_result⟩)
 (.leaf ⟨(32, 21341845618944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record031_result⟩))
 (.branch 33
 (.leaf ⟨(32, 21341849845760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record032_result⟩)
 (.branch 34
 (.leaf ⟨(32, 21341856088064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record033_result⟩)
 (.leaf ⟨(32, 21341979820288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record034_result⟩)))))))
 (.branch 52
 (.branch 43
 (.branch 39
 (.branch 37
 (.branch 36
 (.leaf ⟨(32, 21341988208640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record035_result⟩)
 (.leaf ⟨(32, 21342095425792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record036_result⟩))
 (.branch 38
 (.leaf ⟨(32, 21342105634816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record037_result⟩)
 (.leaf ⟨(32, 21342498078784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record038_result⟩)))
 (.branch 41
 (.branch 40
 (.leaf ⟨(32, 21346543222848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record039_result⟩)
 (.leaf ⟨(32, 21346658828352), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record040_result⟩))
 (.branch 42
 (.leaf ⟨(32, 21350953517632), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record041_result⟩)
 (.leaf ⟨(32, 21367462445120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record042_result⟩))))
 (.branch 47
 (.branch 45
 (.branch 44
 (.leaf ⟨(32, 21367596662784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record043_result⟩)
 (.leaf ⟨(32, 21367598743552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record044_result⟩))
 (.branch 46
 (.leaf ⟨(32, 21374057873664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record045_result⟩)
 (.leaf ⟨(32, 21374062100480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record046_result⟩)))
 (.branch 49
 (.branch 48
 (.leaf ⟨(32, 21374068342784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record047_result⟩)
 (.leaf ⟨(32, 21374192075008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record048_result⟩))
 (.branch 50
 (.leaf ⟨(32, 21374200463360), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record049_result⟩)
 (.branch 51
 (.leaf ⟨(32, 21374307680512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record050_result⟩)
 (.leaf ⟨(32, 21374317889536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record051_result⟩))))))
 (.branch 61
 (.branch 56
 (.branch 54
 (.branch 53
 (.leaf ⟨(32, 21374710333504), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record052_result⟩)
 (.leaf ⟨(32, 21376208535552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record053_result⟩))
 (.branch 55
 (.leaf ⟨(32, 21376253853952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record054_result⟩)
 (.leaf ⟨(32, 21376266143744), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record055_result⟩)))
 (.branch 58
 (.branch 57
 (.leaf ⟨(32, 21376338510080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record056_result⟩)
 (.leaf ⟨(32, 21376340656128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record057_result⟩))
 (.branch 59
 (.leaf ⟨(32, 21376346898432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record058_result⟩)
 (.branch 60
 (.leaf ⟨(32, 21376388055296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record059_result⟩)
 (.leaf ⟨(32, 21376398264320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record060_result⟩)))))
 (.branch 65
 (.branch 63
 (.branch 62
 (.leaf ⟨(32, 21376857808960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record061_result⟩)
 (.leaf ⟨(32, 21378602369792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record062_result⟩))
 (.branch 64
 (.leaf ⟨(32, 21379005022784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_result⟩)
 (.leaf ⟨(32, 21380548804864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record064_result⟩)))
 (.branch 67
 (.branch 66
 (.leaf ⟨(32, 21380559013888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record065_result⟩)
 (.leaf ⟨(32, 21380901912640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record066_result⟩))
 (.branch 68
 (.leaf ⟨(32, 21380904009728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record067_result⟩)
 (.branch 69
 (.leaf ⟨(32, 21380951457856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record068_result⟩)
 (.leaf ⟨(32, 21381018558528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record069_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (32250 + i))) 0 70 :=
  interval_of_check _ 0 70 (by decide +kernel)

public theorem complete : Block 32250 32320 :=
  block_of_table results 32250 70 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1020

module
prelude
import GraphInputsSix0Part00047Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1012
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 18548487357056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 18557691789568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record001_result⟩)
 (.leaf ⟨(32, 18560911442176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 18577992220672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 18578091311104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record004_result⟩)
 (.leaf ⟨(32, 18590927454464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 18591447517312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 18593073889536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record007_result⟩)
 (.leaf ⟨(32, 18593470251264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 18593527892096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 18595467821312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record010_result⟩)
 (.leaf ⟨(32, 18595476209664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 18595868344576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 18595878813696), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record013_result⟩)
 (.leaf ⟨(32, 18599760691456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 18599769079808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 18600029094144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record016_result⟩)
 (.leaf ⟨(32, 18600039563264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 18600163295488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 18602309730560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record019_result⟩)
 (.leaf ⟨(32, 18606010140800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 18608354820096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record021_result⟩)
 (.leaf ⟨(32, 18615194632256), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 18616672092416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record023_result⟩)
 (.leaf ⟨(32, 18616940560384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 18616948883456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 18617343164416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record026_result⟩)
 (.leaf ⟨(32, 18617477365760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 18618752467200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 18618888814592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record029_result⟩)
 (.leaf ⟨(32, 18618897137664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 18619020935168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 18619029258240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record032_result⟩)
 (.leaf ⟨(32, 18619489599488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 18634053320960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 18634321723648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record035_result⟩)
 (.leaf ⟨(32, 18634332192768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 18729960292480), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 18732040667264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record038_result⟩)
 (.leaf ⟨(32, 18744522915968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 18766399357056), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 18766469627936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record041_result⟩)
 (.leaf ⟨(32, 18770762498080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 18778881605760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 18779083997216), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record044_result⟩)
 (.leaf ⟨(32, 18800760094976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 18801634640128), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record046_result⟩)
 (.leaf ⟨(32, 18801903042816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 18801903108096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record048_result⟩)
 (.leaf ⟨(32, 18802037244160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 18805927510272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 18806195912960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record051_result⟩)
 (.leaf ⟨(32, 18806195978240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 18806197993728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 18814513250560), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record054_result⟩)
 (.leaf ⟨(32, 18814517412096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 18814517477376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 18814519492864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record057_result⟩)
 (.leaf ⟨(32, 18814922145856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 18817069621312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 18817394835712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record060_result⟩)
 (.leaf ⟨(32, 18817394900992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 18817531052288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 18817939963904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record063_result⟩)
 (.leaf ⟨(32, 18839414849600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 18839481958432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 18847803457568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record066_result⟩)
 (.leaf ⟨(32, 18848000589888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 18874915373312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 18874915438592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record069_result⟩)
 (.leaf ⟨(32, 18881236254784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 18883236872448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record071_result⟩)
 (.leaf ⟨(32, 18883236937728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 18883507404864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record073_result⟩)
 (.leaf ⟨(32, 18885654880320), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 18939069399296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 18939333640448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record076_result⟩)
 (.leaf ⟨(32, 18939342028800), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 18939465761024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 18943626510592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record079_result⟩)
 (.leaf ⟨(32, 18943634898944), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 18947390898432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 18947927769088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record082_result⟩)
 (.leaf ⟨(32, 18951948009728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 18951956398080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 18952216412416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record085_result⟩)
 (.leaf ⟨(32, 18952226881536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 18952350613760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 18954497048832), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record088_result⟩)
 (.leaf ⟨(32, 18955976638720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 18956249268224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 18956513509376), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record091_result⟩)
 (.leaf ⟨(32, 18956521832448), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 18956645629952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 18956786073600), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record094_result⟩)
 (.leaf ⟨(32, 18960269508864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 18960806379520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record096_result⟩)
 (.leaf ⟨(32, 18960814702592), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 18962349883648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record098_result⟩)
 (.leaf ⟨(32, 18962490392576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00047.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31450 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31450 31550 :=
  block_of_table results 31450 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1012

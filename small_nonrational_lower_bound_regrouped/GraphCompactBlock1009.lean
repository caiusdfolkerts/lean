module
prelude
import GraphInputsSix0Part00044Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1009
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 17489125736704), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 17493422833664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record001_result⟩)
 (.leaf ⟨(32, 17493695397888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 17494207365120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 17498368114688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record004_result⟩)
 (.leaf ⟨(32, 17501991927808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 17519171731456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 17523483640064), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record007_result⟩)
 (.leaf ⟨(32, 17523752108032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 17523760431104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 17524272138240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record010_result⟩)
 (.leaf ⟨(32, 17532056635648), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 17532593506304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 17532610150912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record013_result⟩)
 (.leaf ⟨(32, 17549236371972), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 17557847343104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 17566441406464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record016_result⟩)
 (.leaf ⟨(32, 17566969888768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 17583596240896), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 17583612887040), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record019_result⟩)
 (.leaf ⟨(32, 17630180245888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 17632128500096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record021_result⟩)
 (.leaf ⟨(32, 17632260620672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 17636555571584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record023_result⟩)
 (.leaf ⟨(32, 17636819812736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 17701984764288), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 17702123045120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record026_result⟩)
 (.leaf ⟨(32, 17702322274432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 17702525698112), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 17702995394816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record029_result⟩)
 (.leaf ⟨(32, 17702995460096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 17703123353856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 17703127515392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record032_result⟩)
 (.leaf ⟨(32, 17703127580672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 17703255474432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 17703263862784), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record035_result⟩)
 (.leaf ⟨(32, 17704149926272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 17704414167424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 17706415915264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record038_result⟩)
 (.leaf ⟨(32, 17706617225344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 17706686447680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 17707288264960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record041_result⟩)
 (.leaf ⟨(32, 17708833931296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 17710408827136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 17710507917568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record044_result⟩)
 (.leaf ⟨(32, 17715001655552), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 17722313310464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record046_result⟩)
 (.leaf ⟨(32, 17723353497856), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 17739633738048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record048_result⟩)
 (.leaf ⟨(32, 17748219478336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 17748220518720), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 17775135375616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record051_result⟩)
 (.leaf ⟨(32, 17775403827264), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 17777551310880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 17783721115904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record054_result⟩)
 (.leaf ⟨(32, 17783725326400), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 17786737819904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 17787778007296), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record057_result⟩)
 (.leaf ⟨(32, 17839761162496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 17856395903232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 17856395968512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record060_result⟩)
 (.leaf ⟨(32, 17856532119808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 17856941031424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 17857068990464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record063_result⟩)
 (.leaf ⟨(32, 17857077313536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 17921160036608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 17972446937344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record066_result⟩)
 (.leaf ⟨(32, 17976799559936), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 17976931680512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 17977200115840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record069_result⟩)
 (.leaf ⟨(32, 17993971040512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 17993979428864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record071_result⟩)
 (.leaf ⟨(32, 17994103161088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 17994107387904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record073_result⟩)
 (.leaf ⟨(32, 17994111549440), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 17994371596416), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 17994507911168), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record076_result⟩)
 (.leaf ⟨(32, 17994571858048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 17998272299008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 18045516939520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record079_result⟩)
 (.leaf ⟨(32, 18145336181120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 18178602795392), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 18180204494976), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record082_result⟩)
 (.leaf ⟨(32, 18180890714496), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 18181947285888), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 18182284869760), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record085_result⟩)
 (.leaf ⟨(32, 18186579820672), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 18194767118464), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 18194901319808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record088_result⟩)
 (.leaf ⟨(32, 18194967380096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 18216378269952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 18216848031776), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record091_result⟩)
 (.leaf ⟨(32, 18220671140096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 18220935381248), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 18220941672512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record094_result⟩)
 (.leaf ⟨(32, 18221008781344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 18246185091328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record096_result⟩)
 (.leaf ⟨(32, 18246383272192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 18246385352960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record098_result⟩)
 (.leaf ⟨(32, 18246440943624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00044.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (31150 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 31150 31250 :=
  block_of_table results 31150 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock1009

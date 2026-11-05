module
prelude
import GraphInputsRow19Part00009Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0049
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 49
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 15264424921344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 15264490981632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record001_result⟩)
 (.leaf ⟨(19, 15264524011776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 15264869072896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 15264870048000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record004_result⟩)
 (.leaf ⟨(19, 15264870113280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 15264870633472), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 15264877908000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record007_result⟩)
 (.leaf ⟨(19, 15264894683168), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 15269162918144), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 15274587717633), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record010_result⟩)
 (.leaf ⟨(19, 15277484417280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 15278021287936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 15278022328320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record013_result⟩)
 (.leaf ⟨(19, 15285822300416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 15285823406080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 15285830688768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record016_result⟩)
 (.leaf ⟨(19, 15285831599104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 15286325612576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 15286327051264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record019_result⟩)
 (.leaf ⟨(19, 15286359032352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(19, 15290239090944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record021_result⟩)
 (.branch 23
 (.leaf ⟨(19, 15290643515648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record022_result⟩)
 (.leaf ⟨(19, 15290645921792), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(19, 15292786835712), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record024_result⟩)
 (.branch 26
 (.leaf ⟨(19, 15293443277056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record025_result⟩)
 (.leaf ⟨(19, 15294655498496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(19, 15294655563776), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 15307806606344), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record028_result⟩)
 (.leaf ⟨(19, 15310623145984), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(19, 15310895710208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 15320148477184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record031_result⟩)
 (.leaf ⟨(19, 15320156865536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(19, 15320685216260), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 15324535947264), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record034_result⟩)
 (.leaf ⟨(19, 15324737249280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(19, 15324737964288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record036_result⟩)
 (.branch 38
 (.leaf ⟨(19, 15325005651968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record037_result⟩)
 (.leaf ⟨(19, 15325009545248), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(19, 15326867753216), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 15326867818496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record040_result⟩)
 (.leaf ⟨(19, 15327140250632), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(19, 15327157026817), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 15333596332033), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record043_result⟩)
 (.leaf ⟨(19, 15341900138528), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record044_result⟩)))
 (.branch 47
 (.branch 46
 (.leaf ⟨(19, 15437778731008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record045_result⟩)
 (.leaf ⟨(19, 15510548840448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record046_result⟩))
 (.branch 48
 (.leaf ⟨(19, 15523427450880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record047_result⟩)
 (.leaf ⟨(19, 15543261216768), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record048_result⟩)))))))
 (.branch 73
 (.branch 61
 (.branch 55
 (.branch 52
 (.branch 50
 (.leaf ⟨(19, 15570676318208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record049_result⟩)
 (.branch 51
 (.leaf ⟨(19, 15579134099456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record050_result⟩)
 (.leaf ⟨(19, 15579603804160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record051_result⟩)))
 (.branch 53
 (.leaf ⟨(19, 15579670904832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record052_result⟩)
 (.branch 54
 (.leaf ⟨(19, 15579860762624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record053_result⟩)
 (.leaf ⟨(19, 15579869085696), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record054_result⟩))))
 (.branch 58
 (.branch 56
 (.leaf ⟨(19, 15590786875648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record055_result⟩)
 (.branch 57
 (.leaf ⟨(19, 15595338735616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record056_result⟩)
 (.leaf ⟨(19, 15602888572928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record057_result⟩)))
 (.branch 59
 (.leaf ⟨(19, 15614153392128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record058_result⟩)
 (.branch 60
 (.leaf ⟨(19, 15614161715200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record059_result⟩)
 (.leaf ⟨(19, 15614466916352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record060_result⟩)))))
 (.branch 67
 (.branch 64
 (.branch 62
 (.leaf ⟨(19, 15614936621056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record061_result⟩)
 (.branch 63
 (.leaf ⟨(19, 15626371399680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record062_result⟩)
 (.leaf ⟨(19, 15626510802944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record063_result⟩)))
 (.branch 65
 (.leaf ⟨(19, 15626635640832), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record064_result⟩)
 (.branch 66
 (.leaf ⟨(19, 15626643963904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record065_result⟩)
 (.leaf ⟨(19, 15627345526784), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record066_result⟩))))
 (.branch 70
 (.branch 68
 (.leaf ⟨(19, 15627411587072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record067_result⟩)
 (.branch 69
 (.leaf ⟨(19, 15627543707648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record068_result⟩)
 (.leaf ⟨(19, 15627550990336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record069_result⟩)))
 (.branch 71
 (.leaf ⟨(19, 15629491961856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record070_result⟩)
 (.branch 72
 (.leaf ⟨(19, 15629722067200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record071_result⟩)
 (.leaf ⟨(19, 15636243679488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record072_result⟩))))))
 (.branch 85
 (.branch 79
 (.branch 76
 (.branch 74
 (.leaf ⟨(19, 15638324054272), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record073_result⟩)
 (.branch 75
 (.leaf ⟨(19, 15649262797824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record074_result⟩)
 (.leaf ⟨(19, 15649518650112), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record075_result⟩)))
 (.branch 77
 (.leaf ⟨(19, 15661736853504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record076_result⟩)
 (.branch 78
 (.leaf ⟨(19, 15661877167104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record077_result⟩)
 (.leaf ⟨(19, 15662000898816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record078_result⟩))))
 (.branch 82
 (.branch 80
 (.leaf ⟨(19, 15663817228288), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record079_result⟩)
 (.branch 81
 (.leaf ⟨(19, 15664023602176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record080_result⟩)
 (.leaf ⟨(19, 15664081273600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record081_result⟩)))
 (.branch 83
 (.leaf ⟨(19, 15678326718592), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record082_result⟩)
 (.branch 84
 (.leaf ⟨(19, 15820619055104), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record083_result⟩)
 (.leaf ⟨(19, 15820685115392), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record084_result⟩)))))
 (.branch 91
 (.branch 88
 (.branch 86
 (.leaf ⟨(19, 15820817235968), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record085_result⟩)
 (.branch 87
 (.leaf ⟨(19, 15820824518656), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record086_result⟩)
 (.leaf ⟨(19, 15842395818240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record087_result⟩)))
 (.branch 89
 (.leaf ⟨(19, 15844476193024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record088_result⟩)
 (.branch 90
 (.leaf ⟨(19, 15876688447744), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record089_result⟩)
 (.leaf ⟨(19, 15878834882816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record090_result⟩))))
 (.branch 94
 (.branch 92
 (.leaf ⟨(19, 16094899216384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record091_result⟩)
 (.branch 93
 (.leaf ⟨(19, 16095156174848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record092_result⟩)
 (.leaf ⟨(19, 16095164497920), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record093_result⟩)))
 (.branch 96
 (.branch 95
 (.leaf ⟨(19, 16107513585664), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record094_result⟩)
 (.leaf ⟨(19, 16127212126208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record095_result⟩))
 (.branch 97
 (.leaf ⟨(19, 16143037825024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record096_result⟩)
 (.leaf ⟨(19, 16174902476800), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00009.record097_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (2998 + i))) 0 98 :=
  interval_of_check _ 0 98 (by decide +kernel)

public theorem complete : Block 2998 3096 :=
  block_of_table results 2998 98 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0049

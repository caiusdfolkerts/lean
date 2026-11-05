module
prelude
import GraphInputsRow26Part00021Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0337
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 38
 (.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(26, 12723182174208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record000_result⟩)
 (.leaf ⟨(26, 12781982416912), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record001_result⟩))
 (.branch 3
 (.leaf ⟨(26, 12782116618256), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record002_result⟩)
 (.leaf ⟨(26, 12786411307536), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record003_result⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(26, 12898600484864), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record004_result⟩)
 (.leaf ⟨(26, 12919417176080), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record005_result⟩))
 (.branch 7
 (.leaf ⟨(26, 12919551377424), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record006_result⟩)
 (.branch 8
 (.leaf ⟨(26, 12919555538960), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record007_result⟩)
 (.leaf ⟨(26, 12927990171664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record008_result⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(26, 13104356261888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record009_result⟩)
 (.leaf ⟨(26, 13125441226752), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record010_result⟩))
 (.branch 12
 (.leaf ⟨(26, 13125697013768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record011_result⟩)
 (.branch 13
 (.leaf ⟨(26, 13125697143816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record012_result⟩)
 (.leaf ⟨(26, 13125709791232), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record013_result⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(26, 13125713920001), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record014_result⟩)
 (.leaf ⟨(26, 13125961384968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record015_result⟩))
 (.branch 17
 (.leaf ⟨(26, 13134278560000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record016_result⟩)
 (.branch 18
 (.leaf ⟨(26, 13134412972032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record017_result⟩)
 (.leaf ⟨(26, 13136568516608), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record018_result⟩))))))
 (.branch 28
 (.branch 23
 (.branch 21
 (.branch 20
 (.leaf ⟨(26, 13197940670848), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record019_result⟩)
 (.leaf ⟨(26, 13199852773760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record020_result⟩))
 (.branch 22
 (.leaf ⟨(26, 13237265703296), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record021_result⟩)
 (.leaf ⟨(26, 13240954322944), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record022_result⟩)))
 (.branch 25
 (.branch 24
 (.leaf ⟨(26, 13308371468544), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record023_result⟩)
 (.leaf ⟨(26, 13340378468640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record024_result⟩))
 (.branch 26
 (.leaf ⟨(26, 13377357316096), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record025_result⟩)
 (.branch 27
 (.leaf ⟨(26, 13384805269632), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record026_result⟩)
 (.leaf ⟨(26, 13386412721408), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record027_result⟩)))))
 (.branch 33
 (.branch 30
 (.branch 29
 (.leaf ⟨(26, 13516677325056), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record028_result⟩)
 (.leaf ⟨(26, 13524384383104), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record029_result⟩))
 (.branch 31
 (.leaf ⟨(26, 13524652818432), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record030_result⟩)
 (.branch 32
 (.leaf ⟨(26, 13524656979968), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record031_result⟩)
 (.leaf ⟨(26, 13610291052672), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record032_result⟩))))
 (.branch 35
 (.branch 34
 (.leaf ⟨(26, 13651891257600), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record033_result⟩)
 (.leaf ⟨(26, 13669071126528), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record034_result⟩))
 (.branch 36
 (.leaf ⟨(26, 13669607931904), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record035_result⟩)
 (.branch 37
 (.leaf ⟨(26, 13890486894624), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record036_result⟩)
 (.leaf ⟨(26, 13899934040064), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record037_result⟩)))))))
 (.branch 57
 (.branch 47
 (.branch 42
 (.branch 40
 (.branch 39
 (.leaf ⟨(26, 13900003156224), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record038_result⟩)
 (.leaf ⟨(26, 13929385361664), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record039_result⟩))
 (.branch 41
 (.leaf ⟨(26, 13935436693504), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record040_result⟩)
 (.leaf ⟨(26, 13937975263488), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record041_result⟩)))
 (.branch 44
 (.branch 43
 (.leaf ⟨(26, 13937986772992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record042_result⟩)
 (.leaf ⟨(26, 13976629944576), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record043_result⟩))
 (.branch 45
 (.leaf ⟨(26, 14004550434816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record044_result⟩)
 (.branch 46
 (.leaf ⟨(26, 14004558757888), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record045_result⟩)
 (.leaf ⟨(26, 14010254688512), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record046_result⟩)))))
 (.branch 52
 (.branch 49
 (.branch 48
 (.leaf ⟨(26, 14010989740032), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record047_result⟩)
 (.leaf ⟨(26, 14012607692800), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record048_result⟩))
 (.branch 50
 (.leaf ⟨(26, 14013144498176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record049_result⟩)
 (.branch 51
 (.leaf ⟨(26, 14201720471552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record050_result⟩)
 (.leaf ⟨(26, 14201984712704), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record051_result⟩))))
 (.branch 54
 (.branch 53
 (.leaf ⟨(26, 14201993035776), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record052_result⟩)
 (.leaf ⟨(26, 14203528216832), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record053_result⟩))
 (.branch 55
 (.leaf ⟨(26, 14204263268352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record054_result⟩)
 (.branch 56
 (.leaf ⟨(26, 14220708085760), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record055_result⟩)
 (.leaf ⟨(26, 14220980649984), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record056_result⟩))))))
 (.branch 66
 (.branch 61
 (.branch 59
 (.branch 58
 (.leaf ⟨(26, 14221443072000), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record057_result⟩)
 (.leaf ⟨(26, 14235740471552), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record058_result⟩))
 (.branch 60
 (.leaf ⟨(26, 14236277342208), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record059_result⟩)
 (.leaf ⟨(26, 14236285665280), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record060_result⟩)))
 (.branch 63
 (.branch 62
 (.leaf ⟨(26, 14236475523072), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record061_result⟩)
 (.leaf ⟨(26, 14250769678592), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record062_result⟩))
 (.branch 64
 (.leaf ⟨(26, 14451034034240), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record063_result⟩)
 (.branch 65
 (.leaf ⟨(26, 14453248626720), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record064_result⟩)
 (.leaf ⟨(26, 14484320043008), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record065_result⟩)))))
 (.branch 71
 (.branch 68
 (.branch 67
 (.leaf ⟨(26, 14486534619136), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record066_result⟩)
 (.leaf ⟨(26, 14486658416640), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record067_result⟩))
 (.branch 69
 (.leaf ⟨(26, 14492899540992), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record068_result⟩)
 (.branch 70
 (.leaf ⟨(26, 14554180354048), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record069_result⟩)
 (.leaf ⟨(26, 14558605344768), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record070_result⟩))))
 (.branch 73
 (.branch 72
 (.leaf ⟨(26, 14564846469120), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record071_result⟩)
 (.leaf ⟨(26, 14589032956160), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record072_result⟩))
 (.branch 74
 (.leaf ⟨(26, 14589569826816), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record073_result⟩)
 (.branch 75
 (.leaf ⟨(26, 14589573988352), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record074_result⟩)
 (.leaf ⟨(26, 14602940498176), Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00021.record075_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (15150 + i))) 0 76 :=
  interval_of_check _ 0 76 (by decide +kernel)

public theorem complete : Block 15150 15226 :=
  block_of_table results 15150 76 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0337

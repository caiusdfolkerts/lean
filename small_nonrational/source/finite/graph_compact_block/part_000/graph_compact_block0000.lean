module
prelude
import GraphInputsRow16Part00000Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0000
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(16, 402458247168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record000_result⟩)
 (.branch 2
 (.leaf ⟨(16, 402466570240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record001_result⟩)
 (.leaf ⟨(16, 406817177600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(16, 680565735424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record003_result⟩)
 (.branch 5
 (.leaf ⟨(16, 742909870080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record004_result⟩)
 (.leaf ⟨(16, 744990244864), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(16, 777198338048), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record006_result⟩)
 (.branch 8
 (.leaf ⟨(16, 882429165568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record007_result⟩)
 (.leaf ⟨(16, 1025295581184), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(16, 1432050761728), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record009_result⟩)
 (.branch 11
 (.leaf ⟨(16, 1470702321664), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record010_result⟩)
 (.leaf ⟨(16, 1502034854400), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(16, 1505799274496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record012_result⟩)
 (.branch 14
 (.leaf ⟨(16, 1506327691520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record013_result⟩)
 (.leaf ⟨(16, 1506331918336), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(16, 1506338160640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record015_result⟩)
 (.branch 17
 (.leaf ⟨(16, 1506340241408), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record016_result⟩)
 (.leaf ⟨(16, 1507747463424), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(16, 1507879649280), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record018_result⟩)
 (.branch 20
 (.leaf ⟨(16, 1508143890432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record019_result⟩)
 (.leaf ⟨(16, 1508351418432), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(16, 1575055540224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record021_result⟩)
 (.leaf ⟨(16, 1576464908288), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record022_result⟩))
 (.branch 24
 (.leaf ⟨(16, 1576863350784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record023_result⟩)
 (.leaf ⟨(16, 1577193586944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(16, 1577195732992), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record025_result⟩)
 (.branch 27
 (.leaf ⟨(16, 1577201975296), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record026_result⟩)
 (.leaf ⟨(16, 1874314985472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(16, 1878859513856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record028_result⟩)
 (.branch 30
 (.leaf ⟨(16, 1882883981312), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record029_result⟩)
 (.leaf ⟨(16, 1883152384000), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(16, 2020318740480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record031_result⟩)
 (.branch 33
 (.leaf ⟨(16, 2020587143168), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record032_result⟩)
 (.leaf ⟨(16, 2020593385472), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(16, 2020595466240), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record034_result⟩)
 (.branch 36
 (.leaf ⟨(16, 2053831131136), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record035_result⟩)
 (.leaf ⟨(16, 2057566388224), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(16, 2057704636416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record037_result⟩)
 (.branch 39
 (.leaf ⟨(16, 2058096771328), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record038_result⟩)
 (.leaf ⟨(16, 2058233118720), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(16, 2058241441792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record040_result⟩)
 (.branch 42
 (.leaf ⟨(16, 2089376825344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record041_result⟩)
 (.leaf ⟨(16, 2091826315520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(16, 2091826380800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record043_result⟩)
 (.branch 45
 (.leaf ⟨(16, 2091960582144), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record044_result⟩)
 (.leaf ⟨(16, 2092228984832), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(16, 2126151647232), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record046_result⟩)
 (.leaf ⟨(16, 2126285848576), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record047_result⟩))
 (.branch 49
 (.leaf ⟨(16, 2126956724736), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record048_result⟩)
 (.leaf ⟨(16, 2150044368896), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(16, 2160974659840), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record050_result⟩)
 (.branch 52
 (.leaf ⟨(16, 2394313293824), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record051_result⟩)
 (.leaf ⟨(16, 2455257579520), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(16, 2468404592640), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record053_result⟩)
 (.branch 55
 (.leaf ⟨(16, 2469954339072), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record054_result⟩)
 (.leaf ⟨(16, 2710465167616), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(16, 3260222078976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record056_result⟩)
 (.branch 58
 (.leaf ⟨(16, 3459230302208), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record057_result⟩)
 (.leaf ⟨(16, 3527455899648), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(16, 3531748769792), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record059_result⟩)
 (.branch 61
 (.leaf ⟨(16, 3532479594496), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record060_result⟩)
 (.leaf ⟨(16, 3532485836800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(16, 3535341101120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record062_result⟩)
 (.branch 64
 (.leaf ⟨(16, 3738637975552), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record063_result⟩)
 (.leaf ⟨(16, 3741089611776), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(16, 3786426843392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record065_result⟩)
 (.branch 67
 (.leaf ⟨(16, 3809774608384), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record066_result⟩)
 (.leaf ⟨(16, 3809907574016), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(16, 3809912954944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record068_result⟩)
 (.branch 70
 (.leaf ⟨(16, 3809912971264), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record069_result⟩)
 (.leaf ⟨(16, 3964938518784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(16, 3964938584064), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record071_result⟩)
 (.leaf ⟨(16, 4102377504768), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record072_result⟩))
 (.branch 74
 (.leaf ⟨(16, 4111091138816), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record073_result⟩)
 (.leaf ⟨(16, 4119012114688), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(16, 4119548985344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record075_result⟩)
 (.branch 77
 (.leaf ⟨(16, 4119557308416), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record076_result⟩)
 (.leaf ⟨(16, 4119821549568), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(16, 4239548022784), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record078_result⟩)
 (.branch 80
 (.leaf ⟨(16, 4336176398592), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record079_result⟩)
 (.leaf ⟨(16, 4336184786944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(16, 4336576921856), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record081_result⟩)
 (.branch 83
 (.leaf ⟨(16, 4359461044480), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record082_result⟩)
 (.leaf ⟨(16, 4359530414080), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(16, 4359597391872), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record084_result⟩)
 (.branch 86
 (.leaf ⟨(16, 4359605714944), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record085_result⟩)
 (.leaf ⟨(16, 4376710152448), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(16, 4377247023104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record087_result⟩)
 (.branch 89
 (.leaf ⟨(16, 4377255346176), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record088_result⟩)
 (.leaf ⟨(16, 4393890021376), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(16, 4394162585600), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record090_result⟩)
 (.branch 92
 (.leaf ⟨(16, 4804799692800), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record091_result⟩)
 (.leaf ⟨(16, 4804805935104), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(16, 4872852307968), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record093_result⟩)
 (.branch 95
 (.leaf ⟨(16, 4872986444032), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record094_result⟩)
 (.leaf ⟨(16, 4873250750464), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(16, 4873324077120), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record096_result⟩)
 (.leaf ⟨(16, 4873589374976), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record097_result⟩))
 (.branch 99
 (.leaf ⟨(16, 5106290491392), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record098_result⟩)
 (.leaf ⟨(16, 5140685881344), Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00000.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (0 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 0 100 :=
  block_of_table results 0 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0000

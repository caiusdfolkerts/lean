module
prelude
import GraphInputsRow27Part00008Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0411
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(27, 18616948883456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record000_result⟩)
 (.branch 2
 (.leaf ⟨(27, 18617477365760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record001_result⟩)
 (.leaf ⟨(27, 18618897137664), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(27, 18619020935168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record003_result⟩)
 (.branch 5
 (.leaf ⟨(27, 18619029258240), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record004_result⟩)
 (.leaf ⟨(27, 18817394900992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(27, 18956521832448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record006_result⟩)
 (.branch 8
 (.leaf ⟨(27, 18956786073600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record007_result⟩)
 (.leaf ⟨(27, 18960814702592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(27, 18962895077376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record009_result⟩)
 (.branch 11
 (.leaf ⟨(27, 19059028557824), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record010_result⟩)
 (.leaf ⟨(27, 19097985220608), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(27, 19098513702912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record012_result⟩)
 (.branch 14
 (.leaf ⟨(27, 19099933474816), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record013_result⟩)
 (.leaf ⟨(27, 19100065595392), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(27, 19100329836544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record015_result⟩)
 (.branch 17
 (.leaf ⟨(27, 19168508264704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record016_result⟩)
 (.leaf ⟨(27, 19168642531328), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(27, 19168650854400), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record018_result⟩)
 (.branch 20
 (.leaf ⟨(27, 19169111195648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record019_result⟩)
 (.leaf ⟨(27, 19281865703424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(27, 19286158573568), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record021_result⟩)
 (.leaf ⟨(27, 19294480072704), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record022_result⟩))
 (.branch 24
 (.leaf ⟨(27, 19298105954368), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record023_result⟩)
 (.leaf ⟨(27, 19471041298432), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(27, 19475069927424), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record025_result⟩)
 (.branch 27
 (.leaf ⟨(27, 19512581816320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record026_result⟩)
 (.leaf ⟨(27, 19538991153152), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(27, 19586194046984), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record028_result⟩)
 (.branch 30
 (.leaf ⟨(27, 19588687396864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record029_result⟩)
 (.leaf ⟨(27, 19589090000896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(27, 19602341890176), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record031_result⟩)
 (.branch 33
 (.leaf ⟨(27, 19612108324864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record032_result⟩)
 (.leaf ⟨(27, 19612240445440), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(27, 19612504686592), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record034_result⟩)
 (.branch 36
 (.leaf ⟨(27, 19612700786688), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record035_result⟩)
 (.leaf ⟨(27, 19612768927744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(27, 19646004592640), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record037_result⟩)
 (.branch 39
 (.leaf ⟨(27, 19649752334336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record038_result⟩)
 (.leaf ⟨(27, 19657404776448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(27, 19657675259904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record040_result⟩)
 (.branch 42
 (.leaf ⟨(27, 19680825704448), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record041_result⟩)
 (.leaf ⟨(27, 19683937943552), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(27, 19683946266624), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record043_result⟩)
 (.branch 45
 (.leaf ⟨(27, 19684012326912), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record044_result⟩)
 (.leaf ⟨(27, 19684045357056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(27, 19693108725760), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record046_result⟩)
 (.leaf ⟨(27, 19697401595904), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record047_result⟩))
 (.branch 49
 (.leaf ⟨(27, 19705723095040), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record048_result⟩)
 (.leaf ⟨(27, 19710410228288), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(27, 19718195003648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record050_result⟩)
 (.branch 52
 (.leaf ⟨(27, 19718329270272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record051_result⟩)
 (.leaf ⟨(27, 19718337593344), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(27, 19718731874304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record053_result⟩)
 (.branch 55
 (.leaf ⟨(27, 19718865945088), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record054_result⟩)
 (.leaf ⟨(27, 19724800950272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(27, 19724933070848), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record056_result⟩)
 (.branch 58
 (.leaf ⟨(27, 19725197312000), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record057_result⟩)
 (.leaf ⟨(27, 19725203554304), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(27, 19725320980480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record059_result⟩)
 (.branch 61
 (.leaf ⟨(27, 19725442892032), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record060_result⟩)
 (.leaf ⟨(27, 19731694225408), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(27, 19740015724544), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record062_result⟩)
 (.branch 64
 (.leaf ⟨(27, 19917051035648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record063_result⟩)
 (.leaf ⟨(27, 19921343905792), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(27, 20047443525632), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record065_result⟩)
 (.branch 67
 (.leaf ⟨(27, 20130682667008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record066_result⟩)
 (.leaf ⟨(27, 20149950251008), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(27, 20158535991296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record068_result⟩)
 (.branch 70
 (.leaf ⟨(27, 20161854734336), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record069_result⟩)
 (.leaf ⟨(27, 20162894921728), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(27, 20193063470080), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record071_result⟩)
 (.leaf ⟨(27, 20199300562944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record072_result⟩))
 (.branch 74
 (.leaf ⟨(27, 20199432520320), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record073_result⟩)
 (.leaf ⟨(27, 20227319431168), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(27, 20274604935296), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record075_result⟩)
 (.branch 77
 (.leaf ⟨(27, 20289629980800), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record076_result⟩)
 (.leaf ⟨(27, 20561962991616), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(27, 20685726515200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record078_result⟩)
 (.branch 80
 (.leaf ⟨(27, 20685732724864), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record079_result⟩)
 (.leaf ⟨(27, 20685927817216), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(27, 20686195179520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record081_result⟩)
 (.branch 83
 (.leaf ⟨(27, 20693707702272), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record082_result⟩)
 (.leaf ⟨(27, 20701849323648), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(27, 20710385811456), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record084_result⟩)
 (.branch 86
 (.leaf ⟨(27, 20710435356672), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record085_result⟩)
 (.leaf ⟨(27, 20711475412992), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(27, 20719077785600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record087_result⟩)
 (.branch 89
 (.leaf ⟨(27, 20719211986944), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record088_result⟩)
 (.leaf ⟨(27, 20719216148480), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(27, 20719337474056), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record090_result⟩)
 (.branch 92
 (.leaf ⟨(27, 20723498222600), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record091_result⟩)
 (.leaf ⟨(27, 20723514998785), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(27, 20727791092744), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record093_result⟩)
 (.branch 95
 (.leaf ⟨(27, 20728055333896), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record094_result⟩)
 (.leaf ⟨(27, 20748987139200), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(27, 20748991333376), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record096_result⟩)
 (.leaf ⟨(27, 20749255442948), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record097_result⟩))
 (.branch 99
 (.leaf ⟨(27, 20756912209920), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record098_result⟩)
 (.leaf ⟨(27, 20770632763520), Papers.RationalityTen.CompactReplay.GraphInputsRow27Part00008.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (18473 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 18473 18573 :=
  block_of_table results 18473 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0411

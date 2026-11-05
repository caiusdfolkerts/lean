module
prelude
import GraphInputsRow19Part00024Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0064
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 48
 (.branch 24
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(19, 25261143752704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record000_result⟩)
 (.branch 2
 (.leaf ⟨(19, 25261655458304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record001_result⟩)
 (.leaf ⟨(19, 25261655719936), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(19, 25303305429056), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record003_result⟩)
 (.branch 5
 (.leaf ⟨(19, 25311626928192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record004_result⟩)
 (.leaf ⟨(19, 25315787677760), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(19, 25367713161280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record006_result⟩)
 (.branch 8
 (.leaf ⟨(19, 25367741005824), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record007_result⟩)
 (.leaf ⟨(19, 25367747248128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(19, 25376034660416), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record009_result⟩)
 (.branch 11
 (.leaf ⟨(19, 25383315972160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record010_result⟩)
 (.leaf ⟨(19, 25400038195200), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(19, 25414600818688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record012_result⟩)
 (.branch 14
 (.leaf ⟨(19, 25415641006080), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record013_result⟩)
 (.leaf ⟨(19, 25444520828992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(19, 25444619919424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record015_result⟩)
 (.branch 17
 (.leaf ⟨(19, 25445048270912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record016_result⟩)
 (.leaf ⟨(19, 25445050368000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(19, 25447740481600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record018_result⟩)
 (.branch 20
 (.leaf ⟨(19, 25448797052992), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record019_result⟩)
 (.leaf ⟨(19, 25573468938304), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record020_result⟩)))
 (.branch 22
 (.leaf ⟨(19, 25577646071872), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record021_result⟩)
 (.branch 23
 (.leaf ⟨(19, 25589468110912), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record022_result⟩)
 (.leaf ⟨(19, 25633592738048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record023_result⟩))))))
 (.branch 36
 (.branch 30
 (.branch 27
 (.branch 25
 (.leaf ⟨(19, 25639009157376), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record024_result⟩)
 (.branch 26
 (.leaf ⟨(19, 25658152067136), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record025_result⟩)
 (.leaf ⟨(19, 25659209565184), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record026_result⟩)))
 (.branch 28
 (.leaf ⟨(19, 25844069204224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record027_result⟩)
 (.branch 29
 (.leaf ⟨(19, 25877354414336), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record028_result⟩)
 (.leaf ⟨(19, 25878423732480), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record029_result⟩))))
 (.branch 33
 (.branch 31
 (.leaf ⟨(19, 25878923346176), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record030_result⟩)
 (.branch 32
 (.leaf ⟨(19, 25895603601408), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record031_result⟩)
 (.leaf ⟨(19, 25915333607424), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record032_result⟩)))
 (.branch 34
 (.leaf ⟨(19, 25915341930496), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record033_result⟩)
 (.branch 35
 (.leaf ⟨(19, 25927815856128), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record034_result⟩)
 (.leaf ⟨(19, 25931175952384), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record035_result⟩)))))
 (.branch 42
 (.branch 39
 (.branch 37
 (.leaf ⟨(19, 25942831464704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record036_result⟩)
 (.branch 38
 (.leaf ⟨(19, 25946451640576), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record037_result⟩)
 (.leaf ⟨(19, 25946468155648), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record038_result⟩)))
 (.branch 40
 (.leaf ⟨(19, 25963094638848), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record039_result⟩)
 (.branch 41
 (.leaf ⟨(19, 25963131895808), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record040_result⟩)
 (.leaf ⟨(19, 25963140218880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record041_result⟩))))
 (.branch 45
 (.branch 43
 (.leaf ⟨(19, 25963363106816), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record042_result⟩)
 (.branch 44
 (.leaf ⟨(19, 25963371429888), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record043_result⟩)
 (.leaf ⟨(19, 25963387944960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record044_result⟩)))
 (.branch 46
 (.leaf ⟨(19, 25963882876928), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record045_result⟩)
 (.branch 47
 (.leaf ⟨(19, 25964419678208), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record046_result⟩)
 (.leaf ⟨(19, 25964428001280), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record047_result⟩)))))))
 (.branch 72
 (.branch 60
 (.branch 54
 (.branch 51
 (.branch 49
 (.leaf ⟨(19, 26118971752704), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record048_result⟩)
 (.branch 50
 (.leaf ⟨(19, 26121089384448), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record049_result⟩)
 (.leaf ⟨(19, 26152223932672), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record050_result⟩)))
 (.branch 52
 (.leaf ⟨(19, 26184419672320), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record051_result⟩)
 (.branch 53
 (.leaf ⟨(19, 26188848889856), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record052_result⟩)
 (.leaf ⟨(19, 26216631664896), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record053_result⟩))))
 (.branch 57
 (.branch 55
 (.leaf ⟨(19, 26437244436608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record054_result⟩)
 (.branch 56
 (.leaf ⟨(19, 26469456691328), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record055_result⟩)
 (.leaf ⟨(19, 26478042431616), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record056_result⟩)))
 (.branch 58
 (.leaf ⟨(19, 26478273642624), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record057_result⟩)
 (.branch 59
 (.leaf ⟨(19, 26502692356224), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record058_result⟩)
 (.leaf ⟨(19, 26502706020608), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record059_result⟩)))))
 (.branch 66
 (.branch 63
 (.branch 61
 (.leaf ⟨(19, 26504048214016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record060_result⟩)
 (.branch 62
 (.leaf ⟨(19, 26510237909120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record061_result⟩)
 (.leaf ⟨(19, 26512633922048), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record062_result⟩)))
 (.branch 64
 (.leaf ⟨(19, 26519582818560), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record063_result⟩)
 (.branch 65
 (.leaf ⟨(19, 26572499206400), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record064_result⟩)
 (.leaf ⟨(19, 26572499271680), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record065_result⟩))))
 (.branch 69
 (.branch 67
 (.leaf ⟨(19, 26572633473024), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record066_result⟩)
 (.branch 68
 (.leaf ⟨(19, 26572763447552), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record067_result⟩)
 (.leaf ⟨(19, 26572771835904), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record068_result⟩)))
 (.branch 70
 (.leaf ⟨(19, 26572837896192), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record069_result⟩)
 (.branch 71
 (.leaf ⟨(19, 26574918270976), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record070_result⟩)
 (.leaf ⟨(19, 26575958458368), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record071_result⟩))))))
 (.branch 84
 (.branch 78
 (.branch 75
 (.branch 73
 (.leaf ⟨(19, 26579558801536), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record072_result⟩)
 (.branch 74
 (.leaf ⟨(19, 26580954972160), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record073_result⟩)
 (.leaf ⟨(19, 26622460707072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record074_result⟩)))
 (.branch 76
 (.leaf ⟨(19, 26631239467072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record075_result⟩)
 (.branch 77
 (.leaf ⟨(19, 26637681893440), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record076_result⟩)
 (.leaf ⟨(19, 26644435730688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record077_result⟩))))
 (.branch 81
 (.branch 79
 (.leaf ⟨(19, 26644439957504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record078_result⟩)
 (.branch 80
 (.leaf ⟨(19, 26644778582016), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record079_result⟩)
 (.leaf ⟨(19, 26648533541120), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record080_result⟩)))
 (.branch 82
 (.leaf ⟨(19, 26648747475456), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record081_result⟩)
 (.branch 83
 (.leaf ⟨(19, 26652761456640), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record082_result⟩)
 (.leaf ⟨(19, 26656785973504), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record083_result⟩)))))
 (.branch 90
 (.branch 87
 (.branch 85
 (.leaf ⟨(19, 26656992396352), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record084_result⟩)
 (.branch 86
 (.leaf ⟨(19, 26671547170944), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record085_result⟩)
 (.leaf ⟨(19, 26678828482688), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record086_result⟩)))
 (.branch 88
 (.leaf ⟨(19, 26711816159488), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record087_result⟩)
 (.branch 89
 (.leaf ⟨(19, 26712856346880), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record088_result⟩)
 (.leaf ⟨(19, 26716997722240), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record089_result⟩))))
 (.branch 93
 (.branch 91
 (.leaf ⟨(19, 26716999803008), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record090_result⟩)
 (.branch 92
 (.leaf ⟨(19, 26777382560000), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record091_result⟩)
 (.leaf ⟨(19, 26990990115072), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record092_result⟩)))
 (.branch 95
 (.branch 94
 (.leaf ⟨(19, 27025348804864), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record093_result⟩)
 (.leaf ⟨(19, 27051119673600), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record094_result⟩))
 (.branch 96
 (.leaf ⟨(19, 27053332168960), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record095_result⟩)
 (.leaf ⟨(19, 27053340557312), Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00024.record096_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (4442 + i))) 0 97 :=
  interval_of_check _ 0 97 (by decide +kernel)

public theorem complete : Block 4442 4539 :=
  block_of_table results 4442 97 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0064

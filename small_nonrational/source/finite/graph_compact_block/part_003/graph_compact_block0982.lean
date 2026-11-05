module
prelude
import GraphInputsSix0Part00017Cases
public import GraphCompactBlocks

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0982
open Papers.RationalityTen ConcreteGrowth GraphCaseCertificate GraphFiniteDispatch FiniteChecks

private def results : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 50
 (.branch 25
 (.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨(32, 6927121678336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record000_result⟩)
 (.branch 2
 (.leaf ⟨(32, 6927381725312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record001_result⟩)
 (.leaf ⟨(32, 6927650160640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record002_result⟩)))
 (.branch 4
 (.leaf ⟨(32, 6927654322176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record003_result⟩)
 (.branch 5
 (.leaf ⟨(32, 6929061544192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record004_result⟩)
 (.leaf ⟨(32, 6929069932544), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record005_result⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨(32, 6929193664768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record006_result⟩)
 (.branch 8
 (.leaf ⟨(32, 6929197891584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record007_result⟩)
 (.leaf ⟨(32, 6929202053120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record008_result⟩)))
 (.branch 10
 (.leaf ⟨(32, 6929268113408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record009_result⟩)
 (.branch 11
 (.leaf ⟨(32, 6929462100096), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record010_result⟩)
 (.leaf ⟨(32, 6929598414848), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record011_result⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨(32, 6929662361728), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record012_result⟩)
 (.branch 14
 (.leaf ⟨(32, 6929730535424), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record013_result⟩)
 (.leaf ⟨(32, 6929734696960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record014_result⟩)))
 (.branch 16
 (.leaf ⟨(32, 6933362802688), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record015_result⟩)
 (.branch 17
 (.leaf ⟨(32, 6936474976512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record016_result⟩)
 (.leaf ⟨(32, 6936479203328), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record017_result⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨(32, 6936483364864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record018_result⟩)
 (.branch 20
 (.leaf ⟨(32, 6936545263616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record019_result⟩)
 (.leaf ⟨(32, 6936549425152), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record020_result⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨(32, 6936943673472), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record021_result⟩)
 (.leaf ⟨(32, 6944504955008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record022_result⟩))
 (.branch 24
 (.leaf ⟨(32, 6950944260224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record023_result⟩)
 (.leaf ⟨(32, 6951984447616), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record024_result⟩))))))
 (.branch 37
 (.branch 31
 (.branch 28
 (.branch 26
 (.leaf ⟨(32, 6968687231232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record025_result⟩)
 (.branch 27
 (.leaf ⟨(32, 6968691458048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record026_result⟩)
 (.leaf ⟨(32, 6968695619584), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record027_result⟩)))
 (.branch 29
 (.leaf ⟨(32, 6968757518336), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record028_result⟩)
 (.branch 30
 (.leaf ⟨(32, 6968761679872), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record029_result⟩)
 (.leaf ⟨(32, 6968889638912), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record030_result⟩))))
 (.branch 34
 (.branch 32
 (.leaf ⟨(32, 6969155928192), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record031_result⟩)
 (.branch 33
 (.leaf ⟨(32, 6975115280640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record032_result⟩)
 (.leaf ⟨(32, 6975316582656), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record033_result⟩)))
 (.branch 35
 (.leaf ⟨(32, 6977312950528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record034_result⟩)
 (.branch 36
 (.leaf ⟨(32, 6977329595136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record035_result⟩)
 (.leaf ⟨(32, 6977337983232), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record036_result⟩)))))
 (.branch 43
 (.branch 40
 (.branch 38
 (.leaf ⟨(32, 6977338048512), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record037_result⟩)
 (.branch 39
 (.leaf ⟨(32, 6977465942272), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record038_result⟩)
 (.leaf ⟨(32, 6977470103808), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record039_result⟩)))
 (.branch 41
 (.leaf ⟨(32, 6977470169088), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record040_result⟩)
 (.branch 42
 (.leaf ⟨(32, 6977589610752), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record041_result⟩)
 (.leaf ⟨(32, 6977734344960), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record042_result⟩))))
 (.branch 46
 (.branch 44
 (.leaf ⟨(32, 6977734410240), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record043_result⟩)
 (.branch 45
 (.leaf ⟨(32, 6977738539136), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record044_result⟩)
 (.leaf ⟨(32, 6977740619904), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record045_result⟩)))
 (.branch 48
 (.branch 47
 (.leaf ⟨(32, 6977858046080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record046_result⟩)
 (.leaf ⟨(32, 6979612377344), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record047_result⟩))
 (.branch 49
 (.leaf ⟨(32, 6979616538880), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record048_result⟩)
 (.leaf ⟨(32, 6979616604160), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record049_result⟩)))))))
 (.branch 75
 (.branch 62
 (.branch 56
 (.branch 53
 (.branch 51
 (.leaf ⟨(32, 6979669985536), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record050_result⟩)
 (.branch 52
 (.leaf ⟨(32, 6979880780032), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record051_result⟩)
 (.leaf ⟨(32, 6979880845312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record052_result⟩)))
 (.branch 54
 (.leaf ⟨(32, 6979884974208), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record053_result⟩)
 (.branch 55
 (.leaf ⟨(32, 6979938420864), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record054_result⟩)
 (.leaf ⟨(32, 6982287228929), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record055_result⟩))))
 (.branch 59
 (.branch 57
 (.leaf ⟨(32, 6983830735104), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record056_result⟩)
 (.branch 58
 (.leaf ⟨(32, 6983905247488), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record057_result⟩)
 (.leaf ⟨(32, 6983911555072), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record058_result⟩)))
 (.branch 60
 (.leaf ⟨(32, 6983962855680), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record059_result⟩)
 (.branch 61
 (.leaf ⟨(32, 6984028915968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record060_result⟩)
 (.leaf ⟨(32, 6984173650176), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record061_result⟩)))))
 (.branch 68
 (.branch 65
 (.branch 63
 (.leaf ⟨(32, 6984173715456), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record062_result⟩)
 (.branch 64
 (.leaf ⟨(32, 6984175796224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record063_result⟩)
 (.leaf ⟨(32, 6984176836608), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record064_result⟩)))
 (.branch 66
 (.leaf ⟨(32, 6984179925120), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record065_result⟩)
 (.branch 67
 (.leaf ⟨(32, 6984231291008), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record066_result⟩)
 (.leaf ⟨(32, 6986171220224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record067_result⟩))))
 (.branch 71
 (.branch 69
 (.leaf ⟨(32, 6986179608576), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record068_result⟩)
 (.branch 70
 (.leaf ⟨(32, 6986447978497), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record069_result⟩)
 (.leaf ⟨(32, 6988528353281), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record070_result⟩)))
 (.branch 73
 (.branch 72
 (.leaf ⟨(32, 6992420669568), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record071_result⟩)
 (.leaf ⟨(32, 6992548595968), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record072_result⟩))
 (.branch 74
 (.leaf ⟨(32, 6992552790144), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record073_result⟩)
 (.leaf ⟨(32, 6992618850432), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record074_result⟩))))))
 (.branch 87
 (.branch 81
 (.branch 78
 (.branch 76
 (.leaf ⟨(32, 6992763584640), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record075_result⟩)
 (.branch 77
 (.leaf ⟨(32, 6992765665408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record076_result⟩)
 (.leaf ⟨(32, 6992765698048), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record077_result⟩)))
 (.branch 79
 (.leaf ⟨(32, 6998917808384), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record078_result⟩)
 (.branch 80
 (.leaf ⟨(32, 6998922035200), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record079_result⟩)
 (.leaf ⟨(32, 6998926196736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record080_result⟩))))
 (.branch 84
 (.branch 82
 (.leaf ⟨(32, 6998930228224), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record081_result⟩)
 (.branch 83
 (.leaf ⟨(32, 6999186243712), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record082_result⟩)
 (.leaf ⟨(32, 6999454515840), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record083_result⟩)))
 (.branch 85
 (.leaf ⟨(32, 7003078557952), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record084_result⟩)
 (.branch 86
 (.leaf ⟨(32, 7003082784768), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record085_result⟩)
 (.leaf ⟨(32, 7003086946304), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record086_result⟩)))))
 (.branch 93
 (.branch 90
 (.branch 88
 (.leaf ⟨(32, 7003090977792), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record087_result⟩)
 (.branch 89
 (.leaf ⟨(32, 7003346830080), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record088_result⟩)
 (.leaf ⟨(32, 7003481194624), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record089_result⟩)))
 (.branch 91
 (.leaf ⟨(32, 7003487339520), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record090_result⟩)
 (.branch 92
 (.leaf ⟨(32, 7003615265408), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record091_result⟩)
 (.leaf ⟨(32, 7003883700736), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record092_result⟩))))
 (.branch 96
 (.branch 94
 (.leaf ⟨(32, 7012819697920), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record093_result⟩)
 (.branch 95
 (.leaf ⟨(32, 7014966132992), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record094_result⟩)
 (.leaf ⟨(32, 7016039350528), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record095_result⟩)))
 (.branch 98
 (.branch 97
 (.leaf ⟨(32, 7033120129024), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record096_result⟩)
 (.leaf ⟨(32, 7033186189312), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record097_result⟩))
 (.branch 99
 (.leaf ⟨(32, 7046055362816), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record098_result⟩)
 (.leaf ⟨(32, 7046575425664), Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00017.record099_result⟩))))))))

private theorem keys_checked : Interval (fun i => decide ((results.get i).val =
    GraphRoutes.compactKeys.entry (28486 + i))) 0 100 :=
  interval_of_check _ 0 100 (by decide +kernel)

public theorem complete : Block 28486 28586 :=
  block_of_table results 28486 100 keys_checked

#print axioms complete
end Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0982

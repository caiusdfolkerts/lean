module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import IntegerTables
public import RootedSixExtra06
public import RawKindedFacePlacement
public import RootedSixExtra06OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
open ConcreteGrowth
abbrev blockCount : Nat := 130
noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩
cert_root_6 06
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 65
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨1, 4, 274960, 274960, 361617786720, 288326448720⟩, 518))
 (.leaf (⟨1, 4, 274960, 274960, 361616738145, 288326448645⟩, 783)))
 (.branch 3
 (.leaf (⟨1, 4, 274960, 274960, 361599960930, 288326447205⟩, 1204))
 (.leaf (⟨1, 4, 274960, 274960, 361331525475, 288326420325⟩, 1313))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 274960, 274960, 357036558180, 288325928805⟩, 1422))
 (.leaf (⟨1, 4, 274960, 274960, 288317081445, 288317081445⟩, 1447)))
 (.branch 7
 (.leaf (⟨1, 4, 274945, 274945, 361617786720, 288326448720⟩, 519))
 (.leaf (⟨1, 4, 274945, 274945, 361616738145, 288326448645⟩, 784)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨1, 4, 274945, 274945, 361599960930, 288326447205⟩, 1205))
 (.leaf (⟨1, 4, 274945, 274945, 361331525475, 288326420325⟩, 1314)))
 (.branch 11
 (.leaf (⟨1, 4, 274945, 274945, 357036558180, 288325928805⟩, 1423))
 (.leaf (⟨1, 4, 274945, 274945, 288317081445, 288317081445⟩, 1448))))
 (.branch 14
 (.branch 13
 (.leaf (⟨2, 4, 274960, 274960, 361626105360, 361626105360⟩, 12714177))
 (.leaf (⟨2, 4, 274960, 274960, 361609328160, 361626104160⟩, 22937949)))
 (.branch 15
 (.leaf (⟨2, 4, 274960, 274960, 361592550945, 361626104070⟩, 40305254))
 (.leaf (⟨2, 4, 274960, 274960, 361324115505, 361626081030⟩, 45810362))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨2, 4, 274960, 274960, 361055680050, 361626079350⟩, 57672559))
 (.leaf (⟨2, 4, 274960, 274960, 356760712770, 361625649270⟩, 67896331)))
 (.branch 19
 (.leaf (⟨2, 4, 274960, 274960, 352465745475, 361625618550⟩, 80544972))
 (.leaf (⟨2, 4, 274960, 274960, 288326448720, 361617786720⟩, 28443057))))
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 274960, 274960, 288041236050, 361617784950⟩, 73401439))
 (.leaf (⟨2, 4, 274960, 274960, 215026792020, 361617201270⟩, 87688505)))
 (.branch 23
 (.leaf (⟨1, 4, 274690, 274465, 361617786720, 288326448720⟩, 512))
 (.leaf (⟨1, 4, 274690, 274465, 361616738145, 288326448645⟩, 777)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨1, 4, 274690, 274465, 361599960930, 288326447205⟩, 1198))
 (.leaf (⟨1, 4, 274690, 274465, 361331525475, 288326420325⟩, 1307)))
 (.branch 27
 (.leaf (⟨1, 4, 274690, 274465, 357036558180, 288325928805⟩, 1416))
 (.leaf (⟨1, 4, 274690, 274465, 288317081445, 288317081445⟩, 1441))))
 (.branch 30
 (.branch 29
 (.leaf (⟨2, 4, 274720, 274720, 361626105360, 361626105360⟩, 12255422))
 (.leaf (⟨2, 4, 274720, 274720, 361609328160, 361626104160⟩, 22479194)))
 (.branch 31
 (.leaf (⟨2, 4, 274720, 274720, 361592550945, 361626104070⟩, 39846499))
 (.leaf (⟨2, 4, 274720, 274720, 361324115505, 361626081030⟩, 45351607)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 274720, 274720, 361055680050, 361626079350⟩, 57213804))
 (.leaf (⟨2, 4, 274720, 274720, 356760712770, 361625649270⟩, 67437576)))
 (.branch 35
 (.leaf (⟨2, 4, 274720, 274720, 352465745475, 361625618550⟩, 80086217))
 (.leaf (⟨2, 4, 274720, 274720, 288326448720, 361617786720⟩, 27984302))))
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 4, 274720, 274720, 288041236050, 361617784950⟩, 72942684))
 (.leaf (⟨2, 4, 274720, 274720, 215026792020, 361617201270⟩, 87229750)))
 (.branch 39
 (.leaf (⟨2, 4, 274465, 274690, 361626105360, 361626105360⟩, 12320959))
 (.leaf (⟨2, 4, 274465, 274690, 361609328160, 361626104160⟩, 22544731)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 4, 274465, 274690, 361592550945, 361626104070⟩, 39912036))
 (.leaf (⟨2, 4, 274465, 274690, 361324115505, 361626081030⟩, 45417144)))
 (.branch 43
 (.leaf (⟨2, 4, 274465, 274690, 361055680050, 361626079350⟩, 57279341))
 (.leaf (⟨2, 4, 274465, 274690, 356760712770, 361625649270⟩, 67503113))))
 (.branch 46
 (.branch 45
 (.leaf (⟨2, 4, 274465, 274690, 352465745475, 361625618550⟩, 80151754))
 (.leaf (⟨2, 4, 274465, 274690, 288326448720, 361617786720⟩, 28049839)))
 (.branch 47
 (.leaf (⟨2, 4, 274465, 274690, 288041236050, 361617784950⟩, 73008221))
 (.leaf (⟨2, 4, 274465, 274690, 215026792020, 361617201270⟩, 87295287))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (⟨3, 4, 274960, 274960, 361742426640, 434925761040⟩, 136610683683877993485500532))
 (.leaf (⟨3, 4, 274960, 274960, 360937120545, 434925740295⟩, 645576219939394681162039833)))
 (.branch 51
 (.leaf (⟨3, 4, 274960, 274960, 348052218930, 434925342855⟩, 965946450599042952502379298))
 (.leaf (⟨3, 4, 274960, 274960, 288191112480, 434918490480⟩, 325205989279746409821700368))))
 (.branch 54
 (.branch 53
 (.leaf (⟨3, 4, 274960, 274960, 210613265730, 434917970055⟩, 1154541756194911368838579134))
 (.leaf (⟨1, 4, 270595, 262945, 361617786720, 288326448720⟩, 523)))
 (.branch 55
 (.leaf (⟨1, 4, 270595, 262945, 361616738145, 288326448645⟩, 788))
 (.leaf (⟨1, 4, 270595, 262945, 361599960930, 288326447205⟩, 1209)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (⟨1, 4, 270595, 262945, 361331525475, 288326420325⟩, 1318))
 (.leaf (⟨1, 4, 270595, 262945, 357036558180, 288325928805⟩, 1427)))
 (.branch 59
 (.leaf (⟨1, 4, 270595, 262945, 288317081445, 288317081445⟩, 1452))
 (.leaf (⟨2, 4, 270385, 267010, 361626105360, 361626105360⟩, 12779716))))
 (.branch 62
 (.branch 61
 (.leaf (⟨2, 4, 270385, 267010, 361609328160, 361626104160⟩, 23003488))
 (.leaf (⟨2, 4, 270385, 267010, 361592550945, 361626104070⟩, 40370793)))
 (.branch 63
 (.leaf (⟨2, 4, 270385, 267010, 361324115505, 361626081030⟩, 45875901))
 (.branch 64
 (.leaf (⟨2, 4, 270385, 267010, 361055680050, 361626079350⟩, 57738098))
 (.leaf (⟨2, 4, 270385, 267010, 356760712770, 361625649270⟩, 67961870)))))))))
 (.branch 97
 (.branch 81
 (.branch 73
 (.branch 69
 (.branch 67
 (.branch 66
 (.leaf (⟨2, 4, 270385, 267010, 352465745475, 361625618550⟩, 80610511))
 (.leaf (⟨2, 4, 270385, 267010, 288326448720, 361617786720⟩, 28508596)))
 (.branch 68
 (.leaf (⟨2, 4, 270385, 267010, 288041236050, 361617784950⟩, 73466978))
 (.leaf (⟨2, 4, 270385, 267010, 215026792020, 361617201270⟩, 87754044))))
 (.branch 71
 (.branch 70
 (.leaf (⟨2, 4, 266290, 266290, 361626105360, 361626105360⟩, 12583101))
 (.leaf (⟨2, 4, 266290, 266290, 361609328160, 361626104160⟩, 22806873)))
 (.branch 72
 (.leaf (⟨2, 4, 266290, 266290, 361592550945, 361626104070⟩, 40174178))
 (.leaf (⟨2, 4, 266290, 266290, 361324115505, 361626081030⟩, 45679286)))))
 (.branch 77
 (.branch 75
 (.branch 74
 (.leaf (⟨2, 4, 266290, 266290, 361055680050, 361626079350⟩, 57541483))
 (.leaf (⟨2, 4, 266290, 266290, 356760712770, 361625649270⟩, 67765255)))
 (.branch 76
 (.leaf (⟨2, 4, 266290, 266290, 352465745475, 361625618550⟩, 80413896))
 (.leaf (⟨2, 4, 266290, 266290, 288326448720, 361617786720⟩, 28311981))))
 (.branch 79
 (.branch 78
 (.leaf (⟨2, 4, 266290, 266290, 288041236050, 361617784950⟩, 73270363))
 (.leaf (⟨2, 4, 266290, 266290, 215026792020, 361617201270⟩, 87557429)))
 (.branch 80
 (.leaf (⟨3, 4, 262945, 270595, 361742426640, 434925761040⟩, 137819683291313329543381107))
 (.leaf (⟨3, 4, 262945, 270595, 360937120545, 434925740295⟩, 646785219546830017219920408))))))
 (.branch 89
 (.branch 85
 (.branch 83
 (.branch 82
 (.leaf (⟨3, 4, 262945, 270595, 348052218930, 434925342855⟩, 967155450206478288560259873))
 (.leaf (⟨3, 4, 262945, 270595, 288191112480, 434918490480⟩, 326414988887181745879580943)))
 (.branch 84
 (.leaf (⟨3, 4, 262945, 270595, 210613265730, 434917970055⟩, 1155750755802346704896459709))
 (.leaf (⟨1, 4, 205060, 17185, 361617786720, 288326448720⟩, 521))))
 (.branch 87
 (.branch 86
 (.leaf (⟨1, 4, 205060, 17185, 361616738145, 288326448645⟩, 786))
 (.leaf (⟨1, 4, 205060, 17185, 361599960930, 288326447205⟩, 1207)))
 (.branch 88
 (.leaf (⟨1, 4, 205060, 17185, 361331525475, 288326420325⟩, 1316))
 (.leaf (⟨1, 4, 205060, 17185, 357036558180, 288325928805⟩, 1425)))))
 (.branch 93
 (.branch 91
 (.branch 90
 (.leaf (⟨1, 4, 205060, 17185, 288317081445, 288317081445⟩, 1450))
 (.leaf (⟨2, 4, 205120, 82720, 361626105360, 361626105360⟩, 12779716)))
 (.branch 92
 (.leaf (⟨2, 4, 205120, 82720, 361609328160, 361626104160⟩, 23003488))
 (.leaf (⟨2, 4, 205120, 82720, 361592550945, 361626104070⟩, 40370793))))
 (.branch 95
 (.branch 94
 (.leaf (⟨2, 4, 205120, 82720, 361324115505, 361626081030⟩, 45875901))
 (.leaf (⟨2, 4, 205120, 82720, 361055680050, 361626079350⟩, 57738098)))
 (.branch 96
 (.leaf (⟨2, 4, 205120, 82720, 356760712770, 361625649270⟩, 67961870))
 (.leaf (⟨2, 4, 205120, 82720, 352465745475, 361625618550⟩, 80610511)))))))
 (.branch 113
 (.branch 105
 (.branch 101
 (.branch 99
 (.branch 98
 (.leaf (⟨2, 4, 205120, 82720, 288326448720, 361617786720⟩, 28508596))
 (.leaf (⟨2, 4, 205120, 82720, 288041236050, 361617784950⟩, 73466978)))
 (.branch 100
 (.leaf (⟨2, 4, 205120, 82720, 215026792020, 361617201270⟩, 87754044))
 (.leaf (⟨2, 4, 200770, 81970, 361626105360, 361626105360⟩, 12452027))))
 (.branch 103
 (.branch 102
 (.leaf (⟨2, 4, 200770, 81970, 361609328160, 361626104160⟩, 22675799))
 (.leaf (⟨2, 4, 200770, 81970, 361592550945, 361626104070⟩, 40043104)))
 (.branch 104
 (.leaf (⟨2, 4, 200770, 81970, 361324115505, 361626081030⟩, 45548212))
 (.leaf (⟨2, 4, 200770, 81970, 361055680050, 361626079350⟩, 57410409)))))
 (.branch 109
 (.branch 107
 (.branch 106
 (.leaf (⟨2, 4, 200770, 81970, 356760712770, 361625649270⟩, 67634181))
 (.leaf (⟨2, 4, 200770, 81970, 352465745475, 361625618550⟩, 80282822)))
 (.branch 108
 (.leaf (⟨2, 4, 200770, 81970, 288326448720, 361617786720⟩, 28180907))
 (.leaf (⟨2, 4, 200770, 81970, 288041236050, 361617784950⟩, 73139289))))
 (.branch 111
 (.branch 110
 (.leaf (⟨2, 4, 200770, 81970, 215026792020, 361617201270⟩, 87426355))
 (.leaf (⟨3, 4, 201760, 147760, 361742426640, 434925761040⟩, 137819683291313329543381107)))
 (.branch 112
 (.leaf (⟨3, 4, 201760, 147760, 360937120545, 434925740295⟩, 646785219546830017219920408))
 (.leaf (⟨3, 4, 201760, 147760, 348052218930, 434925342855⟩, 967155450206478288560259873))))))
 (.branch 121
 (.branch 117
 (.branch 115
 (.branch 114
 (.leaf (⟨3, 4, 201760, 147760, 288191112480, 434918490480⟩, 326414988887181745879580943))
 (.leaf (⟨3, 4, 201760, 147760, 210613265730, 434917970055⟩, 1155750755802346704896459709)))
 (.branch 116
 (.leaf (⟨2, 4, 135235, 66610, 361626105360, 361626105360⟩, 12976325))
 (.leaf (⟨2, 4, 135235, 66610, 361609328160, 361626104160⟩, 23200097))))
 (.branch 119
 (.branch 118
 (.leaf (⟨2, 4, 135235, 66610, 361592550945, 361626104070⟩, 40567402))
 (.leaf (⟨2, 4, 135235, 66610, 361324115505, 361626081030⟩, 46072510)))
 (.branch 120
 (.leaf (⟨2, 4, 135235, 66610, 361055680050, 361626079350⟩, 57934707))
 (.leaf (⟨2, 4, 135235, 66610, 356760712770, 361625649270⟩, 68158479)))))
 (.branch 125
 (.branch 123
 (.branch 122
 (.leaf (⟨2, 4, 135235, 66610, 352465745475, 361625618550⟩, 80807120))
 (.leaf (⟨2, 4, 135235, 66610, 288326448720, 361617786720⟩, 28705205)))
 (.branch 124
 (.leaf (⟨2, 4, 135235, 66610, 288041236050, 361617784950⟩, 73663587))
 (.leaf (⟨2, 4, 135235, 66610, 215026792020, 361617201270⟩, 87950653))))
 (.branch 127
 (.branch 126
 (.leaf (⟨3, 4, 66610, 135235, 361742426640, 434925761040⟩, 141446442302287260631040112))
 (.leaf (⟨3, 4, 66610, 135235, 360937120545, 434925740295⟩, 650411978557803948307579413)))
 (.branch 128
 (.leaf (⟨3, 4, 66610, 135235, 348052218930, 434925342855⟩, 970782209217452219647918878))
 (.branch 129
 (.leaf (⟨3, 4, 66610, 135235, 288191112480, 434918490480⟩, 330041747898155676967239948))
 (.leaf (⟨3, 4, 66610, 135235, 210613265730, 434917970055⟩, 1159377514813320635984118714))))))))))
cert_raw_4
cert_witness_4 2300
cert_faceTable_4 259
cert_faceWitness_4
cert_validity_4 5
cert_placement_4 5 06
cert_test_10
cert_symmetry_4 06
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
cert_check_4 0000 0000 0 0 1 1
cert_block_8 0000 0 1
cert_check_4 0001 0000 1 0 1 1
cert_block_8 0001 1 1
cert_check_4 0002 0000 2 0 1 1
cert_block_8 0002 2 1
cert_check_4 0003 0000 3 0 1 1
cert_block_8 0003 3 1
cert_check_4 0004 0000 4 0 1 1
cert_block_8 0004 4 1
cert_check_4 0005 0000 5 0 1 1
cert_block_8 0005 5 1
cert_check_4 0006 0000 6 0 1 1
cert_block_8 0006 6 1
cert_check_4 0007 0000 7 0 1 1
cert_block_8 0007 7 1
cert_check_4 0008 0000 8 0 1 1
cert_block_8 0008 8 1
cert_check_4 0009 0000 9 0 1 1
cert_block_8 0009 9 1
cert_check_4 0010 0000 10 0 1 1
cert_block_8 0010 10 1
cert_check_4 0011 0000 11 0 1 1
cert_block_8 0011 11 1
cert_check_4 0012 0000 12 0 2 2
cert_block_8 0012 12 2
cert_check_4 0013 0000 13 0 2 2
cert_block_8 0013 13 2
cert_check_4 0014 0000 14 0 2 2
cert_block_8 0014 14 2
cert_check_4 0015 0000 15 0 2 2
cert_block_8 0015 15 2
cert_check_4 0016 0000 16 0 2 2
cert_block_8 0016 16 2
cert_check_4 0017 0000 17 0 2 2
cert_block_8 0017 17 2
cert_check_4 0018 0000 18 0 2 2
cert_block_8 0018 18 2
cert_check_4 0019 0000 19 0 2 2
cert_block_8 0019 19 2
cert_check_4 0020 0000 20 0 2 2
cert_block_8 0020 20 2
cert_check_4 0021 0000 21 0 2 2
cert_block_8 0021 21 2
cert_check_4 0022 0000 22 0 1 1
cert_block_8 0022 22 1
cert_check_4 0023 0000 23 0 1 1
cert_block_8 0023 23 1
cert_check_4 0024 0000 24 0 1 1
cert_block_8 0024 24 1
cert_check_4 0025 0000 25 0 1 1
cert_block_8 0025 25 1
cert_check_4 0026 0000 26 0 1 1
cert_block_8 0026 26 1
cert_check_4 0027 0000 27 0 1 1
cert_block_8 0027 27 1
cert_check_4 0028 0000 28 0 2 2
cert_block_8 0028 28 2
cert_check_4 0029 0000 29 0 2 2
cert_block_8 0029 29 2
cert_check_4 0030 0000 30 0 2 2
cert_block_8 0030 30 2
cert_check_4 0031 0000 31 0 2 2
cert_block_8 0031 31 2
cert_check_4 0032 0000 32 0 2 2
cert_block_8 0032 32 2
cert_check_4 0033 0000 33 0 2 2
cert_block_8 0033 33 2
cert_check_4 0034 0000 34 0 2 2
cert_block_8 0034 34 2
cert_check_4 0035 0000 35 0 2 2
cert_block_8 0035 35 2
cert_check_4 0036 0000 36 0 2 2
cert_block_8 0036 36 2
cert_check_4 0037 0000 37 0 2 2
cert_block_8 0037 37 2
cert_check_4 0038 0000 38 0 2 2
cert_block_8 0038 38 2
cert_check_4 0039 0000 39 0 2 2
cert_block_8 0039 39 2
cert_check_4 0040 0000 40 0 2 2
cert_block_8 0040 40 2
cert_check_4 0041 0000 41 0 2 2
cert_block_8 0041 41 2
cert_check_4 0042 0000 42 0 2 2
cert_block_8 0042 42 2
cert_check_4 0043 0000 43 0 2 2
cert_block_8 0043 43 2
cert_check_4 0044 0000 44 0 2 2
cert_block_8 0044 44 2
cert_check_4 0045 0000 45 0 2 2
cert_block_8 0045 45 2
cert_check_4 0046 0000 46 0 2 2
cert_block_8 0046 46 2
cert_check_4 0047 0000 47 0 2 2
cert_block_8 0047 47 2
cert_check_4 0048 0000 48 0 6 6
cert_block_8 0048 48 6
cert_check_4 0049 0000 49 0 6 6
cert_block_8 0049 49 6
cert_check_4 0050 0000 50 0 6 6
cert_block_8 0050 50 6
cert_check_4 0051 0000 51 0 6 6
cert_block_8 0051 51 6
cert_check_4 0052 0000 52 0 6 6
cert_block_8 0052 52 6
cert_check_4 0053 0000 53 0 1 1
cert_block_8 0053 53 1
cert_check_4 0054 0000 54 0 1 1
cert_block_8 0054 54 1
cert_check_4 0055 0000 55 0 1 1
cert_block_8 0055 55 1
cert_check_4 0056 0000 56 0 1 1
cert_block_8 0056 56 1
cert_check_4 0057 0000 57 0 1 1
cert_block_8 0057 57 1
cert_check_4 0058 0000 58 0 1 1
cert_block_8 0058 58 1
cert_check_4 0059 0000 59 0 2 2
cert_block_8 0059 59 2
cert_check_4 0060 0000 60 0 2 2
cert_block_8 0060 60 2
cert_check_4 0061 0000 61 0 2 2
cert_block_8 0061 61 2
cert_check_4 0062 0000 62 0 2 2
cert_block_8 0062 62 2
cert_check_4 0063 0000 63 0 2 2
cert_block_8 0063 63 2
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
cert_check_4 0064 0000 64 0 2 2
cert_block_8 0064 64 2
cert_check_4 0065 0000 65 0 2 2
cert_block_8 0065 65 2
cert_check_4 0066 0000 66 0 2 2
cert_block_8 0066 66 2
cert_check_4 0067 0000 67 0 2 2
cert_block_8 0067 67 2
cert_check_4 0068 0000 68 0 2 2
cert_block_8 0068 68 2
cert_check_4 0069 0000 69 0 2 2
cert_block_8 0069 69 2
cert_check_4 0070 0000 70 0 2 2
cert_block_8 0070 70 2
cert_check_4 0071 0000 71 0 2 2
cert_block_8 0071 71 2
cert_check_4 0072 0000 72 0 2 2
cert_block_8 0072 72 2
cert_check_4 0073 0000 73 0 2 2
cert_block_8 0073 73 2
cert_check_4 0074 0000 74 0 2 2
cert_block_8 0074 74 2
cert_check_4 0075 0000 75 0 2 2
cert_block_8 0075 75 2
cert_check_4 0076 0000 76 0 2 2
cert_block_8 0076 76 2
cert_check_4 0077 0000 77 0 2 2
cert_block_8 0077 77 2
cert_check_4 0078 0000 78 0 2 2
cert_block_8 0078 78 2
cert_check_4 0079 0000 79 0 6 6
cert_block_8 0079 79 6
cert_check_4 0080 0000 80 0 6 6
cert_block_8 0080 80 6
cert_check_4 0081 0000 81 0 6 6
cert_block_8 0081 81 6
cert_check_4 0082 0000 82 0 6 6
cert_block_8 0082 82 6
cert_check_4 0083 0000 83 0 6 6
cert_block_8 0083 83 6
cert_check_4 0084 0000 84 0 1 1
cert_block_8 0084 84 1
cert_check_4 0085 0000 85 0 1 1
cert_block_8 0085 85 1
cert_check_4 0086 0000 86 0 1 1
cert_block_8 0086 86 1
cert_check_4 0087 0000 87 0 1 1
cert_block_8 0087 87 1
cert_check_4 0088 0000 88 0 1 1
cert_block_8 0088 88 1
cert_check_4 0089 0000 89 0 1 1
cert_block_8 0089 89 1
cert_check_4 0090 0000 90 0 2 2
cert_block_8 0090 90 2
cert_check_4 0091 0000 91 0 2 2
cert_block_8 0091 91 2
cert_check_4 0092 0000 92 0 2 2
cert_block_8 0092 92 2
cert_check_4 0093 0000 93 0 2 2
cert_block_8 0093 93 2
cert_check_4 0094 0000 94 0 2 2
cert_block_8 0094 94 2
cert_check_4 0095 0000 95 0 2 2
cert_block_8 0095 95 2
cert_check_4 0096 0000 96 0 2 2
cert_block_8 0096 96 2
cert_check_4 0097 0000 97 0 2 2
cert_block_8 0097 97 2
cert_check_4 0098 0000 98 0 2 2
cert_block_8 0098 98 2
cert_check_4 0099 0000 99 0 2 2
cert_block_8 0099 99 2
cert_check_4 0100 0000 100 0 2 2
cert_block_8 0100 100 2
cert_check_4 0101 0000 101 0 2 2
cert_block_8 0101 101 2
cert_check_4 0102 0000 102 0 2 2
cert_block_8 0102 102 2
cert_check_4 0103 0000 103 0 2 2
cert_block_8 0103 103 2
cert_check_4 0104 0000 104 0 2 2
cert_block_8 0104 104 2
cert_check_4 0105 0000 105 0 2 2
cert_block_8 0105 105 2
cert_check_4 0106 0000 106 0 2 2
cert_block_8 0106 106 2
cert_check_4 0107 0000 107 0 2 2
cert_block_8 0107 107 2
cert_check_4 0108 0000 108 0 2 2
cert_block_8 0108 108 2
cert_check_4 0109 0000 109 0 2 2
cert_block_8 0109 109 2
cert_check_4 0110 0000 110 0 6 6
cert_block_8 0110 110 6
cert_check_4 0111 0000 111 0 6 6
cert_block_8 0111 111 6
cert_check_4 0112 0000 112 0 6 6
cert_block_8 0112 112 6
cert_check_4 0113 0000 113 0 6 6
cert_block_8 0113 113 6
cert_check_4 0114 0000 114 0 6 6
cert_block_8 0114 114 6
cert_check_4 0115 0000 115 0 2 2
cert_block_8 0115 115 2
cert_check_4 0116 0000 116 0 2 2
cert_block_8 0116 116 2
cert_check_4 0117 0000 117 0 2 2
cert_block_8 0117 117 2
cert_check_4 0118 0000 118 0 2 2
cert_block_8 0118 118 2
cert_check_4 0119 0000 119 0 2 2
cert_block_8 0119 119 2
cert_check_4 0120 0000 120 0 2 2
cert_block_8 0120 120 2
cert_check_4 0121 0000 121 0 2 2
cert_block_8 0121 121 2
cert_check_4 0122 0000 122 0 2 2
cert_block_8 0122 122 2
cert_check_4 0123 0000 123 0 2 2
cert_block_8 0123 123 2
cert_check_4 0124 0000 124 0 2 2
cert_block_8 0124 124 2
cert_check_4 0125 0000 125 0 6 6
cert_block_8 0125 125 6
cert_check_4 0126 0000 126 0 6 6
cert_block_8 0126 126 6
cert_check_4 0127 0000 127 0 6 6
cert_block_8 0127 127 6
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
cert_check_4 0128 0000 128 0 6 6
cert_block_8 0128 128 6
cert_check_4 0129 0000 129 0 6 6
cert_block_8 0129 129 6
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1
cert_metadata_validity_12 0000 0 16 16
cert_metadata_validity_12 0016 16 32 16
cert_metadata_validity_12 0032 32 48 16
cert_metadata_validity_12 0048 48 64 16
cert_metadata_validity_12 0064 64 80 16
cert_metadata_validity_12 0080 80 96 16
cert_metadata_validity_12 0096 96 112 16
cert_metadata_validity_12 0112 112 128 16
cert_metadata_validity_12 0128 128 130 2
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 130
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 130
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 130
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 130
  metadata_validity_0112
  metadata_validity_0128))))
cert_metadata_symmetry_13 0000 0 16 16
cert_metadata_symmetry_13 0016 16 32 16
cert_metadata_symmetry_13 0032 32 48 16
cert_metadata_symmetry_13 0048 48 64 16
cert_metadata_symmetry_13 0064 64 80 16
cert_metadata_symmetry_13 0080 80 96 16
cert_metadata_symmetry_13 0096 96 112 16
cert_metadata_symmetry_13 0112 112 128 16
cert_metadata_symmetry_13 0128 128 130 2
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 130
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 130
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 130
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 130
  metadata_symmetry_0112
  metadata_symmetry_0128))))
cert_metadata_normalizers_4 5
cert_metadata_root_4
end Papers.RationalityTen.RootedCanonical.RootedSixExtra06.S5T1

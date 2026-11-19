module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import IntegerTables
public import RootedSixBase04
public import RawKindedFacePlacement
public import RootedSixBase04OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
open ConcreteGrowth
abbrev blockCount : Nat := 129
noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩
cert_root_5 04
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨0, 4, 12816, 12816, 361617201270, 215026792020⟩, 129))
 (.leaf (⟨1, 4, 12816, 12816, 361617786720, 288326448720⟩, 41)))
 (.branch 3
 (.leaf (⟨1, 4, 12816, 12816, 361616738145, 288326448645⟩, 71))
 (.leaf (⟨1, 4, 12816, 12816, 361599960930, 288326447205⟩, 91))))
 (.branch 6
 (.branch 5
 (.leaf (⟨1, 4, 12816, 12816, 361331525475, 288326420325⟩, 111))
 (.leaf (⟨1, 4, 12816, 12816, 357036558180, 288325928805⟩, 121)))
 (.branch 7
 (.leaf (⟨1, 4, 12816, 12816, 288317081445, 288317081445⟩, 125))
 (.leaf (⟨1, 4, 12801, 12801, 361617786720, 288326448720⟩, 41)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨1, 4, 12801, 12801, 361616738145, 288326448645⟩, 71))
 (.leaf (⟨1, 4, 12801, 12801, 361599960930, 288326447205⟩, 91)))
 (.branch 11
 (.leaf (⟨1, 4, 12801, 12801, 361331525475, 288326420325⟩, 111))
 (.leaf (⟨1, 4, 12801, 12801, 357036558180, 288325928805⟩, 121))))
 (.branch 14
 (.branch 13
 (.leaf (⟨1, 4, 12801, 12801, 288317081445, 288317081445⟩, 125))
 (.leaf (⟨2, 4, 12816, 12816, 361626105360, 361626105360⟩, 589833)))
 (.branch 15
 (.leaf (⟨2, 4, 12816, 12816, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 12816, 12816, 361592550945, 361626104070⟩, 3211313))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨2, 4, 12816, 12816, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 12816, 12816, 361324115505, 361626081030⟩, 3866683)))
 (.branch 19
 (.leaf (⟨2, 4, 12816, 12816, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 12816, 12816, 356760712770, 361625649270⟩, 5177423))))
 (.branch 22
 (.branch 21
 (.leaf (⟨2, 4, 12816, 12816, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 12816, 12816, 288309671505, 361617786630⟩, 4259905)))
 (.branch 23
 (.leaf (⟨2, 4, 12816, 12816, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 12816, 12816, 283746268755, 361617754230⟩, 6881385)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨2, 4, 12816, 12816, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨1, 4, 12546, 12321, 361617786720, 288326448720⟩, 41)))
 (.branch 27
 (.leaf (⟨1, 4, 12546, 12321, 361616738145, 288326448645⟩, 71))
 (.leaf (⟨1, 4, 12546, 12321, 361599960930, 288326447205⟩, 91))))
 (.branch 30
 (.branch 29
 (.leaf (⟨1, 4, 12546, 12321, 361331525475, 288326420325⟩, 111))
 (.leaf (⟨1, 4, 12546, 12321, 357036558180, 288325928805⟩, 121)))
 (.branch 31
 (.leaf (⟨1, 4, 12546, 12321, 288317081445, 288317081445⟩, 125))
 (.leaf (⟨2, 4, 12576, 12576, 361626105360, 361626105360⟩, 589833)))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf (⟨2, 4, 12576, 12576, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 12576, 12576, 361592550945, 361626104070⟩, 3211313)))
 (.branch 35
 (.leaf (⟨2, 4, 12576, 12576, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 12576, 12576, 361324115505, 361626081030⟩, 3866683))))
 (.branch 38
 (.branch 37
 (.leaf (⟨2, 4, 12576, 12576, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 12576, 12576, 356760712770, 361625649270⟩, 5177423)))
 (.branch 39
 (.leaf (⟨2, 4, 12576, 12576, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 12576, 12576, 288309671505, 361617786630⟩, 4259905)))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf (⟨2, 4, 12576, 12576, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 12576, 12576, 283746268755, 361617754230⟩, 6881385)))
 (.branch 43
 (.leaf (⟨2, 4, 12576, 12576, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨2, 4, 12321, 12546, 361626105360, 361626105360⟩, 589833))))
 (.branch 46
 (.branch 45
 (.leaf (⟨2, 4, 12321, 12546, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 12321, 12546, 361592550945, 361626104070⟩, 3211313)))
 (.branch 47
 (.leaf (⟨2, 4, 12321, 12546, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 12321, 12546, 361324115505, 361626081030⟩, 3866683))))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf (⟨2, 4, 12321, 12546, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 12321, 12546, 356760712770, 361625649270⟩, 5177423)))
 (.branch 51
 (.leaf (⟨2, 4, 12321, 12546, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 12321, 12546, 288309671505, 361617786630⟩, 4259905))))
 (.branch 54
 (.branch 53
 (.leaf (⟨2, 4, 12321, 12546, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 12321, 12546, 283746268755, 361617754230⟩, 6881385)))
 (.branch 55
 (.leaf (⟨2, 4, 12321, 12546, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨3, 4, 12816, 12816, 361742426640, 434925761040⟩, 1208944266640182156001281)))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf (⟨3, 4, 12816, 12816, 361473991440, 434925741840⟩, 6044721333200910780006405))
 (.leaf (⟨3, 4, 12816, 12816, 356910588960, 434925371760⟩, 18134163999602732340019215)))
 (.branch 59
 (.leaf (⟨3, 4, 12816, 12816, 352615621680, 434925344880⟩, 30223606666004553900032025))
 (.leaf (⟨3, 4, 12816, 12816, 287922677025, 434918490375⟩, 54402491998808197020057645))))
 (.branch 62
 (.branch 61
 (.leaf (⟨3, 4, 12816, 12816, 283627709745, 434918463495⟩, 66491934665210018580070455))
 (.leaf (⟨3, 4, 12816, 12816, 210613265730, 434917970055⟩, 90670819998013661700096075)))
 (.branch 63
 (.leaf (⟨3, 4, 12816, 12816, 141893788995, 434917935495⟩, 114849705330817304820121695))
 (.leaf (⟨1, 4, 8451, 801, 361617786720, 288326448720⟩, 41))))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf (⟨1, 4, 8451, 801, 361616738145, 288326448645⟩, 71))
 (.leaf (⟨1, 4, 8451, 801, 361599960930, 288326447205⟩, 91)))
 (.branch 67
 (.leaf (⟨1, 4, 8451, 801, 361331525475, 288326420325⟩, 111))
 (.leaf (⟨1, 4, 8451, 801, 357036558180, 288325928805⟩, 121))))
 (.branch 70
 (.branch 69
 (.leaf (⟨1, 4, 8451, 801, 288317081445, 288317081445⟩, 125))
 (.leaf (⟨2, 4, 8496, 4896, 361626105360, 361626105360⟩, 589833)))
 (.branch 71
 (.leaf (⟨2, 4, 8496, 4896, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 8496, 4896, 361592550945, 361626104070⟩, 3211313)))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf (⟨2, 4, 8496, 4896, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 8496, 4896, 361324115505, 361626081030⟩, 3866683)))
 (.branch 75
 (.leaf (⟨2, 4, 8496, 4896, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 8496, 4896, 356760712770, 361625649270⟩, 5177423))))
 (.branch 78
 (.branch 77
 (.leaf (⟨2, 4, 8496, 4896, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 8496, 4896, 288309671505, 361617786630⟩, 4259905)))
 (.branch 79
 (.leaf (⟨2, 4, 8496, 4896, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 8496, 4896, 283746268755, 361617754230⟩, 6881385))))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf (⟨2, 4, 8496, 4896, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨2, 4, 8241, 4866, 361626105360, 361626105360⟩, 589833)))
 (.branch 83
 (.leaf (⟨2, 4, 8241, 4866, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 8241, 4866, 361592550945, 361626104070⟩, 3211313))))
 (.branch 86
 (.branch 85
 (.leaf (⟨2, 4, 8241, 4866, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 8241, 4866, 361324115505, 361626081030⟩, 3866683)))
 (.branch 87
 (.leaf (⟨2, 4, 8241, 4866, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 8241, 4866, 356760712770, 361625649270⟩, 5177423)))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf (⟨2, 4, 8241, 4866, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 8241, 4866, 288309671505, 361617786630⟩, 4259905)))
 (.branch 91
 (.leaf (⟨2, 4, 8241, 4866, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 8241, 4866, 283746268755, 361617754230⟩, 6881385))))
 (.branch 94
 (.branch 93
 (.leaf (⟨2, 4, 8241, 4866, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨3, 4, 8976, 8976, 361742426640, 434925761040⟩, 1208944266640182156001281)))
 (.branch 95
 (.leaf (⟨3, 4, 8976, 8976, 361473991440, 434925741840⟩, 6044721333200910780006405))
 (.leaf (⟨3, 4, 8976, 8976, 356910588960, 434925371760⟩, 18134163999602732340019215)))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf (⟨3, 4, 8976, 8976, 352615621680, 434925344880⟩, 30223606666004553900032025))
 (.leaf (⟨3, 4, 8976, 8976, 287922677025, 434918490375⟩, 54402491998808197020057645)))
 (.branch 99
 (.leaf (⟨3, 4, 8976, 8976, 283627709745, 434918463495⟩, 66491934665210018580070455))
 (.leaf (⟨3, 4, 8976, 8976, 210613265730, 434917970055⟩, 90670819998013661700096075))))
 (.branch 102
 (.branch 101
 (.leaf (⟨3, 4, 8976, 8976, 141893788995, 434917935495⟩, 114849705330817304820121695))
 (.leaf (⟨2, 4, 4146, 4146, 361626105360, 361626105360⟩, 589833)))
 (.branch 103
 (.leaf (⟨2, 4, 4146, 4146, 361609328160, 361626104160⟩, 1245203))
 (.leaf (⟨2, 4, 4146, 4146, 361592550945, 361626104070⟩, 3211313)))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf (⟨2, 4, 4146, 4146, 361340892720, 361626081120⟩, 1900573))
 (.leaf (⟨2, 4, 4146, 4146, 361324115505, 361626081030⟩, 3866683)))
 (.branch 107
 (.leaf (⟨2, 4, 4146, 4146, 357045925440, 361625651040⟩, 2293795))
 (.leaf (⟨2, 4, 4146, 4146, 356760712770, 361625649270⟩, 5177423))))
 (.branch 110
 (.branch 109
 (.leaf (⟨2, 4, 4146, 4146, 352465745475, 361625618550⟩, 6488163))
 (.leaf (⟨2, 4, 4146, 4146, 288309671505, 361617786630⟩, 4259905)))
 (.branch 111
 (.leaf (⟨2, 4, 4146, 4146, 288041236050, 361617784950⟩, 5570645))
 (.leaf (⟨2, 4, 4146, 4146, 283746268755, 361617754230⟩, 6881385))))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf (⟨2, 4, 4146, 4146, 215026792020, 361617201270⟩, 7536755))
 (.leaf (⟨3, 4, 4896, 8496, 361742426640, 434925761040⟩, 1208944266640182156001281)))
 (.branch 115
 (.leaf (⟨3, 4, 4896, 8496, 361473991440, 434925741840⟩, 6044721333200910780006405))
 (.leaf (⟨3, 4, 4896, 8496, 356910588960, 434925371760⟩, 18134163999602732340019215))))
 (.branch 118
 (.branch 117
 (.leaf (⟨3, 4, 4896, 8496, 352615621680, 434925344880⟩, 30223606666004553900032025))
 (.leaf (⟨3, 4, 4896, 8496, 287922677025, 434918490375⟩, 54402491998808197020057645)))
 (.branch 119
 (.leaf (⟨3, 4, 4896, 8496, 283627709745, 434918463495⟩, 66491934665210018580070455))
 (.leaf (⟨3, 4, 4896, 8496, 210613265730, 434917970055⟩, 90670819998013661700096075)))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf (⟨3, 4, 4896, 8496, 141893788995, 434917935495⟩, 114849705330817304820121695))
 (.leaf (⟨3, 4, 801, 8451, 361742426640, 434925761040⟩, 1208944266640182156001281)))
 (.branch 123
 (.leaf (⟨3, 4, 801, 8451, 361473991440, 434925741840⟩, 6044721333200910780006405))
 (.leaf (⟨3, 4, 801, 8451, 356910588960, 434925371760⟩, 18134163999602732340019215))))
 (.branch 126
 (.branch 125
 (.leaf (⟨3, 4, 801, 8451, 352615621680, 434925344880⟩, 30223606666004553900032025))
 (.leaf (⟨3, 4, 801, 8451, 287922677025, 434918490375⟩, 54402491998808197020057645)))
 (.branch 127
 (.leaf (⟨3, 4, 801, 8451, 283627709745, 434918463495⟩, 66491934665210018580070455))
 (.branch 128
 (.leaf (⟨3, 4, 801, 8451, 210613265730, 434917970055⟩, 90670819998013661700096075))
 (.leaf (⟨3, 4, 801, 8451, 141893788995, 434917935495⟩, 114849705330817304820121695))))))))))
cert_raw_3
cert_witness_3 2824
cert_faceTable_3 257
cert_faceWitness_3
cert_validity_3 4
cert_placement_3 4 04
cert_test_9
cert_symmetry_3 04
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
cert_check_3 0000 0000 0 0 1 1
cert_block_6 0000 0 1
cert_check_3 0001 0000 1 0 1 1
cert_block_6 0001 1 1
cert_check_3 0002 0000 2 0 1 1
cert_block_6 0002 2 1
cert_check_3 0003 0000 3 0 1 1
cert_block_6 0003 3 1
cert_check_3 0004 0000 4 0 1 1
cert_block_6 0004 4 1
cert_check_3 0005 0000 5 0 1 1
cert_block_6 0005 5 1
cert_check_3 0006 0000 6 0 1 1
cert_block_6 0006 6 1
cert_check_3 0007 0000 7 0 1 1
cert_block_6 0007 7 1
cert_check_3 0008 0000 8 0 1 1
cert_block_6 0008 8 1
cert_check_3 0009 0000 9 0 1 1
cert_block_6 0009 9 1
cert_check_3 0010 0000 10 0 1 1
cert_block_6 0010 10 1
cert_check_3 0011 0000 11 0 1 1
cert_block_6 0011 11 1
cert_check_3 0012 0000 12 0 1 1
cert_block_6 0012 12 1
cert_check_3 0013 0000 13 0 2 2
cert_block_6 0013 13 2
cert_check_3 0014 0000 14 0 2 2
cert_block_6 0014 14 2
cert_check_3 0015 0000 15 0 2 2
cert_block_6 0015 15 2
cert_check_3 0016 0000 16 0 2 2
cert_block_6 0016 16 2
cert_check_3 0017 0000 17 0 2 2
cert_block_6 0017 17 2
cert_check_3 0018 0000 18 0 2 2
cert_block_6 0018 18 2
cert_check_3 0019 0000 19 0 2 2
cert_block_6 0019 19 2
cert_check_3 0020 0000 20 0 2 2
cert_block_6 0020 20 2
cert_check_3 0021 0000 21 0 2 2
cert_block_6 0021 21 2
cert_check_3 0022 0000 22 0 2 2
cert_block_6 0022 22 2
cert_check_3 0023 0000 23 0 2 2
cert_block_6 0023 23 2
cert_check_3 0024 0000 24 0 2 2
cert_block_6 0024 24 2
cert_check_3 0025 0000 25 0 1 1
cert_block_6 0025 25 1
cert_check_3 0026 0000 26 0 1 1
cert_block_6 0026 26 1
cert_check_3 0027 0000 27 0 1 1
cert_block_6 0027 27 1
cert_check_3 0028 0000 28 0 1 1
cert_block_6 0028 28 1
cert_check_3 0029 0000 29 0 1 1
cert_block_6 0029 29 1
cert_check_3 0030 0000 30 0 1 1
cert_block_6 0030 30 1
cert_check_3 0031 0000 31 0 2 2
cert_block_6 0031 31 2
cert_check_3 0032 0000 32 0 2 2
cert_block_6 0032 32 2
cert_check_3 0033 0000 33 0 2 2
cert_block_6 0033 33 2
cert_check_3 0034 0000 34 0 2 2
cert_block_6 0034 34 2
cert_check_3 0035 0000 35 0 2 2
cert_block_6 0035 35 2
cert_check_3 0036 0000 36 0 2 2
cert_block_6 0036 36 2
cert_check_3 0037 0000 37 0 2 2
cert_block_6 0037 37 2
cert_check_3 0038 0000 38 0 2 2
cert_block_6 0038 38 2
cert_check_3 0039 0000 39 0 2 2
cert_block_6 0039 39 2
cert_check_3 0040 0000 40 0 2 2
cert_block_6 0040 40 2
cert_check_3 0041 0000 41 0 2 2
cert_block_6 0041 41 2
cert_check_3 0042 0000 42 0 2 2
cert_block_6 0042 42 2
cert_check_3 0043 0000 43 0 2 2
cert_block_6 0043 43 2
cert_check_3 0044 0000 44 0 2 2
cert_block_6 0044 44 2
cert_check_3 0045 0000 45 0 2 2
cert_block_6 0045 45 2
cert_check_3 0046 0000 46 0 2 2
cert_block_6 0046 46 2
cert_check_3 0047 0000 47 0 2 2
cert_block_6 0047 47 2
cert_check_3 0048 0000 48 0 2 2
cert_block_6 0048 48 2
cert_check_3 0049 0000 49 0 2 2
cert_block_6 0049 49 2
cert_check_3 0050 0000 50 0 2 2
cert_block_6 0050 50 2
cert_check_3 0051 0000 51 0 2 2
cert_block_6 0051 51 2
cert_check_3 0052 0000 52 0 2 2
cert_block_6 0052 52 2
cert_check_3 0053 0000 53 0 2 2
cert_block_6 0053 53 2
cert_check_3 0054 0000 54 0 2 2
cert_block_6 0054 54 2
cert_check_3 0055 0000 55 0 6 6
cert_block_6 0055 55 6
cert_check_3 0056 0000 56 0 6 6
cert_block_6 0056 56 6
cert_check_3 0057 0000 57 0 6 6
cert_block_6 0057 57 6
cert_check_3 0058 0000 58 0 6 6
cert_block_6 0058 58 6
cert_check_3 0059 0000 59 0 6 6
cert_block_6 0059 59 6
cert_check_3 0060 0000 60 0 6 6
cert_block_6 0060 60 6
cert_check_3 0061 0000 61 0 6 6
cert_block_6 0061 61 6
cert_check_3 0062 0000 62 0 6 6
cert_block_6 0062 62 6
cert_check_3 0063 0000 63 0 1 1
cert_block_6 0063 63 1
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
cert_check_3 0064 0000 64 0 1 1
cert_block_6 0064 64 1
cert_check_3 0065 0000 65 0 1 1
cert_block_6 0065 65 1
cert_check_3 0066 0000 66 0 1 1
cert_block_6 0066 66 1
cert_check_3 0067 0000 67 0 1 1
cert_block_6 0067 67 1
cert_check_3 0068 0000 68 0 1 1
cert_block_6 0068 68 1
cert_check_3 0069 0000 69 0 2 2
cert_block_6 0069 69 2
cert_check_3 0070 0000 70 0 2 2
cert_block_6 0070 70 2
cert_check_3 0071 0000 71 0 2 2
cert_block_6 0071 71 2
cert_check_3 0072 0000 72 0 2 2
cert_block_6 0072 72 2
cert_check_3 0073 0000 73 0 2 2
cert_block_6 0073 73 2
cert_check_3 0074 0000 74 0 2 2
cert_block_6 0074 74 2
cert_check_3 0075 0000 75 0 2 2
cert_block_6 0075 75 2
cert_check_3 0076 0000 76 0 2 2
cert_block_6 0076 76 2
cert_check_3 0077 0000 77 0 2 2
cert_block_6 0077 77 2
cert_check_3 0078 0000 78 0 2 2
cert_block_6 0078 78 2
cert_check_3 0079 0000 79 0 2 2
cert_block_6 0079 79 2
cert_check_3 0080 0000 80 0 2 2
cert_block_6 0080 80 2
cert_check_3 0081 0000 81 0 2 2
cert_block_6 0081 81 2
cert_check_3 0082 0000 82 0 2 2
cert_block_6 0082 82 2
cert_check_3 0083 0000 83 0 2 2
cert_block_6 0083 83 2
cert_check_3 0084 0000 84 0 2 2
cert_block_6 0084 84 2
cert_check_3 0085 0000 85 0 2 2
cert_block_6 0085 85 2
cert_check_3 0086 0000 86 0 2 2
cert_block_6 0086 86 2
cert_check_3 0087 0000 87 0 2 2
cert_block_6 0087 87 2
cert_check_3 0088 0000 88 0 2 2
cert_block_6 0088 88 2
cert_check_3 0089 0000 89 0 2 2
cert_block_6 0089 89 2
cert_check_3 0090 0000 90 0 2 2
cert_block_6 0090 90 2
cert_check_3 0091 0000 91 0 2 2
cert_block_6 0091 91 2
cert_check_3 0092 0000 92 0 2 2
cert_block_6 0092 92 2
cert_check_3 0093 0000 93 0 6 6
cert_block_6 0093 93 6
cert_check_3 0094 0000 94 0 6 6
cert_block_6 0094 94 6
cert_check_3 0095 0000 95 0 6 6
cert_block_6 0095 95 6
cert_check_3 0096 0000 96 0 6 6
cert_block_6 0096 96 6
cert_check_3 0097 0000 97 0 6 6
cert_block_6 0097 97 6
cert_check_3 0098 0000 98 0 6 6
cert_block_6 0098 98 6
cert_check_3 0099 0000 99 0 6 6
cert_block_6 0099 99 6
cert_check_3 0100 0000 100 0 6 6
cert_block_6 0100 100 6
cert_check_3 0101 0000 101 0 2 2
cert_block_6 0101 101 2
cert_check_3 0102 0000 102 0 2 2
cert_block_6 0102 102 2
cert_check_3 0103 0000 103 0 2 2
cert_block_6 0103 103 2
cert_check_3 0104 0000 104 0 2 2
cert_block_6 0104 104 2
cert_check_3 0105 0000 105 0 2 2
cert_block_6 0105 105 2
cert_check_3 0106 0000 106 0 2 2
cert_block_6 0106 106 2
cert_check_3 0107 0000 107 0 2 2
cert_block_6 0107 107 2
cert_check_3 0108 0000 108 0 2 2
cert_block_6 0108 108 2
cert_check_3 0109 0000 109 0 2 2
cert_block_6 0109 109 2
cert_check_3 0110 0000 110 0 2 2
cert_block_6 0110 110 2
cert_check_3 0111 0000 111 0 2 2
cert_block_6 0111 111 2
cert_check_3 0112 0000 112 0 2 2
cert_block_6 0112 112 2
cert_check_3 0113 0000 113 0 6 6
cert_block_6 0113 113 6
cert_check_3 0114 0000 114 0 6 6
cert_block_6 0114 114 6
cert_check_3 0115 0000 115 0 6 6
cert_block_6 0115 115 6
cert_check_3 0116 0000 116 0 6 6
cert_block_6 0116 116 6
cert_check_3 0117 0000 117 0 6 6
cert_block_6 0117 117 6
cert_check_3 0118 0000 118 0 6 6
cert_block_6 0118 118 6
cert_check_3 0119 0000 119 0 6 6
cert_block_6 0119 119 6
cert_check_3 0120 0000 120 0 6 6
cert_block_6 0120 120 6
cert_check_3 0121 0000 121 0 6 6
cert_block_6 0121 121 6
cert_check_3 0122 0000 122 0 6 6
cert_block_6 0122 122 6
cert_check_3 0123 0000 123 0 6 6
cert_block_6 0123 123 6
cert_check_3 0124 0000 124 0 6 6
cert_block_6 0124 124 6
cert_check_3 0125 0000 125 0 6 6
cert_block_6 0125 125 6
cert_check_3 0126 0000 126 0 6 6
cert_block_6 0126 126 6
cert_check_3 0127 0000 127 0 6 6
cert_block_6 0127 127 6
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
cert_check_3 0128 0000 128 0 6 6
cert_block_6 0128 128 6
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0
cert_metadata_validity_11 0000 0 16 16
cert_metadata_validity_11 0016 16 32 16
cert_metadata_validity_11 0032 32 48 16
cert_metadata_validity_11 0048 48 64 16
cert_metadata_validity_11 0064 64 80 16
cert_metadata_validity_11 0080 80 96 16
cert_metadata_validity_11 0096 96 112 16
cert_metadata_validity_11 0112 112 128 16
cert_metadata_validity_11 0128 128 129 1
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 129
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 129
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 129
  metadata_validity_0096
  (FiniteChecks.interval_append (validity) 112 128 129
  metadata_validity_0112
  metadata_validity_0128))))
cert_metadata_symmetry_11 0000 0 16 16
cert_metadata_symmetry_11 0016 16 32 16
cert_metadata_symmetry_11 0032 32 48 16
cert_metadata_symmetry_11 0048 48 64 16
cert_metadata_symmetry_11 0064 64 80 16
cert_metadata_symmetry_11 0080 80 96 16
cert_metadata_symmetry_11 0096 96 112 16
cert_metadata_symmetry_11 0112 112 128 16
cert_metadata_symmetry_11 0128 128 129 1
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 129
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 129
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 129
  metadata_symmetry_0096
  (FiniteChecks.interval_append (symmetry) 112 128 129
  metadata_symmetry_0112
  metadata_symmetry_0128))))
cert_metadata_normalizers_3 4
cert_metadata_root_3
end Papers.RationalityTen.RootedCanonical.RootedSixBase04.S4T0

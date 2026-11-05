module
prelude
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification
public import SmallSubsumedForest08Packed000
public import SmallSubsumedForest08Packed001
public import SmallSubsumedForest08Packed002
public import SmallSubsumedForest08Packed003
public import SmallSubsumedForest08Packed004
public import SmallSubsumedForest08Packed005
public import SmallSubsumedForest08Packed006
public import SmallSubsumedForest08Packed007
public import SmallSubsumedForest08Packed008
public import SmallSubsumedForest08Packed009

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 61753
abbrev leafCount : Nat := 257
def widths : PackedRawNatGrowth.Widths := ⟨12,16,11,9⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 250
 (.branch 100
 (.branch 50
 nodeBlocks000
 nodeBlocks001)
 (.branch 150
 nodeBlocks002
 (.branch 200
 nodeBlocks003
 nodeBlocks004)))
 (.branch 350
 (.branch 300
 nodeBlocks005
 nodeBlocks006)
 (.branch 400
 nodeBlocks007
 (.branch 450
 nodeBlocks008
 nodeBlocks009))))
def counterTable : Table Nat :=
(.branch 250
 (.branch 100
 (.branch 50
 nodeCounters000
 nodeCounters001)
 (.branch 150
 nodeCounters002
 (.branch 200
 nodeCounters003
 nodeCounters004)))
 (.branch 350
 (.branch 300
 nodeCounters005
 nodeCounters006)
 (.branch 400
 nodeCounters007
 (.branch 450
 nodeCounters008
 nodeCounters009))))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)

def leafTable : Table Nat :=
(.branch 128
 (.branch 64
 (.branch 32
 (.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf 0x1888e4cd2c69e57e4d84ae010004000a)
 (.leaf 0x1a957bf419334e60ccc6364ee36e00e002000c))
 (.branch 3
 (.leaf 0x186f83d44725ae64d445ee4ec36e00c004000c)
 (.leaf 0x188d36ce84d2c69654e440010004000a)))
 (.branch 6
 (.branch 5
 (.leaf 0x1a8d45725f0dee18d42ab666453000c002000c)
 (.leaf 0x1a637bf44b2b7062e60d145ee4e600c002000c))
 (.branch 7
 (.leaf 0x1a817bf42d2bce60ccca3a6364ee00c002000c)
 (.leaf 0x1a7d87183f27ee44ccca6464e4ee00c002000c))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf 0x1a817c5289022e86ccca1064e4ee00c002000c)
 (.leaf 0x187183f44728508ce4cd2c5ee4e600c002000c))
 (.branch 11
 (.leaf 0x17c57af44b289038e80d2c5ee4e600c002000c)
 (.leaf 0x1a8d45708ae48d72a666945302ca016002000c)))
 (.branch 14
 (.branch 13
 (.leaf 0x17c578544f036e80d5c5dc4fe2e2016002000c)
 (.leaf 0x1a857c4ff8e86cb4a1267e5062e2016002000c))
 (.branch 15
 (.leaf 0x1a7b87183f3aee44ccc64e4ee2b2016002000c)
 (.leaf 0x1a777f7383024e88ccc6664ee2ca016002000c)))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf 0x1a7b7f142f3fce48ccc6364ee2ca016002000c)
 (.leaf 0x1a8b645454e78ce463a4ee36e31201e002000c))
 (.branch 19
 (.leaf 0x17c77af418e80d2c5f44ec36e312018004000c)
 (.leaf 0x182976344ce7ace46424ee36e31201e002000c)))
 (.branch 22
 (.branch 21
 (.leaf 0x1a1d742e76d745d854c4b448a28407c006000c)
 (.leaf 0x144322ee62d14c1e8647de62016802c00c000c))
 (.branch 23
 (.leaf 0x19b7798dfed6ca026085ce44625407c006000c)
 (.leaf 0x17ef78cdeacacc8687265a3f032c02c002000c))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf 0x1a437fae5cd147b66c24ec3462fe080004000c)
 (.leaf 0x17f370540ce7ed445ec54e46a2fa148004000c))
 (.branch 27
 (.leaf 0x1a4f7c9022e86d146064ec346312068004000c)
 (.leaf 0x188536ee6ad44bb85f054e494284148004000c)))
 (.branch 30
 (.branch 29
 (.leaf 0x1a5964f422e78ce463a4ee348312142002000c)
 (.leaf 0x1a9977b37edced2c69857e470268148004000c))
 (.branch 31
 (.leaf 0x1a6d6d3386e02cb46b053641c2f811a002000c)
 (.leaf 0x19bd70541ce7ecfc63a4ee3482fa106002000c))))))
 (.branch 48
 (.branch 40
 (.branch 36
 (.branch 34
 (.branch 33
 (.leaf 0x17f97b7416e50ccc66c4ee39c328002000b)
 (.leaf 0x17fb734e20cb4c5869e53636c2fc156002000c))
 (.branch 35
 (.leaf 0x19bd6f1120e46d945da52e3c22b407a002000c)
 (.leaf 0x1789576e4acc6c888746723cc32e02c002000c)))
 (.branch 38
 (.branch 37
 (.leaf 0x136b15ce82cf2c828c87a26802b802a004000c)
 (.leaf 0x1a8b61ae18cb4c8e69a50637832e07a002000c))
 (.branch 39
 (.leaf 0x17c57b2e68cccc846544ee3f632c07a002000c)
 (.leaf 0x1a1d742e76d74c945d854c4d428407c006000c))))
 (.branch 44
 (.branch 42
 (.branch 41
 (.leaf 0x1a1d468fcce76bba66654c284212092066000c)
 (.leaf 0x1a5182b3d8e72d446064ec356312068004000c))
 (.branch 43
 (.leaf 0x1a1d74346ee76d745d854c45228407c006000c)
 (.leaf 0x13b336ae82cf6c828c46805c42b8016002000c)))
 (.branch 46
 (.branch 45
 (.leaf 0x185337ee04cccc9e80253641c2d2036002000c)
 (.leaf 0x186f83d446e64d445f44ec370302080004000c))
 (.branch 47
 (.leaf 0x18e9416e7ecf6c826b8578348300052002000c)
 (.leaf 0x17bf44ae68d14c526a24ec370330040004000c)))))
 (.branch 56
 (.branch 52
 (.branch 50
 (.branch 49
 (.leaf 0x1824fd6e0ecfcc8665651e41a31a06e002000c)
 (.leaf 0x17f93dae34d74c625dc5044d42d207c006000c))
 (.branch 51
 (.leaf 0x183737ce00cb4c56b12826536270036002000c)
 (.leaf 0x18ad3ace32caec508727d26b42a002c002000c)))
 (.branch 54
 (.branch 53
 (.leaf 0x13b3006de6d14ca4a687d86b416802c00c000c)
 (.leaf 0x17c3458d9ad12c2060e5964cc2ea066006000c))
 (.branch 55
 (.leaf 0x18ef5f2e82cf6c8268454839c334052002000c)
 (.leaf 0x1890e84d5c66c54c44233608a006000a))))
 (.branch 60
 (.branch 58
 (.branch 57
 (.leaf 0x18f35f3416e4acc66bc57839c338052002000c)
 (.leaf 0x1383346e4acc6c888706b25962ee016002000c))
 (.branch 59
 (.leaf 0x17bf44ae60d14ba65f44ec37033a080004000c)
 (.leaf 0x1a8561ae30cb4bbc6825064b033e016002000c)))
 (.branch 62
 (.branch 61
 (.leaf 0x1a4f61ce60d1460a4ec4da34633e080004000c)
 (.leaf 0x1a5361cde8cacbc068254e43233e052002000c))
 (.branch 63
 (.leaf 0x1a5361cde8cac8f068254443233e12e002000c)
 (.leaf 0x1a851dee2cd10a9896e8346c218002c00c000c)))))))
 (.branch 96
 (.branch 80
 (.branch 72
 (.branch 68
 (.branch 66
 (.branch 65
 (.leaf 0x19eb32b026e6ec7e5f05942541e009407a000c)
 (.leaf 0x1a877f6e5cccca3c6664ee3dc30c156002000c))
 (.branch 67
 (.leaf 0x1a537c8e42ce4a706364ee43033c142002000c)
 (.leaf 0x19e182ede2d44bc260e566486326068004000c)))
 (.branch 70
 (.branch 69
 (.leaf 0x1a77382e16d5cbee85c6c02e618002e016000c)
 (.leaf 0x1a4f882e72d44bb8608566486326068004000c))
 (.branch 71
 (.leaf 0x1a757ece5ccccc166b05363dc30c156002000c)
 (.leaf 0x188cdfad7264c5c44e030c14e00a000a))))
 (.branch 76
 (.branch 74
 (.branch 73
 (.leaf 0x19ed97579750108ae2ed825ee25202a002000c)
 (.leaf 0x1a5b425084e48d72a68694578282052002000c))
 (.branch 75
 (.leaf 0x17c970741d030e80d5c5de54629a052002000c)
 (.leaf 0x1a93156e2ecf2b9c96e91c6242ce02a004000c)))
 (.branch 78
 (.branch 77
 (.leaf 0x17c37af1b2e80cda96863c4e4312130006000c)
 (.leaf 0x1a537c8f7ae86caca1467e54e29a052002000c))
 (.branch 79
 (.leaf 0x1a937a5576de6d6aa6c99064e1b002c00c000c)
 (.leaf 0x17c970710ae80d528ea5de54c29a07a002000c)))))
 (.branch 88
 (.branch 84
 (.branch 82
 (.branch 81
 (.leaf 0x1a835e12b0e12d90ac099663a1b002c00c000c)
 (.leaf 0x1a1f94d7b76b308ae2ed6a4fe252034002000c))
 (.branch 83
 (.leaf 0x1a578632dd036e74d5c61e4fe252142002000c)
 (.leaf 0x1891342e84d526665461da13a00e000a)))
 (.branch 86
 (.branch 85
 (.leaf 0x1a5d7c935f10adfad5a5d651629a142002000c)
 (.leaf 0x1a498f560b562e44d0e60626a1620de02a000c))
 (.branch 87
 (.leaf 0x1a497f0db4cacc9ac3068254e286052002000c)
 (.leaf 0x1a457fb0b7024e88d0a61e4e628212e002000c))))
 (.branch 92
 (.branch 90
 (.branch 89
 (.leaf 0x1a457fade4cacbc085e6c254e286052002000c)
 (.leaf 0x1a178eb89d86adcccc464e546256052002000c))
 (.branch 91
 (.leaf 0x1a498a3838dcccacbe867e54e26e052002000c)
 (.leaf 0x19bd969799554dfed6c60625217a0de02a000c)))
 (.branch 94
 (.branch 93
 (.leaf 0x19b988ce14d0cba486e6bc5ae254068004000c)
 (.leaf 0x1a937c0e14d0cb9c99860c5042e6080004000c))
 (.branch 95
 (.leaf 0x1a557fb204fa4e56cb469453629e156002000c)
 (.leaf 0x1a817c5289022e86ccc64e4ee256142002000c))))))
 (.branch 112
 (.branch 104
 (.branch 100
 (.branch 98
 (.branch 97
 (.leaf 0x19bd7fb7ad40ee7ecfc6364ee282066002000c)
 (.leaf 0x1a8b896e74d2c69654e2ca06e004000a))
 (.branch 99
 (.leaf 0x1a97a2d7f1412e48ccc6364ee282066002000c)
 (.leaf 0x1a7f87580ae2ccb4a8c6ae51e252142002000c)))
 (.branch 102
 (.branch 101
 (.leaf 0x1a1989b868de2d44b0c5ec54e2e2148004000c)
 (.leaf 0x1a97a2d854e42ce4be8638506282066002000c))
 (.branch 103
 (.leaf 0x1a817bd433292e78ce464e4ee256142002000c)
 (.leaf 0x19e589d86adfacccc1a65651e26a066002000c))))
 (.branch 108
 (.branch 106
 (.branch 105
 (.leaf 0x19bb85f786e44cccc1867053626a066002000c)
 (.leaf 0x1891340e82d4467e54e2b614e004000a))
 (.branch 107
 (.leaf 0x1a1f8e773adc8cd89426b05a4286142002000c)
 (.leaf 0x19e1918df8d08c788ee6985c026e156002000c)))
 (.branch 110
 (.branch 109
 (.leaf 0x1a758eee70d80c1e96e6b05302fe052006000c)
 (.leaf 0x1a1b6bce88d98be29be6385ac2cc142008000c))
 (.branch 111
 (.leaf 0x1a7d22ce6ed7ec1e9ea6822ce1b002e016000c)
 (.leaf 0x1a838ed280e0ed1e9c065232c1a80b802c000c)))))
 (.branch 120
 (.branch 116
 (.branch 114
 (.branch 113
 (.leaf 0x17b6e2ed6ab689ea68a1f802e00e000a)
 (.leaf 0x17195f2e72cf6c98b7491c54c2a0036002000c))
 (.branch 115
 (.leaf 0x179d5cadb6d54b80a9897067618002c00c000c)
 (.leaf 0x144d0d6e16d8abeab7a6bc5301c805400e000c)))
 (.branch 118
 (.branch 117
 (.leaf 0x1a49822dcccb2ca0bfe68056625a068004000c)
 (.leaf 0x1a9b7bce14cb4c52b446b251e25807a002000c))
 (.branch 119
 (.leaf 0x1a498a3838dcccb2be867e54e25a068004000c)
 (.leaf 0x17f7024e88cc2b8c99866c4e421212e012000c))))
 (.branch 124
 (.branch 122
 (.branch 121
 (.leaf 0x1a937a552515ae16d5c6242e01ac0ea02a000c)
 (.leaf 0x182f7593aae66cfcbc265651e27006e002000c))
 (.branch 123
 (.leaf 0x1894e44d14c8c6b657e2b8074004000a)
 (.leaf 0x1a891e0e44d0ec8ca6e6b259616805a00c000c)))
 (.branch 126
 (.branch 125
 (.leaf 0x18233aee00cb4c94c6265651e27006e002000c)
 (.leaf 0x1783416e7ecf6c8091057c2cc2120b8036000c))
 (.branch 127
 (.leaf 0x184f19ce5ad92c1caba6865602e8080004000c)
 (.leaf 0x18af7d4e5ad44c20b8e5f44ec2e8080004000c))))))))
 (.branch 192
 (.branch 160
 (.branch 144
 (.branch 136
 (.branch 132
 (.branch 130
 (.branch 129
 (.leaf 0x1999600e5acf6b388c86865602a0086002000c)
 (.leaf 0x17f702ae2ad66b3a9ec5dc50433007a008000c))
 (.branch 131
 (.leaf 0x18a15d8e5acf6b8e96c94663c2a002c002000c)
 (.leaf 0x18a7804e14cb4c50b106b653625807a002000c)))
 (.branch 134
 (.branch 133
 (.leaf 0x13ab11ee5ed92c22b386b451827007a002000c)
 (.leaf 0x15f2e72d3ebae99a68e2e802e004000a))
 (.branch 135
 (.leaf 0x188ce5cd14ba66be5662b8086004000a)
 (.leaf 0x17c5440e78d2cbeebae68e4ec2e8040004000c))))
 (.branch 140
 (.branch 138
 (.branch 137
 (.leaf 0x198737310ce52d2291c69a5442a0126002000c)
 (.leaf 0x1417084e46d8abf0ba46bc578270052002000c))
 (.branch 139
 (.leaf 0x19870e4e5ed82ba68746be560270086002000c)
 (.leaf 0x13ab36ae82cf6c828c46805c427007a002000c)))
 (.branch 142
 (.branch 141
 (.leaf 0x17eb3db36ee6ad44bb068254e2d015c004000c)
 (.leaf 0x17c17854192f8e80ce463450627015e002000c))
 (.branch 143
 (.leaf 0x1789578e44cc6b949c28f467227002c002000c)
 (.leaf 0x17c97aedfccb4c52b406ba51e25807a002000c)))))
 (.branch 152
 (.branch 148
 (.branch 146
 (.branch 145
 (.leaf 0x1a79828e2ccb4bba8626aa51e25806e002000c)
 (.leaf 0x199d5d5416e7ad56bea66c2a01c402c018000c))
 (.branch 147
 (.leaf 0x17f746f146e62cc29c266c4e433012e008000c)
 (.leaf 0x19938990e2e62d548c866c55e2a0002000b)))
 (.branch 150
 (.branch 149
 (.leaf 0x1895036e04d54c8c8f466e5c625807a002000c)
 (.leaf 0x17f7184e34d6ac949fc5dc5042d207a008000c))
 (.branch 151
 (.leaf 0x193988f114e7ad22bec69c54e2a0052002000c)
 (.leaf 0x1891038e02d3cbbc9d86865ce270052002000c))))
 (.branch 156
 (.branch 154
 (.branch 153
 (.leaf 0x188f4bd3dce7ace6bec69c54e2a0052002000c)
 (.leaf 0x17f7609440e34d8e96a5dc5042d207a008000c))
 (.branch 155
 (.leaf 0x1859440e7ad26bea98462459e2e8040004000c)
 (.leaf 0x18813dd0cae7ad62be469c5002a0156002000c)))
 (.branch 158
 (.branch 157
 (.leaf 0x18853dee32caec74bd269c54e2a0052002000c)
 (.leaf 0x18af7d5410e62cccc1866c4ee2a0002000b))
 (.branch 159
 (.leaf 0x1446f32e50d3ec509c068a5342d0040004000c)
 (.leaf 0x18ed5c8e82cf6c866543e83341c40b802c000c))))))
 (.branch 176
 (.branch 168
 (.branch 164
 (.branch 162
 (.branch 161
 (.leaf 0x18e7108e7ed6ac227f06b850028807a002000c)
 (.leaf 0x140d15ce4ed8abea79c6885782b8080004000c))
 (.branch 163
 (.leaf 0x18e73dce7ecf6c788f06b85a8288156002000c)
 (.leaf 0x18ed440e7ed3ec5096e6b85302d0054004000c)))
 (.branch 166
 (.branch 165
 (.leaf 0x18e781eddccf4c788f06b65a828e156002000c)
 (.leaf 0x18bd880e6cd54c209986b451831e052006000c))
 (.branch 167
 (.leaf 0x188ae84d529ec66c54c336088008000a)
 (.leaf 0x1890e3cd0c9c26b458c2ee13a004000a))))
 (.branch 172
 (.branch 170
 (.branch 169
 (.leaf 0x1a4f882e72d44bb8b566085662f2068004000c)
 (.leaf 0x1a757ece5ccccc16ab26b053627a156002000c))
 (.branch 171
 (.leaf 0x1a5182b320e72d44be86064ec2be068004000c)
 (.leaf 0x1a4f883320e72d44bb86085662be068004000c)))
 (.branch 174
 (.branch 173
 (.leaf 0x170b3b934edf0c4c68051e2b816a08e07a000c)
 (.leaf 0x17fb220dfccb4c58b0869e53628e156002000c))
 (.branch 175
 (.leaf 0x17c936cdfad5ac52b405dc51c33607a008000c)
 (.leaf 0x1a1d7b3442e68bba6085962e21c8092066000c)))))
 (.branch 184
 (.branch 180
 (.branch 178
 (.branch 177
 (.leaf 0x1888e12d5cbae6645ae30a152006000a)
 (.leaf 0x1a757ed274e5ccccc166b053628e156002000c))
 (.branch 179
 (.leaf 0x141d030e78d5cbc0b026845482aa052002000c)
 (.leaf 0x13e8fb2e76caebecb0669c54e292052002000c)))
 (.branch 182
 (.branch 181
 (.leaf 0x144ae8ae60d28ba696c5f44ec33a07a008000c)
 (.leaf 0x137736ce02d28c5289869a54e33607a008000c))
 (.branch 183
 (.leaf 0x1890e72d44b8068454e2f2086004000a)
 (.leaf 0x17ed70f3e8dd869c50646e32816a08e07a000c))))
 (.branch 188
 (.branch 186
 (.branch 185
 (.leaf 0x1a5961d422e60d0a60a4e632a17a12e01a000c)
 (.leaf 0x17c97b3418e68d0a60c4e632a17a12e01a000c))
 (.branch 187
 (.leaf 0x17fb70f41ae62d0a6124e632a17a12e01a000c)
 (.leaf 0x197f418e7ed6ebb86b85782881c408a018000c)))
 (.branch 190
 (.branch 189
 (.leaf 0x18e73e4e7ecf6c866b85a82d017e07a016000c)
 (.leaf 0x18c55cb3e6e7acde67654a2f217e07a016000c))
 (.branch 191
 (.leaf 0x18c1522df4cb069c5923c62a61d80e0082000c)
 (.leaf 0x18bd8913e6e7ad526765462f2192052016000c)))))))
 (.branch 224
 (.branch 208
 (.branch 200
 (.branch 196
 (.branch 194
 (.branch 193
 (.leaf 0x18bf5cae3ccaec886b45902ee17e07a016000c)
 (.leaf 0x18c35f4e84cdec5269c54833616607a01a000c))
 (.branch 195
 (.leaf 0x18c13eadf0cc4c5662a5923301d80b6040000c)
 (.leaf 0x18c310ae80d527486ba5482a016608407a000c)))
 (.branch 198
 (.branch 197
 (.leaf 0x1a117fce2cd0c7b66c24fe2ce16412e07c000c)
 (.leaf 0x1a1d7caff8e86d0c6064fe2e216412e066000c))
 (.branch 199
 (.leaf 0x1a1d1dce2cd108346c24e828617a12e07c000c)
 (.leaf 0x17c5022db2d96c845d45642b4228142064000c))))
 (.branch 204
 (.branch 202
 (.branch 201
 (.leaf 0x1a1f258e74d567be66852a25617a13407e000c)
 (.leaf 0x18bf893318e6cd5466655e25817a0de052000c))
 (.branch 203
 (.leaf 0x195b7fb272dfad6c5d652e28c208142056000c)
 (.leaf 0x19272c6df2d86bbe5f252e2fc1dc148052000c)))
 (.branch 206
 (.branch 205
 (.leaf 0x17c72c2d9ccc4c5664c5963341b2144054000c)
 (.leaf 0x1a1b8ef88ee72d6a64e5462ae1be066052000c))
 (.branch 207
 (.leaf 0x17c77af40ee80d225ee4e629a19214a130000c)
 (.leaf 0x1a118e4e40d50c546b05a82ce1c607c07a000c)))))
 (.branch 216
 (.branch 212
 (.branch 210
 (.branch 209
 (.leaf 0x1a458c11a8df6d0660a4ea32a1dc13607c000c)
 (.leaf 0x1a7994ce70d80c186685302b417c15607a000c))
 (.branch 211
 (.leaf 0x1a43924e88d98bf06985782fc194080052000c)
 (.leaf 0x1a4f9852fee86d9660859026c1c00c2080000c)))
 (.branch 214
 (.branch 213
 (.leaf 0x1a518f2e70d80c226b057828617a0cc052000c)
 (.leaf 0x1892e2cd2469658e2c41d415013a000a))
 (.branch 215
 (.leaf 0x1a1f565258e74d5666853825617a13407e000c)
 (.leaf 0x1a1f258e74d569586685cc25617a13407e000c))))
 (.branch 220
 (.branch 218
 (.branch 217
 (.leaf 0x1a2761edd0cc4c2a66a54632e19a12e052000c)
 (.leaf 0x18c55cb342e84cde66654a25817e0e007a000c))
 (.branch 219
 (.leaf 0x1a8b61ae18caac8e69a50632e1e207a052000c)
 (.leaf 0x18c55cae2cd10b7c6be5182ba17c07c07a000c)))
 (.branch 222
 (.branch 221
 (.leaf 0x18c55cae74cdeb8067654a28817e07c07a000c)
 (.leaf 0x17cb789188e38d0c60c4fe32a19413012e000c))
 (.branch 223
 (.leaf 0x17cb785188e80cda63e4fc2e21c613012e000c)
 (.leaf 0x17cb784e04cc2c206ba51e2e61c212e052000c))))))
 (.branch 240
 (.branch 232
 (.branch 228
 (.branch 226
 (.branch 225
 (.leaf 0x18c12c4dbcd58c246224fe3361dc0e4052000c)
 (.leaf 0x185f2c8df4cc4bbe6ae5962d016a0e0054000c))
 (.branch 227
 (.leaf 0x17c76e0df0cac8ee68655c3141b2130082000c)
 (.leaf 0x17cb788e38d0cc2060c4fe32c1fa12e052000c)))
 (.branch 230
 (.branch 229
 (.leaf 0x17cb788dd2cc4c2067254632e19a12e052000c)
 (.leaf 0x17c57b2e1acaac846a250632e1e207a052000c))
 (.branch 231
 (.leaf 0x17c57aedbacacc846ba56631618207a052000c)
 (.leaf 0x17c5788e38caac8868450632c1fa07a052000c))))
 (.branch 236
 (.branch 234
 (.branch 233
 (.leaf 0x17c77b2e68cc2c526544ee32c22a07c054000c)
 (.leaf 0x17c9706e80d528ec5de54c29c24208407a000c))
 (.branch 235
 (.leaf 0x198f8950bae4cd8463c57627016612e07a000c)
 (.leaf 0x19677c71bee4cd225f44e631a1ac130082000c)))
 (.branch 238
 (.branch 237
 (.leaf 0x17c740ce4cd229585f44e631a248130082000c)
 (.leaf 0x1a677c72bae1acb467e5063141b20e0082000c))
 (.branch 239
 (.leaf 0x18bf89119ce34d9263e58e25817e0b607a000c)
 (.leaf 0x188d38336ce84d2c69654e27016807a000b)))))
 (.branch 248
 (.branch 244
 (.branch 242
 (.branch 241
 (.leaf 0x1891378e74d5cb8067654c28818007c07a000c)
 (.leaf 0x188d665418e7cd745e054c28218015607a000c))
 (.branch 243
 (.leaf 0x17c77b2e68cccc486544ee32c1b20e607c000c)
 (.leaf 0x188d418e62d0abb86be56633a18005a01a000c)))
 (.branch 246
 (.branch 245
 (.leaf 0x18ef88ee82d6ac1e6545463341ac052000b)
 (.leaf 0x195588ce0ad6c89a6565be2bc17c15607a000c))
 (.branch 247
 (.leaf 0x18c11b2df0cc8c4862a4ea3301dc0e607c000c)
 (.leaf 0x18f3860df2d6a8a260e58c2a41f413407e000c))))
 (.branch 252
 (.branch 250
 (.branch 249
 (.leaf 0x1892e6cd5466c55e31e1c413a088000a)
 (.leaf 0x191b442e66d3ec4a6a05302b816415607a000c))
 (.branch 251
 (.leaf 0x18e53dae7ed3ec546b85a82d01c607c07a000c)
 (.leaf 0x191b442e08d40c4a6424e831a1ac15607a000c)))
 (.branch 254
 (.branch 253
 (.leaf 0x18e53dae20d40c5465a54a33222407c07a000c)
 (.leaf 0x18f340ce50d70c2268a5003321f4080052000c))
 (.branch 255
 (.leaf 0x18b9890e54d0ac206b657e30617c080052000c)
 (.branch 256
 (.leaf 0x1891378e84d5cc2066c54c33618007a01a000c)
 (.leaf 0x184781541ae7cd7465454c28818007c07a000c))))))))))
def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList 12 (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1

def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 7
  | 3 => 2
  | 4 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1440 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck RootedSmallCache.candidateMasks RootedSmallCache.badMasks
        RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
        RootedSmallGeneratorWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.Small.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08

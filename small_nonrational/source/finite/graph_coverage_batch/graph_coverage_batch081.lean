module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch081
open Papers.RationalityTen GraphCandidateCoverage

def candidate08100 : Description := ⟨88, ⟨13, 0x16a7aa4d19a83740284bbdbde66ea072e3755b4cd606a0349d8bebff5b4ac0544a9da4e0a5d522288f42ea0b8fc67ca3be1cd0dfe6e93681a0ccd465131e948ca1e4aa248117c85c4101fd0f886ca31c17f8b9856e29e141887c3dc1d40d004f82460db03f01c00b605a02b015409004601e80e0048023011007c03c01d00c005002200e006802c0120080018008002000⟩⟩
theorem candidate08100_checked : Checked candidate08100 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628566790144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08101 : Description := ⟨91, ⟨13, 0xb58d27e80b335893c25208efea7b1bcc5e0eeee75e3a8dcb4e3b6e93699b1cd5c69f34958ccbff53727bd37c978486a2750d68313f31f34efa74d3681a18cd064f3069698a424ef26191e08be4161ca0d946322b014d09f84a421d10387b83b41a10c405bc27812606d024c10007e03501a40ce06502b015407003201880b805202000f007401e00e0068024010007002000c004000⟩⟩
theorem candidate08101_checked : Checked candidate08101 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628671926528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08102 : Description := ⟨92, ⟨13, 0x16a79ffcd1a26909a825bf9dee4f407853afdd4ce576eab699abed3b691317d7fea6e528a7bd37c975488a23d0ba82e3f19f28f026ff3681a10c746062d114889e04c625691ec8c44121fd0f886ca34d18d8bf45c82b514e0a0c4a421f10387b83ac19f0c305b427c12606c023411807002b015409004601c00c8062024011808803c01d00e006803201800a002c012008002000c004000⟩⟩
theorem candidate08102_checked : Checked candidate08102 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628684216320 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08103 : Description := ⟨92, ⟨13, 0x181eb58d6aaa8d4d1a4fd1a683d4058b1c49e1290817bb3cc5ddcea37393965c76dd76d33639ac6d3e692b1997feb05511275d37c978486a2750d68313f31f34efc7343809ba4da0681334193ca5e50f27792408be4151cb0d9462e2be14c89f84d61ee0ed069431016f09f848c1b407e03501a40ca06102b015406603201880b805201f00f007402800e0068024010007002800c004000⟩⟩
theorem candidate08103_checked : Checked candidate08103 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628806127872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08104 : Description := ⟨81, ⟨13, 0x29253ff862c25209cfe77b6bcc1d40e576eab6994a29ef4df25c522289040a9f28f0276537f9b40d6c60a2d114a49e449022f90487c43651998acc538281129087c40e1ee0e9068c27c126050823411807003501a40b605a02b01540a804601c00c806202f016809804602200f007403801900a003801a00b004802000e0040018008002000⟩⟩
theorem candidate08104_checked : Checked candidate08104 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19632970858496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08105 : Description := ⟨94, ⟨13, 0x58f290b428a044b8a4e515088bc2fa13504b7f1bd1de46f0a7653afdd4ce266e9b6a5b04d5069bb18d804a8753aa94d3d49be4baa4510e682e3fb1f8cf9470d3699aa4cce64e30316a4a324c624e11ec8c442b20c8ec072236519d8c6c5fa2e415a8a5c50625210d081c3dc1c40cf86182da14408583c81ba0b105102740e80700330184078032018809004602200d00600180090040010006002⟩⟩
theorem candidate08105_checked : Checked candidate08105 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19636733216896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08106 : Description := ⟨99, ⟨13, 0xb525902b55546a31d0627ff33996ac8fe3b70f8856c2521090587fa3dd1eb6f42786bb79d84ea973d3985c90e136f23721b5ed5269cb48137c9ab44b21f50be7fb3e51e70f067653809b40cfe64029594489e849022f90c48303fa1cb0d946282d21620aac4fe26e11e086c3e21d80df86b830a16c0ad8508262108077835811c08d04601ac0d406901900c405a029011808803c01d00e006002800e0068024010007⟩⟩
theorem candidate08106_checked : Checked candidate08106 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19645985718848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08107 : Description := ⟨103, ⟨13, 0xa014ce65ab23f8edc3ee16109783f3da5ea0f35768ba81cdee5671db75db4cd5d6a0349d8c6bff5b4ac1544a9da4e0a6a112687a42f9fecf947993c01d94e026d034399a8ca263a3031688a4c50d27a130c92047822f90b08263fa1e48e586fc36518c0bfc5cc2cf15a0a6c4d62390f707543781a20ac04fc24a0db03281840b605a02b015405a029011808803c01d00d0064030014007803801a00a004802000c0050018008002000⟩⟩
theorem candidate08107_checked : Checked candidate08107 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19646004592640 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08108 : Description := ⟨91, ⟨13, 0xadbd2868112428edc25209cfe3768ba81cf2e47706b709b52d5e69eb4916cab05529a6f934a971486a17cff67ca3c99d84e6e71e3761b4cd746883339938c145a2248117c8544131fc0f2472c37e1b28c68566281135894840e1ee0de068c2b412408583c81b206a03481980c205b02d00f807803201880bc05c02d014808c04401900a003801a00a004802000e005002000c004001⟩⟩
theorem candidate08108_checked : Checked candidate08108 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19649744011264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08109 : Description := ⟨86, ⟨13, 0x50224771db894c252096fe3768ba81c1adc26d4b579a7ad245b2ac154a69be4baa434ff67ca39b9bb0da66883339938c746062d113d092045f2098f247603961bf0d9469831a15a8a0c4d625210387b83781a3092042c1e40d903b01d00d406903301840b605a01f00f006403101700a404602200d0064030014007003401800a004802000e005002000c004001⟩⟩
theorem candidate08109_checked : Checked candidate08109 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19649752334336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08110 : Description := ⟨99, ⟨13, 0xad5551a7ff23f8edc2521090587fa3d09dbcea973d3985c90e136f23721b5ed6469cb4816d2b054df26952e290d42f9fecf947973bf1d94e687013749b40d0a63a30316889e849022f90b08263fa1e48e586fc36518d0b4856229813f89b84aa23c10d88283e21d80df869830a16c0ad8508242108077835811a08c03501a406403101780b805a029011808803e01e00e807003401900c005001c00d0050024010007⟩⟩
theorem candidate08110_checked : Checked candidate08110 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19650280686080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08111 : Description := ⟨78, ⟨13, 0x526a2c912f857bf99e96ebb6b9b509a52cc7649ac755d2a8252927652208754311f94ec66b434e99b0ca660a2d19564a484f723b10bc7f037d1a48cc86323011740a6c4d6220103068831417109f82440fe06e02f81740ac05502a012008e03c01b00d404e02500f0074038019009804802000f004802000e0050018008002000⟩⟩
theorem candidate08111_checked : Checked candidate08111 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19657404776448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08112 : Description := ⟨79, ⟨13, 0xb6d525e73b14b89642bdffefcb7b23d5de68ebb71db631adcd42694ac114d29d948822690ea8653f29d34e0466c3299834ab252128593e88ec4161be8cc06323011740aec53e27e103073c3721a20c505c427809104782000dc06502f81780ac05502a011c06c034013809404001e00e807002601200780240100070018008002000⟩⟩
theorem candidate08112_checked : Checked candidate08112 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19657664790784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08113 : Description := ⟨82, ⟨13, 0x52da83536f8963dbdeacf3875f35c5a84d29663b24d608a6952b27652ea8c4447a1d90c47e13c09ba0d36684336194cc7a5be2d29628a8052328513cc8f43fa1f10e5c6963011740adc53c28310207503761a00c505c427c09103701b00be05602a815009004701b00d0050027012007803a01c00c004802201000580240100070018008002000⟩⟩
theorem candidate08113_checked : Checked candidate08113 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19657675259904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08114 : Description := ⟨87, ⟨13, 0xa4ed0062c31458994259fccf1d74f3959b78da56b9b505a52cc764b2c6d5d6a84537a94138091042ea11cf907803b41b98d9e6b434e99acca660a2d19564a5250c27913708ba42a2098ff46c83491990c686002e814d89ac4402060b884fc24a10d037817c0ba05b02a815008c03e01b80d404e0250118074038019009804802000e005002000e0050018008002000⟩⟩
theorem candidate08114_checked : Checked candidate08114 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19659485151232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08115 : Description := ⟨96, ⟨13, 0x149aa004b524851918b0c51625f0ae84abf99da4e9f72b3705b48d736a134a198ec9660baff97cab6555daa114dea524ec26fd2208623fe1f24f007633759b38d6869d3361948c145a32ac94a4a184f724891dc8bc42a2098fe079237c1b18d2466431a1808b9c53626b110081831413f09283d00be05d02d01580a803e01e00d404e0250110078038019009804802000d005002400e0050018008002000⟩⟩
theorem candidate08115_checked : Checked candidate08115 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19660525338624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08116 : Description := ⟨89, ⟨13, 0x2a914b2a0ed0063bb1638a3c2ca12cf3374f3761b4ad746a0b4a598ec5f5daac09506a6c4eaa70122087a42e9f94f9077b3811b98d9e69e34119acca663d2df1694b1452328791e88ba42e2080e5c6f63641a58ccc62e3001740a0c4d62200ea06f02e210d03f017c0b605802a815009004601e80dc066027011808003a01c00c004802200e005802000e0050018008002000⟩⟩
theorem candidate08116_checked : Checked candidate08116 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19664048504832 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08117 : Description := ⟨93, ⟨13, 0x296b41da00c7da3831608a544ae16509678eba79c7cda56b9b505a52cc7631aed5636aeb542a9a94aa9d54e024410ea8473f29f20f007683731b3cd3a682335994cc7a5be2d29628a5050a27a13708f445d21490547f23b01bd8d9069833218b8c005d028313588802e215709f84340be05d02d81540a804701f00dc066027012808c03a01c00c004802000e006002000e0050018008002000⟩⟩
theorem candidate08117_checked : Checked candidate08117 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19672370003968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08118 : Description := ⟨87, ⟨13, 0xad553fe96141c9fc4b5228b0ac84741ede9af3a75d3aa1cdae5472036edb5cd736adb4f1a4c9ab42fa11cf8c79c3c19d94de26cc34e9940c805c12d416309ec49122e10c48303fc1bc0d886642fe1678abc52c28010607c03aa1870b8056027e12008503cc15e08d03781a40ce06602e815c0a804001b00c806202d012808c03c01c00800340100070030014002000⟩⟩
theorem candidate08118_checked : Checked candidate08118 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19676051021888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08119 : Description := ⟨105, ⟨13, 0x280339d99cca2e4e51f38ed47062bb144895c2be12cfe67a83aedd3ce3e6ec3695ae8d41694b31d8c6bb55ce2c75608aeb543a9b94aa9d94e024410f47e53e41da0e046cf34f19acca663a30316f0b4658a2ac9498a1a4f426191d88ba44621590487f23b01cb8df46c834c1998c646002e814d8a0c4d622010306f03441710ab84340be05b02c01540a8027011808003a01c00d0064030013009003c01c00c005802000e0050018008002000⟩⟩
theorem candidate08119_checked : Checked candidate08119 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19680825704448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08120 : Description := ⟨99, ⟨13, 0xaa2d2be8354048494206004fe97e6bdb1ea6f3775f3a89c7add86d1b5d1a7ed29663b18d76ab0453727653789a5493a4391ee89143c2184fc27cc3be9d9ce046e83669a78d0866932998f4b7c5a52c514a0a1e4f423d11747f43e21cb8ccc5d02cf1590a6450423911008103da1d50de06803121710ac04300dc06a02c01540a803601900bc05c028012008003a01c00c004801c00b004802000e0060028008002000⟩⟩
theorem candidate08120_checked : Checked candidate08120 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19681286045696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08121 : Description := ⟨86, ⟨13, 0x576a933419a03c9d6253090840c009fd2fcd79bba75d0ee6772738e1b88da86c6b5d1a7ed285b62aed3b09ba4871f88f8e7923b71b9cda469e34299a4ca45a521a90407ea3e21c00d8c6662e715f0a6451222010207b43781890a9048c2180f404c82600f007403501680b205802a010007a03201700a004402000f807002400e006802c0120070028008002000⟩⟩
theorem candidate08121_checked : Checked candidate08121 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19683869737216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08122 : Description := ⟨81, ⟨13, 0x2bc14968573f99cece51720b705ae8d41694331d732a554ec26a125291047aa17cf627943bd9d90dd66b734f19acca460a2d195648ee42a1fe8df066631a1800b9c57029b14089ac4402060de055424a10d07a026c0f007502f816c0b405802a010007c03d016809c0460220108080038019009804801c00d005802800e0050018008002000⟩⟩
theorem candidate08122_checked : Checked candidate08122 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19683937943552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08123 : Description := ⟨80, ⟨13, 0x139d937c4ae15cfe6728b8f9b82d746a0b4a198eb9952aa76122077b3b41bacd3c66b32918e8c0c5bc2d19628ab24f423b91187f237c1a60ccc6343001738a6c50626b110081837815709284341e809b03c01d80ea05f02d81680b005402000f807a027011808804001c00d0064030013009003801a00c005802800e0050018008002000⟩⟩
theorem candidate08123_checked : Checked candidate08123 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19683946266624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08124 : Description := ⟨84, ⟨13, 0x14079cec9ca2530907f23ae1d3ae70729b6a1ae8d3f694331d738a534dd2438fc47c73cd1df4da469e3349948c746062de168cb1455927a11dc88c42b2090f886c634c1998b9c56a2200f686f03461890ab84982180f403c01d00d406603001680b005402000f006402e014008804001c00d0064030013009003801a00c005802400e0050020008002000⟩⟩
theorem candidate08124_checked : Checked candidate08124 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19684012326912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08125 : Description := ⟨98, ⟨13, 0x501a73b2728f9c76a38312b848c12df3aeba74e39c1ca6e3e6e0369dae8d41693331d738b1d5822bad4aa9bb4baa31cfc87c63cd1df4ed06ea3689a78cd665031d1818b785a32c515649e847722310ac8243f91d80e5c6fa3641a60ccc6002b514189ac4a42050f606f03461700ab849821a0f303c01a40cc05b02c0150080031017008c04001c00d0064030013009003801a00c005802000e005002000c002000⟩⟩
theorem candidate08125_checked : Checked candidate08125 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19684045357056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08126 : Description := ⟨92, ⟨13, 0x1419a03c2421030027f4bf35e6ee9d7393939c7adc46d435d1a7ed28663ada55769d84dd269524e90e47ba184fc47c73cb9d9cdce6d234f1a14cd265231e96f8b4a58a27a10b88203fa1f10e006c63331738b3c56429914108e44402040f687543781890ac048c2180f404c01e00d405a02c015008003d01900bc05c028011008003e01c00c004801c00d005802400e0060028008002000⟩⟩
theorem candidate08126_checked : Checked candidate08126 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19684406607872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08127 : Description := ⟨87, ⟨13, 0xa50500a5a924289ac25dfccf1d7693a81cacdbc6d33501a4ec9660baff96cab1b527a83138291042ea11cff87ca3c01d8cdcc6d035c99a8ca260a2d194a4a184f226e12448ee45f215104c7f03c91b28d385fe2e614d89ac4402060f704fc24a0db03781740b605a02b015408c03e01e00dc04a023011007803a019009804001c00d00500240100050018008002000⟩⟩
theorem candidate08127_checked : Checked candidate08127 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19692720816128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08128 : Description := ⟨87, ⟨13, 0xaa2d27e905437a02cbb624f094823bff5e62eee751b969c76dbe6d33639af8d3e692aff9608a3b4f826f92f090e435a128ffe7cd3be9d34e046e83681a68cd064f30694b0a204ef23b917c82c37d1b28cc056029a13f09483dc1da0df06202de13c09303680fc06a034819c0ca06002b015406803201880b805002000f007402600e0068024010007002000c004000⟩⟩
theorem candidate08128_checked : Checked candidate08128 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19693096435968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08129 : Description := ⟨90, ⟨13, 0x4ffe3b513488bc33213504b7a03a99caedbe6d335eda76d2264b305d7fcb04528a8ed3e09be4baa2510f685d3f11f28f026e83681a6cc746062de168ca864f026f92b49284622090fe87c43971be8d9469a32f17e8b9056a29c14189483dc1d60de86182da13e093036011a08c03001580aa04601a00c8062028011808803c01d00e0068032018009802c012008002000c004000⟩⟩
theorem candidate08129_checked : Checked candidate08129 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19693108725760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08130 : Description := ⟨86, ⟨13, 0x55228474029784776171097799ba81c46dd86d33501a4ec5f60aada5604a254e9270522087a42e9f80f9477b3a69c08dcc6d034399a8ca263d2df1694a4650f25511d48be42e2080fe87c43971bd8d946382ff1730a0c4d62200f707503780db03f016c0b405802b015409004602080f406e023011008003c01d00c004401c00d00580240100050018008002000⟩⟩
theorem candidate08130_checked : Checked candidate08130 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19697284169728 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08131 : Description := ⟨90, ⟨13, 0x5ac6cc7545a4fd08a80b2f0893c2521030027f4bdd9e62eee7623a8dc76e236ec3699b1cd3e692b199608a6e4ea26f92f090e44ea1ad0627de3e69df4e9a7023741b40d0c6683279694a5e50f27791d48be3e21cb8d946662be14c89f84d622010207b83b41a50c405bc1b407e03501a40ca05802b015408203201880b805002000f007401c00d0058024010007002800c004000⟩⟩
theorem candidate08131_checked : Checked candidate08131 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19697391386880 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08132 : Description := ⟨89, ⟨13, 0x27ff34697c476a2690b784d3f99e80ec3753388dbb0da669db4898bec1558229b94a29d44df24410f485d3f01f28e9a7023681a78c746062de168ca444f026312b48e64622090fe87c43971be8d9469a31b17e8b90536283135888040c1ee0eb069030c16d06c023411805802b015409004602080c8062023011008003c01d00e0068032018009802c012008002800c004000⟩⟩
theorem candidate08132_checked : Checked candidate08132 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19697401595904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08133 : Description := ⟨94, ⟨13, 0x5962a8b4929ffcbb63b512784a42120b100a7f8bddde5aef4762baa5cc8e487163785b96daf6ccb5f5a72d2058226f92f090e44ba168fc47ca3be9d34e046e83681a78c1a5a329613bc8ee45f2090f8872e37d1b28ccc58229814789b84aa22310107c43c01bf0d306142d813a09484201de0d6050823411807e03501a406403101700a0046022010007803a01c00c804c01c00d0058024010007⟩⟩
theorem candidate08133_checked : Checked candidate08133 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19701686076160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08134 : Description := ⟨90, ⟨13, 0x590a7ff2df8f9c2de134fe67ae3c8ddb0ec375338e5b4cd7869db4898c6bfc58eaa1d4a69d44df24410ea8473fe1f80f947633681a74c746062de168ca124df26312508e64622158ec06fa36519a0c6c5fa2e414d8a0c4d622010307b83701a40c305b42ae13f06c023411807402b015408e04101e00c8062025011808803c01d00e00680320180098030012008002800c004000⟩⟩
theorem candidate08134_checked : Checked candidate08134 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19705723095040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08135 : Description := ⟨97, ⟨13, 0x2c7f5aaa58505e7ff2d491fc5161590948424162014ff17af3d09e4cedb762baa5cf4e61724384db6cdaf6c03591a72d204df26ad25891342fa11cff87ca3ce1e0ceca6e33681a74c805c12d413d09b849122f90c48303fa1bc0d946642d21620aac4fe26e11e088c4241f10ec06dc30a16c0ad8508262108077835812408d04601bc0d406901900c405a025011808803c01d00e006002000e0068024010007⟩⟩
theorem candidate08135_checked : Checked candidate08135 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19710410228288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08136 : Description := ⟨97, ⟨13, 0x2bc75b7ab4d542943424a0449d63ed1dd894c2521030027f4bcd5d40e8a73e398dc6ee266fa376db94da96c835dda7ad245b62c093ac9be4bc2438fc47ca3d19de8ee275039b9c14dc86d33509a20cce64e2d2917c86a4101fa8f8872e37b1b28ccc57c29913f09ac4402040f706f02ba13d094042c1e40d903a01a80d206502d816807a03701900c405c028011808801c00d0058024010007002800c004001⟩⟩
theorem candidate08136_checked : Checked candidate08136 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19718195003648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08137 : Description := ⟨89, ⟨13, 0x29434088ed425209cfe475c3a81c8ee266edb6a5aeed3d6922e7163ab04529a6f934a971493a4390be7e23e51ed0ec275038f1c14da66ba350999cc9c60a2d191dc8be42f2090fe07c43971be8d946662b314089ac4a42200f706f034615a09e842c1e40d903501a40cc06002d816807803201880bc05c02d014008c044019009803801a00b004802000e005002000c004001⟩⟩
theorem candidate08137_checked : Checked candidate08137 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19718329270272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08138 : Description := ⟨89, ⟨13, 0x28112728f9c76a253094825bf91d70ea0713376db52d7769eb491738b1d582294d37c9754871f88f947503829b4cd4266732718e8c0c5bc2d193d08ee45f22310ac8243e21d80e5c6fa3651a60ccc56a28313589484401ee0de068c27a10b07903640e806a03481980c005b02d00f006403101700a004602200d0064030013007003401800b004802000e005002000c004001⟩⟩
theorem candidate08138_checked : Checked candidate08138 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19718337593344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08139 : Description := ⟨93, ⟨13, 0x2aa1424a0447761290818013fa5e6aea0731b899bb6dca6d4b5dda7ad245b4ac093ac9be4d2a5c524e90e42f9f88f9477a3a81cdce0a6e43699a84d1066732718f4b7c5a527a117c85c4101fd0f8872e37b1b28ccc59e2b214c89ac47222010207b83aa1bc09e84a02160f206c81a80d206502d816807a03701900c405e02e01680a004602200c003801a00b004802000e006002800c004001⟩⟩
theorem candidate08139_checked : Checked candidate08139 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19718731874304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08140 : Description := ⟨96, ⟨13, 0x15459ffc76a12908482c4029fe2f42762baa5cc8e487163785b96daf6beb4e5a40b044df26952e2927487217cfc47ca3be9d94e9a7023741b40d3c63a30316f0b464f423b917c8243fa1f10e5c6fa3651998b4856229813f89b84aa23c11188083e21d80df869830a16c0ad84e8252108077835811a08c03501a406403101780b805a028011808804001e00e807003401900c004c01c00d0058024010007⟩⟩
theorem candidate08140_checked : Checked candidate08140 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19718865945088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08141 : Description := ⟨74, ⟨13, 0x589aa5544d864c139ec4f4c79dbae5d3ee7372bb8d9b24d76693a7cd2f088c43b2194fc67c93ce9e04ec06bc350194492247822f10487c43971988b9853825210386ec31413e093036c14609704881fc0dc05f02e01680ac05502380d804e024011007803a019009004001e00d00580240100040018008002000⟩⟩
theorem candidate08141_checked : Checked candidate08141 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19724792561920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08142 : Description := ⟨77, ⟨13, 0x2192f4c75cba7dcaed76693b24d7cab9c574aa894189f34baa23d0ec8623f19f24f347813b19ae4d4065130514909ee49123c117885e4121fc0f8872e34e1988b9853825210386ec31413e093036c12207f037017c0b805a02b015409004701e00d804e024011007803a019009004001e00d00580240100040018008002000⟩⟩
theorem candidate08142_checked : Checked candidate08142 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19724800950272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08143 : Description := ⟨77, ⟨13, 0x2db5626a95535689b2428b3c2c1ee0f4b79dbb49d3ee7672b38d9b24d5d693adb15229da44d21d50ca7fc3e49e80f0076035e1a1cca249123c11788263c91bf0c605cc29b135888034418a09f84941b609704881fc0dc05f02e81680ac05502380d804e025011007803a019009004001e00d00500240100050018008002000⟩⟩
theorem candidate08143_checked : Checked candidate08143 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19724924682496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08144 : Description := ⟨77, ⟨13, 0x24851678583d2dda4e9f72b3575a4ec935f2ad955d2a8150627690ea8623fe1f24f0076335c9a1cca260a29213dc92247822f10a88263f81e48df869c3181730a6c4d62200d1062827e12506d82440fe06e02f81740b405602a812008e03e01e00d804e025011007803a019009004001e00d00500240100050018008002000⟩⟩
theorem candidate08144_checked : Checked candidate08144 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19724933070848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08145 : Description := ⟨77, ⟨13, 0x2f3b6dda9553528a1164897c24e09cf737a53b55d78e7371b3655aead5c692aa394b29bd4bc22750e87ff3f31e74ec06bf34f9a18c9e49123c117866431918089ac4a422010386e834216f09f84981b409704881fc0dc069033017c0ac05502380d806202e013807803a019009004001e00d004802000e005002000c004000⟩⟩
theorem candidate08145_checked : Checked candidate08145 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725040288000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08146 : Description := ⟨83, ⟨13, 0xb6d589a97943495dc8fe29d0b07e5bd91eaef34775ba7dcdee5d71db5e5abad2753427cd3b489a43aa194ff87c93bd9d34e0469c3439944c1a52128593e88f045e2088f246fc33518c0b9857629f13f073c3721a20c504f024a0db04882000dc06502f81780b405602a811c07a036013809404402000f007402400f00680280120080018008002000⟩⟩
theorem candidate08146_checked : Checked candidate08146 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725193085184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08147 : Description := ⟨78, ⟨13, 0x589a27d0c98583dc1e76e9f6bb3575a4ec935f2ada54d09f34ed23d511c85e40a9f24f327653501a1cca260a29213dc92247822f0f887923971bf0cc46302e615c0a043a41bb0d1062827c12506d82440fe075037017c0b405602a812008e03d01b00b404e026011007803a019009004001e00d00580280120080018008002000⟩⟩
theorem candidate08147_checked : Checked candidate08147 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725197312000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08148 : Description := ⟨86, ⟨13, 0x52e683736f95dc546192f6f7ab3ce1d3ee5c6bb3581a4ec935f2ada54d09f34ed25d511e8764311f8cf9277c39a1ba4d4068332898f4b1454029194289e64aa248917885c4101fd0f8872e33118e0b9856e29e14187503761a00c504f82460db04881b80be05a02b015409004701e80d804e024011007c03c01d00c0048022010006802c0120080018008002000⟩⟩
theorem candidate08148_checked : Checked candidate08148 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725203554304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08149 : Description := ⟨82, ⟨13, 0x5b7697743795dc52e259093823bf2dec6f5a7773af1cb4e3b6c735f1ab8d25534a7c137a97844ea1d0ffe7e63be9d34e0469a343193cc1a52128593e88f045e20b0cc06323011580a684fc252103876837c1a10b784f024c0da04882000dc06903381940be05602a811c06c03401880b804e02000f007402400f0068024010007002000c004000⟩⟩
theorem candidate08149_checked : Checked candidate08149 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725308690688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08150 : Description := ⟨85, ⟨13, 0x296d3fe9b9454219904b7b93d65d7ee576bdb57da44c935f2a9a54ac9f04dea5d511e8764311f8cf9278134d9a10cd863a3031628a8652228492b492847b2090fe87c43971a68cbc6362e415a8a70506252103875837a19f0b684f824c0d804882300dc05f02b015409004701b00d0062027012008803c01d00e0068032018009002c012008002000c004000⟩⟩
theorem candidate08150_checked : Checked candidate08150 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725320980480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08151 : Description := ⟨85, ⟨13, 0x2dbb5aaa68d2e283d36f95dc58e29512c849c205f96f847bb3d75ddced57393965c76d8e6bab58da4aa6a4eba6f52f089d43a1ffcfcc77e39a1ba4d3e68132794bca144fa248917882a33218b8c0457c29913f09ac4401da0dd06942de13f091836812206e03481940be05602a811c06c03301880b804e01f00f00740240100068024010007002800c004000⟩⟩
theorem candidate08151_checked : Checked candidate08151 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19725442892032 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08152 : Description := ⟨82, ⟨13, 0x5ea281524289ac23de9aed274eb951b7eda36a2349d92cbe35b2aba549ea0c4dca2510ee7fc3e39e54efc6e93669ae4cdc65130514a4a184f226e12448544131fc0f246fc34e17f8b984402070f6868c31213f086036c0f006e03301740b405702a811808003e01e00d805c025011007c03a019009004001c00d00500240100050020008002000⟩⟩
theorem candidate08152_checked : Checked candidate08152 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19727079505920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08153 : Description := ⟨86, ⟨13, 0x5e82c6352ca5151428131618a2c4ca12304e7a0bc81daae9b7343951c82dbf6d2b655aead43692aa2d4dea5c4dda5e10d684a3ff9f14f2477e3b59ba4d9e6bf34f99b4c9e50c26e124482637e1b20cc863430013589484402070dd06202de13f086836813207803481980be05702a810006202e013807c03a019009004001c00d005002000e005002000c004000⟩⟩
theorem candidate08153_checked : Checked candidate08153 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19727120662784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08154 : Description := ⟨87, ⟨13, 0xb14d02a2290c9847bdb5ea2f3e74eb949b7eda36bb3511a4ec965f1ada547c9f34dca3dd12087b42e2054f8e7973be1d9cdd26cd35019b8ca260a29494309e44dc2488f887923971bf0cc45fe2e61598a7050c2070f687483761a30c484f82180db03c01d40dc05a02b815408c04001e80d805e026011007c03a019009004001c00d00580280120080020008002000⟩⟩
theorem candidate08154_checked : Checked candidate08154 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19727343747072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08155 : Description := ⟨83, ⟨13, 0xb18d0de8132b98af45221230477e5bcc5ddce9b736b93db7eda56c735f1a86d25535a7c1376978435a128ffe7c53811ba4d9e69a336993cc1a52c28813bc82237e1b20cc06343001580a684fc252103876837c1880b784f021a0da04c01f80f006903381940be05702a810007a03401880b804e02000f807402400e0068028010007002000c004000⟩⟩
theorem candidate08155_checked : Checked candidate08155 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19727389065472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08156 : Description := ⟨86, ⟨13, 0x52ce7f92c6866427a096f4074c3949b7eda56bdb519a44c965f1aa214d69f04dda5d512887b42e9df0dd26cf34d9a14cd663a3031628a864f026f92b492845a2160e5c6fc3641a68cbc6042e415a8a70506252103875837a1860b684f821a0d804d82300ea05f02b815408c04001e80d0062027011808803e01d00e0068032018009002c014008002000c004000⟩⟩
theorem candidate08156_checked : Checked candidate08156 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19727401355264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08157 : Description := ⟨84, ⟨13, 0x1626a4bcffa18d0938273db5ea2f3b74fb95dae2d4264b2f954ac9f04dea5c51ea89043da17902a7c93c09d94d6c69b3361828a5250c27b92448bc4121f10e5c6022b314e0a044a42070e906ec34618a09f049812208c03701b00d205f02d01580aa05401b00d006202f016809c04c02200f0074038019009004001a00b004802000e0040018008002000⟩⟩
theorem candidate08157_checked : Checked candidate08157 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19729607622656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08158 : Description := ⟨89, ⟨13, 0x2c5340a99e43ee16108f7b83d41e7ce9d728b761b46d5d6a2349d8bebe35b4a8953b49b94d423dd11c87a42e2054f8e7993bd9d9ce046cd34399b8ca260a29214349e44c323c0f887923971bf0c605fe2e615c0a6c50c2200f687483781a20c484942180db03c01d40dc05a02c015409004602000f406c026011008003a019009003c01c00d00580280120080028008002000⟩⟩
theorem candidate08158_checked : Checked candidate08158 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19731636617216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08159 : Description := ⟨82, ⟨13, 0x506e8152b9847bdbdea6e9d7273761b46d606a2349d8bebe35b4a8953b49b9447a1e0fc67c73811ba4d9a6833371944c7a58a291943c95442e2080fe87c439718e0bfc5cc2b714c88803da1d40de0680312123086036c13007e03c01b80b405802a812008c04001e80d805c024011008003e01d00c004802200e006802c0120080028008002000⟩⟩
theorem candidate08159_checked : Checked candidate08159 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19731642859520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08160 : Description := ⟨86, ⟨13, 0x5ac6c634d1a0f50265731638a3c246102fcb7bb3cc5ddce9b7393939bb0da56c7358da86d2563329b13ae9bb4bc22750d68313f31f14e046e93679a04cda64f297943c9de4101cb8d906663171800af853227e13588803b41a50c405bc24610d06d02600fc07803481940be05802a810007a03301880b804e02000f807402400e006802c010007002800c004000⟩⟩
theorem candidate08160_checked : Checked candidate08160 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19731684016384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08161 : Description := ⟨85, ⟨13, 0x29653fc9a34b1a2cd0b384f3d01d30e516ec3695ac4d46691317d7c6a83536275d37687a42e9dece046cf34f1a08cd663a3031628a444f026312b48f645a2160e5c6fc3641a68c586042e414d8a0c4d62200eb069030c16d09284341b009b04601d40be05802a812008c04001e80cc062027011808804001d00e0068032018009002c014008002800c004000⟩⟩
theorem candidate08161_checked : Checked candidate08161 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19731694225408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08162 : Description := ⟨94, ⟨13, 0x589a95f4979ff4aee28912c849c2120b0fd87afbd6de8aef47613ab1cc8e487163785b3ad996beb59da96d2053726f52f088c43c2194fc67c93be9d34e0469e34219b0c1a52128693e88f045e2090f8872e33318c8c0458229814789b84aa22310507a43c01bf0cf06342d813a09484201de0d6051824411808003701a406c031017009c048022010007803a01c00c804801e00d0058024010007⟩⟩
theorem candidate08162_checked : Checked candidate08162 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19733898330880 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08163 : Description := ⟨97, ⟨13, 0x296d3fc93947062a10cc84f412deb2f0a75fba61ce0e5771f3695af6d5f6a334898c6b9c575aa1d4d2a554f826ed2ea8764171f8cf347813b41b3cd3668433598e8c0c58a284937c98c49423d916888c42b2090fe47603971b20cbc6363021720ad4538283129081c37a19f0c305b42ae13e09304341b009b046017c0aa04702000d0062027012008c04401d00e00680320180090030016008002000c004000⟩⟩
theorem candidate08163_checked : Checked candidate08163 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19739883603968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08164 : Description := ⟨90, ⟨13, 0x52d67f91c18a6c2ce13cf5c791bb61d30e5671f3695af0d626a334898c6aeb542a9a94aa9d74dda1d508e7fc3c01da0d9e69d34119acc746062c514249be4c624a11ec8b44131fc8ec06fc36419a0c586042e414d8a0c4d62200dc069030c16d0ab84fc24a10d06c026c11807602f815408e04001f00cc062027012808c04401d00e00680320180090030014008002800c004000⟩⟩
theorem candidate08164_checked : Checked candidate08164 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19740015724544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08165 : Description := ⟨97, ⟨13, 0x297341ba0545462290c9847bf35ed8f5679bba75ce4e5c71eb68daecd606a2349d8c6b6953428f944a9f34ed26e51ee89143b2184fc67c73cb9df0ece6e93669a80d0666e32898f4b1452828513d09b849121710407f43e21cb8cc46382ff1730ac853c28211c87b43aa1bb0d006242b013e09184301b607803701680aa04702000f406c02f012008803e01d00c004802000e006802c0120080030008002000⟩⟩
theorem candidate08165_checked : Checked candidate08165 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19740228599808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08166 : Description := ⟨82, ⟨13, 0x4ff22770cc859c279f96e98737b695af6d626a334898c69f04eba6ed1ea89342f9e64d9e69b34119acc746062c514249be4c624a11ec8b442c1cb8df86c832f18b0c085c82b411c86f43481860b6856027c125086836016c09b04601d40ca05f02a811c08003d01a00cc06202d013808c04401d00e0068032018009002c014008003000c004000⟩⟩
theorem candidate08166_checked : Checked candidate08166 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19740279965696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08167 : Description := ⟨86, ⟨13, 0x54aa9913fe8dfc57612708482c3f61ee8f4676dbb09d58e7d719b7e9b3ad966c0359da96d204dea5e0ff87e33e49e74ec069d34219b0c1a49123c11788643f51990c646022c114c0a3c4dc25511188283d21b70cf06342d81630a104a42100ef06b028812e09104601fc0e806e034811c06c031017009c04a024011007803a01c00c804802000f0068024010007⟩⟩
theorem candidate08167_checked : Checked candidate08167 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19742219830016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08168 : Description := ⟨94, ⟨13, 0x56aa9574189ff48fe2810ad849c2120b0fd87ba3d19db6ec275639e9cc2e48709b721b3ad806a9352da40a744dea6ad1ea8964391ff0f9279c3c19d94d3a67f3361900b1452b28392448bc43120c0fe86643141808b485882ab13f89b84782230f4876036e1ae0c685b02b614209884201de0d6051024411c08c03f81b80d606901b00c405a027012808803c01d00e00600240100068024010007⟩⟩
theorem candidate08168_checked : Checked candidate08168 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19742622483008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08169 : Description := ⟨75, ⟨13, 0xb7dd52e89f4339c847821c90c87d8bb41baed736a0b4a596ec626282a11446a074b1245d1c48c6420a05d00273638c1b98d6866b32997dcb585772ad93589584961e58eb46f63491800ba04ca21a0f706d82e210d05e82800fa06403081740b605502a013807c03901b80d404601d00e00380100070018008002000⟩⟩
theorem candidate08169_checked : Checked candidate08169 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19831283859584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08170 : Description := ⟨78, ⟨13, 0x62d6fb96fbb4851f689f390992c44a1c8fb178e3885ae8d41694b2dd8c0c1158c2c2d504a074eca58922e8e246320ad02e7e53a91c60df86b4335994cbee5ac2bb956c9804ac23d0f9c75a3911a48c005d026510d07b82e2139086824c0e0064030816c0b005502a013809004401c80d404601d00e00380100070018008002000⟩⟩
theorem candidate08170_checked : Checked candidate08170 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19835444609152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08171 : Description := ⟨79, ⟨13, 0xc5adf0e9094369c84c5e5c310d8623ed5e34ed4712b7adbaad716a0b4a596ec426042c61616a8753aa90d3ea9d94ba249118c8934159f94d6e66b32997dcb585772ad94589ac4c024b11e87ce3ad1c88cb46002e811b07b82e2155086832412807d03801b00b605502a0138088039015008c04201d00e00380100070018008002000⟩⟩
theorem candidate08171_checked : Checked candidate08171 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19844030349440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08172 : Description := ⟨80, ⟨13, 0x1791a6452da86d31794e468e21b0c484b3d59e18ed475137adbaad71694b319968c425eb2b6550ea75521a7d5380926462a2450547cc3cb1adcd086532fb95b0a2c4d626012588ba3e71d68e446c832d1800ba04a82360f686803121710aa832412808303e81c00d805502a011007202f015009004201d00e004801c0080038008002000⟩⟩
theorem candidate08172_checked : Checked candidate08172 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19878389039232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08173 : Description := ⟨92, ⟨13, 0x159da3ecce245f1f48ef457a1f30e181c3ee1ddae5d7143831ba4d41694b3e98c4b4958f2c05510a3c511a82d2ac8db423205cef674b39b1a78cd665330397b0b765a62ba14949ea4c225410b08223e41e38ebc72837e1a58c686002e814f89a04a223810e87b83a817109e049421a09302d81540a805001e80e0058029011808003a01c00d005802a01100700280100070018008002000⟩⟩
theorem candidate08173_checked : Checked candidate08173 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19908861657088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08174 : Description := ⟨82, ⟨13, 0x5a4690943699344661970487fe3c0dcd8d8d6a0b4a5888a374f7255d25a91146fa1ed08882d3ff1e74f0274f38a9bfcd3666b32997b0b845a62ba14409b24c224990c882c3e41d50e506603001740ac04662070f7068c2e21520930434128071033818c0c405b02c81540a805002280e006802b0118074038016007002000e0040018008002000⟩⟩
theorem candidate08174_checked : Checked candidate08174 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917042647296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08175 : Description := ⟨85, ⟨13, 0x2d23484a1b4c9a2330cb8003c0dce0dee6a0b4a59f4c445ce2cd546e9ee4aba4a92228df43da11105a7fe3cd1e04e9e71837f9a6ccd665330397b0b765a62ba14409b24c224990ac82c3e41ca0d306603001740ad44702070f7068c2e215709304340e206302d81540a805002280e4070034015808c03a01c00d005802a00e006002000e0040018008002000⟩⟩
theorem candidate08175_checked : Checked candidate08175 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917051035648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08176 : Description := ⟨83, ⟨13, 0xa19cc9a3e10f982540e1f70f1776bb9a9c18d8d6a0b4a5888b21582a9bd4469f24ab236cff47a03c01cd8e2a70134e99acca65ec2e11698ae851026c93089264271e38ea86fc31a1800ba057629f134094446621d0f706e42e2152092843414009403b01c40c405b02c81540a805002280b0052025011807403801600700280100070018008002000⟩⟩
theorem candidate08176_checked : Checked candidate08176 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917174767872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08177 : Description := ⟨84, ⟨13, 0x131a8fbc76e28b0f98643ed5e34ed473b3831bd6d41694b3e9888b1a582a9bd4469f24ba237d0887fe3ca1cd8d6e66b32996fcb44570286130891e42a2098f1c75a3961bf0cc86343001740ae04d425111b087c3dc1bb0b8855424a10d04a02200fa05b02a81500a004501f00e4054023010807403801900b805802801000700280100070018008002000⟩⟩
theorem candidate08177_checked : Checked candidate08177 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917178994688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08178 : Description := ⟨82, ⟨13, 0x50ce64d1f087cc0e1f70f1776bb831bdcd41694b3e9888b1a582a9bd4469f24ab236cff478039b1c60e0269d335994cc0e5ec2dd9698ae851026c93089263c71bf0d306343001740a7c4d025111c08743dc1b90b8855c24a10d05001d80e205b02a81500a004501f00e4058029012808c03a01c00d005802a00e00600280100070018008002000⟩⟩
theorem candidate08178_checked : Checked candidate08178 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917183156224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08179 : Description := ⟨91, ⟨13, 0xb4b520e86732691f40ee000fea7aa3c95e0aed7738382dbdcd3f694b3e9888b68569a8e13e495549524350ee8434179fe8f3474e39a9c60e0269d334994cc0e5ec2dd9698ae851026c930892642b1fd8f206ca34c1740ad453426d12808e043a2070dc868c3121710ab849821807103501540a805002280e406402e014809403a01c00d005802a00e00600240100070020008002000⟩⟩
theorem candidate08179_checked : Checked candidate08179 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917249216512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08180 : Description := ⟨89, ⟨13, 0x301b59da3c50be64d22f8fa477a29111987cc32e0950387dc3c5ddaee6f72eb8a1c18df06e935b9a82d296282d6563cb08539290d4469f54ba25891c48414009e64f0e75239b1c68df8698335994cc0e5bb26110b078e3af1bf0c686002e815a0a104a21ee0ea85c42b0125086828012608f031016c0aa054015008c03a01c00d005802a00e005002000e0060018008002000⟩⟩
theorem candidate08180_checked : Checked candidate08180 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917443203200 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08181 : Description := ⟨89, ⟨13, 0x301173bb4b5666abf546a58520e8cf433915c6a621d0c8840c0fa02ef1976839c9cb2e2470937c1baed7369fb4a58a0b1e510a59524c91443f213d05e8013cb9cc0e346e934299a4ca66092fb95dc9ac4962170f1875e3651740ac854a27012a08683aa1b60c485c42b012308601f40d406203081740aa05401d00c805e02a00f807403801500700240100070030008002000⟩⟩
theorem candidate08181_checked : Checked candidate08181 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19917643464832 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08182 : Description := ⟨80, ⟨13, 0x1690a3ec576070fb8780b8a1bdcdd26a0b4a59f4c455ce2cd550ea6e51e25591b687a42320ace9671834f19acca66072f616ecb4c57429310ac82c3e41ca0d306323001740a7c4d025111c08743dc1a20b8855c27810d04981f00e205b02a81500a004401c80e0058029011808003a01c00d005802a00f00700300100070018008002000⟩⟩
theorem candidate08182_checked : Checked candidate08182 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19921343905792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08183 : Description := ⟨93, ⟨13, 0x320d881c0edf72f3f775b7a5a42bfd44f9fece2664b2938724249f64f1c74f3889a52cb66293045780b1855faa09452a074eca70d2ce910470a32d0f484b41aa05cfca7cf3a89c60d946b4333194cbf85a52bb1580a1e4e026512b08f44641f30eb46be34917d8ba04c82200f406f030817109f841c12208d03701a80c805f02d81580aa054027012007203500e80700100070028008002000⟩⟩
theorem candidate08183_checked : Checked candidate08183 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19938725150752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08184 : Description := ⟨74, ⟨13, 0x4e2662f2938d4443612cfb478cba89bd6dd8694b311884bad58c2a1d4eaa434eca701248893440a13cfca7cc35b9a60ca65f72ab14589ac4c023d11747ce3ad1b20cb46002e813808d83da1b60c485c42aa139064825011e07d03601740b005502a013809404401c80a804201d00e004801c0080038008002000⟩⟩
theorem candidate08184_checked : Checked candidate08184 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19947106418816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08185 : Description := ⟨73, ⟨13, 0x2f8f444972bba1c44dee6d33629a84c105922ae951ca24501a7512ac91046321e90607e03a61b40cd85eb2e29694ab652f28793149484751f08ea86ca34618088803dc1bc0c504fc18e0b204601ec0e206d03481900b405602a81500a004101880b004401e00e807002e00d004802000e0050018008002000⟩⟩
theorem candidate08185_checked : Checked candidate08185 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19974158565632 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08186 : Description := ⟨79, ⟨13, 0xa3c4c9a3dd11981c3e71e2ee286f735b9a82d296222e71630b0451ba5592208c63a59c60e0466b329981cbd8557288136498442b20b0f906fa34c1980c005d029f13409444702060f706e42e215709e043414008f04301c40b605502a014009c04501c80d0058025011808003a01c00d005802a01300700300100070018008002000⟩⟩
theorem candidate08186_checked : Checked candidate08186 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19985768415232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08187 : Description := ⟨84, ⟨13, 0x1851b4bd44e89f39c994c5622970dd81c3d5de44f06776b8a1bdcda56c535b9a52c435692a394d2a0e4ab23710ea8454181d2ce046cf32997b0b84558290942c9bc4c125790c882c3e41d50d9068c33018c8ba053e26812886e434418a0b884f021a08f04001c40da05f02a81500a004701a00b004e0250100074038016009003c0100070018008002000⟩⟩
theorem candidate08187_checked : Checked candidate08187 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20000800801024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08188 : Description := ⟨85, ⟨13, 0x2d2f5139ce4ca62bb14b81c3d5de44f0671437b9b4ad6e694b319886b9c5692a1d4d295646e21d508a8303a59c60e046cf329981cbd85bb2c59560a4c50b26f13048564161f20d9069833018c8ba053e26812888e03721a20c505c42ae13c086823c0e205f02a81500a004701c80d0058027012808003a01c00d005802a01200780300100070018008002000⟩⟩
theorem candidate08188_checked : Checked candidate08188 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20017980669952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08189 : Description := ⟨83, ⟨13, 0xb4bd15686932997548fa4590da81c3d5de44f067743875bdcda66c7b5e5a4ec4360dad294289f34ab21d508a8303fe1c08da069c32897b0b8452128593789824a423c10c882c3df1e40ea86ca35119a8b9853e26812887b83721a20c504f01b609604001ec0e205a02b01540a004701d80b004a022010007803a01600780340120080018008002000⟩⟩
theorem candidate08189_checked : Checked candidate08189 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20034036465920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08190 : Description := ⟨84, ⟨13, 0x180eb4bd1ea86337297dc8822a10e986640b1eb8ef576c3761b4cd6d691314d828b5653aa901448a064b122050988304091d1cda0698336181cbd25bb291146494a47b20c8f707903af1b28d3467631b1720a884ca25111c07b83ac1c40d205b42720d804b023c11808803981900b005602a8120086031011007803a01c00d005802a009004000c004000⟩⟩
theorem candidate08190_checked : Checked candidate08190 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20034556528768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08191 : Description := ⟨90, ⟨13, 0x6036b3b478a18c87e3e911e874c332058f1577abb61d4ce51710b831bb0d6d6a334898c4c505acac79510a72521a88d40c962420a048f947873a91cd8d3066b30397a4b764f827392948c442c2070f9c78e3af1bf0d346763021720a884ca25111c07b83ac1c40c305b4272125086836014008f04602200ea06402c0154086031011808803a01c00d005802a00a004000c004000⟩⟩
theorem candidate08191_checked : Checked candidate08191 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20036636903552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08192 : Description := ⟨78, ⟨13, 0x51125e316487d4366058f507833889b4cd4260a2da1504a244ab21e90608123a61c60da06b433616fca4850d260929c8f042f1f08f2075a3651a48c6460229b12888803dc1bc0d1062827e0b204602200d206402d01580aa054028012008603901a80c405802200f007403801900b805801e00d004802000e0050018008002000⟩⟩
theorem candidate08192_checked : Checked candidate08192 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20042878091264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08193 : Description := ⟨79, ⟨13, 0xacbd11e44102d801bdb5dcae577103825b4cd425a528192e49574932240f0274a3999c68da06b633616fca524a72090f2072e3651998c0456629c13508d840e1ee0e9068c31413e093027811808803981a40c605a02b01540a805002180ec06202f01580a804c02200f007403801900b805801a00b004802000e0040018008002000⟩⟩
theorem candidate08193_checked : Checked candidate08193 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20047435202560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08194 : Description := ⟨80, ⟨13, 0x1597910437205b0007b53ba1caee20704b699a84b4a503255d2548944091e04e9473336819b0c746072dd94948243c81d78e5c6ca34b1998c0456a29c13508e040e1ee0ea068c31413e093023011007b03981a40c605a02b01540a805002180ec06202b011007803a01c00d006402e01600a804401a00b004802000e0040018008002000⟩⟩
theorem candidate08194_checked : Checked candidate08194 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20047443525632 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08195 : Description := ⟨74, ⟨13, 0x4372000f6a7743889c12da66a128192548944091d30e666d033618e8c0e5bb2928f847903af1b28d2c6022b511c088040e1ee0ea06f034618a09f849815608c04401ec0d2066032018c0b405602a81500a004301880b805802b011007803a01c00d006402e01600a804401a009004001c00a0040018008002000⟩⟩
theorem candidate08195_checked : Checked candidate08195 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20047707766784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08196 : Description := ⟨86, ⟨13, 0x5a0a8f143198ac9ca2a111e86640b1eb8f157873b61d4ce216f73761adad466913109830a8753aa90d410962440a1050567ca3a91c60d3066b30397a4b7651927392f88f646221590647ce33b18d8c085c82a213289444701ee0e2069030c16d0ab84e421a0d8064828011e08c04401c40c805802a8110072031011808803a01c00d005802a00c004000c004000⟩⟩
theorem candidate08196_checked : Checked candidate08196 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20049119152256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08197 : Description := ⟨79, ⟨13, 0xa24c7de1f302c78e3a81cece5670637ada82b1a511a8213509744ab21190287ca3ca1e00e6c6b733596fc9b64c222f90a88263c71d68df863430015c0a6c4a223611007b837815509f849421a09404602200d206402d81680aa05402800f807203101600a8046022010807403801900b805801c00d005002000e0050018008002000⟩⟩
theorem candidate08197_checked : Checked candidate08197 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20062129946624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08198 : Description := ⟨81, ⟨13, 0x2df7478a17ce366713268f9c7862330cb81c3fb5f70f9c78bbb5dc50dd26c535b9a82d2965bb1898a0b1d585a90d3ea96248ba38918c8414009d48df86b434c19acca66072de155ca4a4f526110ac76037d1800ba04a22060f707502e2157086828012608f036816c0aa05401a808c03a01c00d005802601100700300100070018008002000⟩⟩
theorem candidate08198_checked : Checked candidate08198 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20106027499648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08199 : Description := ⟨86, ⟨13, 0x5bee8f142f9c6cc9a3e71e188cc32e0950387ffbfb5f70f9c78bbb5dc50df16e93635adcd41694b2dd8a0b1d585a90d3ea9744b124a522e8e2463210500275238d9bf0d6e698335994cc0e5bc2ab93088563b01be8d306002e815a0a104a223910307b83aa171086828012608f02d81640aa054011808403a01c00d005802600e006002000e0060018008002000⟩⟩
theorem candidate08199_checked : Checked candidate08199 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 20123198980224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate08199_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch081

module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch010
open Papers.RationalityTen GraphCandidateCoverage

def candidate01000 : Description := ⟨78, ⟨13, 0x50825eb0fe85d4065deaec3753388db82d6269db4b582caa1511274d2868ad4091f80f9474d3759a78d046522ea16f4a544f826312948e646222290507c43c91be0d3462c2fd1748b384d623811008183dc1d60d206182da12507a036011a05802b010c082033019008c04402000f0070036015009802c014009002800c004000⟩⟩
theorem candidate01000_checked : Checked candidate01000 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17223399770112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01001 : Description := ⟨73, ⟨13, 0x2ac7498a2c48421d50977c33bcdd74e8172ab88dc14df96ddb649a80d2b59d28513828b040e9f90f5677f3a69cd0e466e535e19a8caa47722f90507c43c91cb8d945fe2e614e89ac4a42050de068c2e00f306d82680de05b02c015c0ac037011808003e01e009803801a00b0050024010005002000c002000⟩⟩
theorem candidate01001_checked : Checked candidate01001 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17227131191552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01002 : Description := ⟨73, ⟨13, 0x212ef86779bae9caae2370536eda80d2b59ba7052568a94302044fc87b03bf9d34e6871c37299a8caa5d82a1129c8ee45f20a0f887923971b28bfc5cc2cc14e89ac4a423b10287483781a30b803cc1b606f02d81600ae05602180dc060026011808003e01e009803801a00b0050024010005002000c002000⟩⟩
theorem candidate01002_checked : Checked candidate01002 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17227668062208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01003 : Description := ⟨72, ⟨13, 0x120d84bbe0dd74e55711b829b76d40695acdd3828ad3f21dfce9a73437299a8caa5d42de94f89ea47722f91148283e21e48ebc72e36517f8b9859c29d135894840a1d40de068c2e00f306d81ec0de05b02c015c0ac04301b808c04001f00f006c02a013008803801a00b0050024010005002000c002000⟩⟩
theorem candidate01003_checked : Checked candidate01003 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17227676385280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01004 : Description := ⟨80, ⟨13, 0x101c7c33bc1cb0e26706b76db74da96bbb579a7ad2c59baa8541693f49422a50c08133c11d40e6e7053721b4cd426883339958bb054225610507c43c91cb8d9466631a1740b3053a26b12908d84401ee0e906f034617109e84902160f206c81bc0d406002d80dc06403001500a004c023009803801600a004802000e005002000c004001⟩⟩
theorem candidate01004_checked : Checked candidate01004 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17228724633600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01005 : Description := ⟨86, ⟨13, 0x48362ef0e180cbe0dddae587133835bb6dba6d4b5ddabcd3d6962cdd542a0b4a1a2b502e7823a81cdce0a6e43699a84d1066732b1750b7a53e27a92a088a4141f10f2475e3971b28d2c66631a1740b3853a26b12908e04401ee0ea06f034617109e84902160f206c81bc0d406002d80dc064028011806c02a013008803801600a004802000e005002000c004001⟩⟩
theorem candidate01005_checked : Checked candidate01005 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17228732956672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01006 : Description := ⟨71, ⟨13, 0xa4145e61c0ffe783bad1d46e8071e37bdaf8d5c69f34a947694643e21290627ff3ef1f34f5674d3901a68d0c66832a130c8be44e1da8cc06322e716b89484661ee0df068431016f0a904f024c0f406d02680f206a03101800b205602080d0064028010007802600f0070034012007002000c004000⟩⟩
theorem candidate01006_checked : Checked candidate01006 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17231576858880 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01007 : Description := ⟨70, ⟨13, 0x445de14eb175337cdaf6d5f69db4b5862a9e51da82905c7ca38e9a6cd086522ea16f4a224df26312508e64621fd8f8875c32f18d8bf45d225211c07b837a19f0c305b42ae13e09303d01b009c04681dc0c005602080fc068032014009004602200f00700360150098030016009002000c004000⟩⟩
theorem candidate01007_checked : Checked candidate01007 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17231589148672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01008 : Description := ⟨78, ⟨13, 0x508229311787f42e9d86ea67443705af6d6269db4b5862a6d51da8893a68ac40a1f80f947b23759a6cd046522ea16f4a224df26312508e646222290507c43c91be0cbc62c2fd1748b345082060f706f43481860b6856027c12507a036011a06202b010406803301900a804602200f0070036015009802c014009003000c004000⟩⟩
theorem candidate01008_checked : Checked candidate01008 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17231985510400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01009 : Description := ⟨74, ⟨13, 0x558e8ff1f284bc005f0aeec75d3a01cdce3c70537b5b76d796a034ad674a3e4f9a70508e7e43d59dfce9a7343919b94d3866a32a91dc8be44e1e48ea86ca33517f8b985ae25211f08143721a30b805482780f306d82680e206f02d81640ae05601b809404602000f807802600e0068028012008002000c002000⟩⟩
theorem candidate01009_checked : Checked candidate01009 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17235721093376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01010 : Description := ⟨73, ⟨13, 0x2ac111475c3a81d1ee0a6fb36f5aecd40618ac7d47c9284562050fc47ca3d69e60ecc73438c9b9cd4066a2ec137092247722f910c8283e21e48ec86f833117f8b444a42360f706ec34615509f03d01b606002d81680ae05601f80a8050023011008403e01e009804001c00d00580280120040018008002000⟩⟩
theorem candidate01010_checked : Checked candidate01010 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17235758350336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01011 : Description := ⟨72, ⟨13, 0x13078fac451d70ea070537cdb7ad766a030c563ea3e3f11f28e6871d3739a80cd45d42de94fc9b84a924891dc8be42d20a0fec7c43c91d70df06622ff12908e03dc1bb0d1855c27c0f406d81dc0c005b02d015c0ac03f014008c04401f00f006c02a013008003801a00c00580280120040018008002000⟩⟩
theorem candidate01011_checked : Checked candidate01011 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17235766673408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01012 : Description := ⟨73, ⟨13, 0x2ac709778ebae9d18e0a6fcb6eda80d2b618ac7138292b455211d02c7e43d79e60ecc73438b9b94cd46552ec137092247722f91207923ad1b28bfc5cc2cc14e89ac4a423b102868c2e015509f83cc1b606f02e816c0ae05601c80dc060025011808403e01e009804001c00d0050024010005002000c002000⟩⟩
theorem candidate01012_checked : Checked candidate01012 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17235989561344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01013 : Description := ⟨72, ⟨13, 0x13078f9425de3aeba744b829b76d40695b0c56389c14239f90f6673437299a8caa5d42de94fc9b84a924891dc8be4442168fec79236517f8b9859c29d135894840a1a30b8055c27e0f306d81c40de05d02d815c0ac03901b809404601f00f006c02a013008003801a00c0050024010005002000c002000⟩⟩
theorem candidate01013_checked : Checked candidate01013 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17235997884416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01014 : Description := ⟨73, ⟨13, 0x280b0b18023c81c14df56dc35d5a7cd31618a75937c93f4942128ffe7cd39a1c68da069f334193cb8053f26e12ac8f23c91d88de866431a1728ad853a284135894846a2030dd06202e615809f83c41b409203501a00ae05601b80c806203001500a003e01e00e806c02000e005002400e0060028010006000⟩⟩
theorem candidate01014_checked : Checked candidate01014 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17236509331456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01015 : Description := ⟨77, ⟨13, 0x260f097800be01e3aeec75d3829be4dbb6a034ad8629c1495a2a908e8163f21cd0e386e53351954ba85bd29f937095249123b917c7923af1b28bfc5cc2b614e8a104d625211b88143aa1a30b8056027e0f306d81bc0d005d02d815c0ac037018009404601f00f006c02a013008003801a00a004802000c005002000c002000⟩⟩
theorem candidate01015_checked : Checked candidate01015 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17236526366720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01016 : Description := ⟨77, ⟨13, 0x2b0b566a7652163e51797ff3e15d2ae7171fb835bd8dba6d4b641afed5e69eb4b1674a3b4a3211cf787823a81cdce4c7053721b4cd32688333995889c3c91d50d9466031a1740b5c4a42330f706e43461710ae850424810b07903640e206f03501880c005b01b80d0064028012808c02600e0050024010007002000c004001⟩⟩
theorem candidate01016_checked : Checked candidate01016 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17236777664768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01017 : Description := ⟨73, ⟨13, 0x2acd01c78eb835bf8dba6d4b579a7ad2c58e2a8127e928455211cf3676939b9c58dc86d335d1a20cce6562ec13708903c91d68d9466431a1740b3053a26b12908d84401ee0d185c42b412408583c81b206f03501800ba05b01c80dc06403001500a004a023009804001c00a004802000e005002000c004001⟩⟩
theorem candidate01017_checked : Checked candidate01017 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17237046132736 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01018 : Description := ⟨72, ⟨13, 0x11f28bb4065e3ae0d6dd36a5abcd3d6962c715409434239cdcdc86d3344199ccac5d42de94fc9b84442168fec7923651a60cc86342e81670a744d625211c08803dc1a30b884902160f206c81c40de06a03001740b603901b80c8050025011806c02a013008003801800a004802000e005002000c004001⟩⟩
theorem candidate01018_checked : Checked candidate01018 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17237054455808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01019 : Description := ⟨76, ⟨13, 0x1026803be35e4ce136feb6d9b5ed806b234e5a6493f49422a908e73438d1b40d3a6853299750b7a53f26e0f2475e3651990c685d02ca15c8a8050e26e12a88d04462020f8876036e1a60c285d02b614209084201de0d604902340de06a01b80c806002a014009404601f00f007403801b00a804c02000e0050024010007⟩⟩
theorem candidate01019_checked : Checked candidate01019 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17237582807552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01020 : Description := ⟨77, ⟨13, 0x215d01c75c3a81d24e587133835aeed5e69eac7d4149d849fa4a10287e23e51eb0f367823b49d40e6e6ba3509a20cce5d823b917c8864141f10f2476437c1998c685ce2cc14e89ac4a423611007b83781a30ad04f424810b06c81a80c005b02d00fc06403001500a0046022009803801a00b005002400e005002000c004001⟩⟩
theorem candidate01020_checked : Checked candidate01020 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17244327444480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01021 : Description := ⟨77, ⟨13, 0x23eb0e08574065d70ea072c3899c1ad776af34f563ea0a4ec250cfc47ca3c11d40e6e6a1344199cba85bd25491dc8be42d20a0fec7c43c91d70df069833318d0b9c59c29d13589484702200f706f034613d092042c1b207703501800b605a01f80c8050023011006c02a013007003401800b005002400e005002000c004001⟩⟩
theorem candidate01021_checked : Checked candidate01021 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17244335767552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01022 : Description := ⟨81, ⟨13, 0x2849408858c011ddeebd72c3899c1adcd6bbb579a7ad3459ba75937c93f4942050fc47ca3c11d40e6e7053721b4cd426883339938b804ab23c91148283e21e48ec46f433318d0b9456c29d14209ac4a423510187543781a30b704f424810b07b03640d406802d80dc06403101800a8050023011006c01c00b005002400e0060028010006001⟩⟩
theorem candidate01022_checked : Checked candidate01022 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17244830699520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01023 : Description := ⟨84, ⟨13, 0x1419857409a00eef7762baa5d26e5e716384db9cd7d6b234e5a6a9d849fa4a10287e23e51ec0efe74d39a1b9cd3c6853291750b7a4a923b917c88a4141f10f246f833318d0b9c5942b91500a1c4dc25511a088c4041f10ec06fc34c1850b6056c27412108403dc1ac08d03500c806002a014008c04402000f807803801b00a804c01c00d0058028012007⟩⟩
theorem candidate01023_checked : Checked candidate01023 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17244864119296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01024 : Description := ⟨73, ⟨13, 0x25ad1918bebe25da8ebb6e0b691b0ed586a13001576a9b543250914e7fe3f29d98dd66ce34119b0b485722ac94f4a1c48f23b112079237c1b18d24664301168887c40c1d20dd86883141710aa84941e8090035817c0ac05402480d4066027013008403c01c00a004c02401000780280120070018008002000⟩⟩
theorem candidate01024_checked : Checked candidate01024 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17320837709824 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01025 : Description := ⟨75, ⟨13, 0x945c6461f0f8675dba89d18dc16d4361dab0d3f5daaaed50ca5451125011527e53e61ebcdd66d234119a4b485722ac950898647622e912079237c1b18d245982060f687483781a20c485c42aa13f09284301e809003581a80c205401a80cc064030014809804201c00a004c02400f00700280120070028008002000⟩⟩
theorem candidate01025_checked : Checked candidate01025 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17327277015040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01026 : Description := ⟨74, ⟨13, 0x46462b8fb37c1baedd12dc16d23629ab0d4255daa191ba8ad3f29eccdd66ce35a1a08cd85d52d215c8ab253e29391d888842d1fd8f246f83631808b384d62060ea06f034418a0b8855c27e12507a01b40d606102f81580a803501980a404e01e00e006c028013009004401e00c005002400e0050018008002000⟩⟩
theorem candidate01026_checked : Checked candidate01026 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17329431773184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01027 : Description := ⟨76, ⟨13, 0x10af7f43ed9f3af867463765b80da26c3b569a84b364eca4491c08c7454a248f5e7663819ba8d986843361690ae45592a111d88903961be8d246323011740b3053a26b129087840a1ec0e906f031415509f84981e609003701700ac05401b00d4060026012008403c01c00a004c02400f004802000e005002000c002000⟩⟩
theorem candidate01027_checked : Checked candidate01027 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17329522540544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01028 : Description := ⟨72, ⟨12, 0xfe5fb3f9af83eb7e89da4d8ad5ad4290f8dd8c48ad7e17b36ce6b468466c5d55a457255953e5274764443fb3633193012ce29d26b2521d41bc18a17115713f1260f406d06106005f05c05605403502902802702401e01c01b01401301201100f00c009007005004003002001000⟩⟩
theorem candidate01028_checked : Checked candidate01028 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17329563893760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01029 : Description := ⟨83, ⟨13, 0x8c8c2ba12afe87db3e75f0ced375d3a85d18e0a6c3b56da84c3055da76137e912470231d1527fd3f21f2cf5e7983b31cd0d0a66c2d215c8ab254224811dc8bc4481e48df06c634918d0c045ce2cc14e89ac4a421e10287b03a41bc0d186282e015509f82400ae05602a00d4060026010807c03c01c00a004c02400d005002400e005002000c002000⟩⟩
theorem candidate01029_checked : Checked candidate01029 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17332643102720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01030 : Description := ⟨75, ⟨13, 0xa4c4b5a1f6f8976a3aedb78da66c93575a80c0059b2a254aea254a1229d0c07fe3f29d98e366e63681ad4d0e66a2d214f4a1c4dc261923c8ec4481e48e586ca34e18c0bfc5a221f10307b83a41bb0d105c42aa12506d81bc0b605602a812406e026011808403c01d00a004c02000f00700280120080018008002000⟩⟩
theorem candidate01030_checked : Checked candidate01030 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17353033187328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01031 : Description := ⟨70, ⟨13, 0x526212ef8975d3829b76d926a034ad85cb3652ba8313828a74301f90f3076639a1b94d6a66a32a9690a7a4dc23b917c8903c91cb0d9469c2ff1730b444a42050e906ec3461700aa83cc1b607a037816c0ae056024810806e026011808403e01e00a004c02000e0068028012008002000c002000⟩⟩
theorem candidate01031_checked : Checked candidate01031 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17356252839936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01032 : Description := ⟨77, ⟨13, 0x29310fb854425df0ced37463765b24d5d6a034ad860b36544a95d44aa0c4e927051528603fe9ebcecc70335a9a1ccd46552d2150898649022f91207923961b28d386302ff1730b304d621e0e906f03441700aa84fc24a0f306d81e40de05b02b010406e030013008c04201e00a004c01e00e0068028012008002800c002000⟩⟩
theorem candidate01032_checked : Checked candidate01032 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17360545710080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01033 : Description := ⟨80, ⟨13, 0x149884bbfa1f0ced375d3a31c14dd96ddb649a80d2b6182cd94aea0c4e0a4491528603fe9f90f5e7983b31cd0e066e535a99a8caa5a42a112408ee45f2240f2472c3651a70bfc5cc2cc14e89ac4a421e10287483781a30b8055427e0f306d81bc0b605702b00dc060026011808403e01e00a004c01c00d0050024010005002000c002000⟩⟩
theorem candidate01033_checked : Checked candidate01033 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17364838580224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01034 : Description := ⟨86, ⟨13, 0x4c1a41912d871425dfd0f83769bae9d12e0a6ecb6edb1ed40695b0c166ca5750627052248ad3fe9f90f667343819b94d7266a32a9754b4853e27a92a892047722f911085a3fb1e48ec072c3651a50bfc5cc2ce14e89ac4a421e10287503781a30b8055c27e0f306d81bc0b605702b00dc04601f00f006c028013008803801a00c0050024010005002000c002000⟩⟩
theorem candidate01034_checked : Checked candidate01034 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17364846903296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01035 : Description := ⟨73, ⟨13, 0x29b728b8c1c57def4f3675dba79d00df16de3695b16d796aeaed5554a70452a11cfca7c83d59c08dcc6cf35e1a70d0e5592a4130c8ec45d2270d906a233518c0b5c40c1cf0dc86882e215209e049421a0db05202680de05f02f016c0b205501b809c04a023010007402601200780380140080018008002000⟩⟩
theorem candidate01035_checked : Checked candidate01035 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17455906849024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01036 : Description := ⟨76, ⟨13, 0x14ee945c60228cf8975dba79d1edbc6d2b649aecd5d5daaa69512a70453a180fca7c83d69c6cdcc6cf35a9a80d0e55929e94389b84c323b11748864141cb8d9069c33118c0b4440c1d20dd86882e215509f049421a0db037817c0b605502480fc06e027013008c04201d009804802000f007002c0140080018008002000⟩⟩
theorem candidate01036_checked : Checked candidate01036 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17455911075840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01037 : Description := ⟨75, ⟨13, 0x945c63a1f6f7b75dba89d18dbc6d1b649abad445daaae1512a575129f94f987af38d9b98d9a6b534399b8ab253d287137098647622e912079234e18c0bfc59822010307b43a41a20c485c42aa13f09284301b60a403781b80ba05502480dc06c030013009404201d009804802000f00700280120080028008002000⟩⟩
theorem candidate01037_checked : Checked candidate01037 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17456109256704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01038 : Description := ⟨80, ⟨13, 0x14e8a0ed0063051627c5bc8dd12dbc6d2b651af0d626a32ed5536a864eaa7011508473f29f20f666e63679ad0d3a682335994cab253b29514449f04df263111085a3b01b20d206683161810b384d622010307583701a40c3055c27e12508683600de05f02a812406e035019809c04a02300e80700360130090030014008002800c004000⟩⟩
theorem candidate01038_checked : Checked candidate01038 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17456166864896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01039 : Description := ⟨73, ⟨13, 0x29b71838713e75ef4f6875aba85d00e3c6e03689b16d79695aaa93e68c7452a1e4fbe7cb3d59d34dd46cc35e1a70caa5592a4117889c37d1a88cd45cc2d712908143d81cf0dc86282e015209e04981e60db05202680f206e02f01700b205602080d804a02401000780260120078034012008002000c002000⟩⟩
theorem candidate01039_checked : Checked candidate01039 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457046126848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01040 : Description := ⟨76, ⟨13, 0x14ee8c04325f3af8975aba85d1edc06d13649aecd2b54d28313e68c7453a248fbe7cb3d69d98dd46cc35a9a80caa55929e943892245e2218f8872e37d1a70cc45cc2d112908143d81d20dd86282e015509f04981e60db03c81b80b8056024810407e036013009004201e009804802000f006802c012008002000c002000⟩⟩
theorem candidate01040_checked : Checked candidate01040 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457050353664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01041 : Description := ⟨68, ⟨13, 0x11707d03ac9d48dc36cfb63daecd2e54d28313e68c43e49ba0d726a03289570a4e50e23a11807f63e21bf8d8469433117509484061ea0ea06ec31416e0ab84f824c0f106d827012208103b81700ac04902080fc06c028013809004401e00e806c0220100078030016009002000c002000⟩⟩
theorem candidate01041_checked : Checked candidate01041 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457058156544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01042 : Description := ⟨68, ⟨13, 0x118e8543dedd42e8c6d13649abad2b55c2a254189d23e59ebcecc6cc35a9a1ccaa55929e943892245e2240f2469c3181730b304d61ec0e906883141700aa84fc24a0f306d82900f206f03701740ac04902080dc06c030013009404201e009804802000f0068028012008002800c002000⟩⟩
theorem candidate01042_checked : Checked candidate01042 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457182474240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01043 : Description := ⟨76, ⟨13, 0x14238ca457e176f7e7603a91d12dc66cfb63dabad2e55c2a254189d24541ff0fc07c93d99b98d726873289570a4e50e23a118088842d1fd8f246f43611a50c605d42ce13588203d41d40d106282dc15709f84941e20db04882040ba056024810406e036013809404401e00e806c0220100078030014009002800c002000⟩⟩
theorem candidate01043_checked : Checked candidate01043 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457190277120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01044 : Description := ⟨84, ⟨13, 0x14e8a1050023231828b142e9f16ed8761ba25b82da46ca35e1ac4d2d55daa6d50c9d34dfa2a0ff87e03e49eccdd66ce35a1a74d0466c3291564a7652a28892b492847322210b47f63c91be0d8c69033418b0ba459c26b11008183ac1b80d205b42ae13f09283d01b005f02b0124082035019809c04a02200f00700360130090030014009002800c004000⟩⟩
theorem candidate01044_checked : Checked candidate01044 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457207052288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01045 : Description := ⟨81, ⟨13, 0x29db450a1145c61690987d03df1ed6f52763ba15c78dc36cfb625aead5c698aa9d3a89bd46222d90f87ff3ef1ed8dd06bf34f9a18c9e55c29d14388e84602258dfc6c23461990c646022e51648a744d625210187a83b41ba0d085cc2a413f09303c41b409104081b40d005902b010406c031014009c03c01d008003c0120070028010006000⟩⟩
theorem candidate01045_checked : Checked candidate01045 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17457297494272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01046 : Description := ⟨74, ⟨13, 0x53fe31cf9d7bdbae9d42e8c70536edb44d92695aae14188c73f21f2cf5e7983b31cd0dca6cc35a9954ab253d24891dc8bc4481e48d385cc2cc14e89ac4a42050f6074834618a0b8055427e0f306d82900de06e02e815c0ac04901b80d8060026012808403e01e009804802000d0050024010005002000c002000⟩⟩
theorem candidate01046_checked : Checked candidate01046 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17461475344384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01047 : Description := ⟨69, ⟨13, 0x29ff18e7cebae9d42e0a6ddb689a56ab84639f90f967343729b30caa55925512448ee45e1e48b9856c29d14209ac4a42050f6068c3141700ac04fc1e60db05202040de06e03401780ba05702b012406e036018009804a01f00f006c026012008804001a00a004802000c005002000c002000⟩⟩
theorem candidate01047_checked : Checked candidate01047 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17462012149760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01048 : Description := ⟨76, ⟨13, 0x14e5a104a462c50ba761ba61d08dc16ca3589a8cd2d5d92a7550c9d34569f80f5c6eb35a1a78d0466b3291564a544f826312b48e645a21690506f834818b0c085d22ce135888040c1d60d206182da15709284341e80d804d81dc0be058020810007e035019809c0460220100070036013009003001600a002800c004000⟩⟩
theorem candidate01048_checked : Checked candidate01048 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17463448176640 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01049 : Description := ⟨84, ⟨13, 0x15fca28508a81328e8b9c2d2136fa07b5bce5e0eec7757370db54d896ae350da62bb255227513768c44189f78f8a7ab3811ba0d9e6bf34319b4c9e55c2a2930c8e845b2200dfc6cc3461998c646002e51648a744d625210187a83b41a10c405cc2a412608683c41b409a03b81b40d005902c0104080031014009c04001d00780380160070028010006000⟩⟩
theorem candidate01049_checked : Checked candidate01049 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17463538618624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01050 : Description := ⟨82, ⟨13, 0x5dce84740a94746521f70bb8513dfdd80ea77433719b5ad5d6a234b9764ab8512a7493728a940a9f80f8e7b03811b98d9a6873371944ab853e29393d498647422d91148283e21e48de86c231817f8ba84101ef0de068831216e0ac04942180f106d81a00bc058020810006e036018009804402000e806c02200f007002c0140090030014002000⟩⟩
theorem candidate01050_checked : Checked candidate01050 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17463893823488 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01051 : Description := ⟨87, ⟨13, 0xbb8538a841407948c6461fd0ba850bbc5d86eaa7433705b50d916b13525a5abb255daa854449d34dd22a502a7e03e39ec0dd66d235b1a78d046693291564a544f826312b48e645a22290507c43c91be0d8c69a31617e8ba447222010307b43a21a40c585b42b012508603d01b006802c010408003301900c004c0220100070036013009002c0140090030014004000⟩⟩
theorem candidate01051_checked : Checked candidate01051 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17463910598656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01052 : Description := ⟨72, ⟨12, 0xf9df7ff68eb5ea1e86e23dc0da2d2b8c78a98927df7cb7b074d6ea6cc65555953e5274aa45e4453e239737d2e62b629d28426b2522051ec1bc18a1701581260f30db07906e06805e05c05805604103603002602402001e01b01301201100f00d00b009008006005004003001000⟩⟩
theorem candidate01052_checked : Checked candidate01052 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17466172899328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01053 : Description := ⟨86, ⟨13, 0x53be32317a8574255f34f8675c3a7dd24e587133835b30d776af3515576a9d4ec26fd1888a940a9f88f927ac3cd9e08ed275039b9ac8d426883379564a8447722f110c8283e21e48df06c63491998c686022e71660a744d625211007483781a30c5056827a12408583640c005f02d00fc06a030014009c04c022009804801a00b005002400e005002000c004001⟩⟩
theorem candidate01053_checked : Checked candidate01053 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17469813227520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01054 : Description := ⟨81, ⟨13, 0x23231738574255f34f8375c3a7dcb0e26706b5ddabcd4555daa753b09bf46222b4fc47c93c11d40e6e6a134419bcab253e25511dc8bc42d20a0fec7c43c91be0d8c66631a1808b9c59c29d13589484401d40de068c31413d092042c1b207703681800be05a01f80d4050027011006c026012008803401800b005002400e005002000c004001⟩⟩
theorem candidate01054_checked : Checked candidate01054 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17469821550592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01055 : Description := ⟨90, ⟨13, 0x540a84940b8ca45de1630987d03dfdd7aea472c3899c1adcd6da35ddabcd4569a2ae15429d64dea3111528153f11f24f0475039b9c14dc86cb3509a20cde64e2ae14f88f246022290507c43c91bd0d8469633318d0c045ca2b614e8a104d625210187a83781a30c505b827a12408583d81b206802f00dc06c03101800a004e026011006c02200b005002400e0060028010006001⟩⟩
theorem candidate01055_checked : Checked candidate01055 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17470316482560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01056 : Description := ⟨74, ⟨13, 0x46022290c984bbc1dd68ea3747b6f9b4ca9a52ba8f94189f34e0a2550c683140c1f78f9a7ad3b31c6cdd06d029e94389b84c3248917c8863e21cb8df46ca34e1988bfc5cc2d112907b83ae1a10c405bc2aa13e09301e40c005602a812408203f014008403c01d009804001e00e006802c012008002000c004000⟩⟩
theorem candidate01056_checked : Checked candidate01056 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17489262346240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01057 : Description := ⟨69, ⟨13, 0x2804f0a758ba99b7cda654d295d47ca0c4f9a70505c7ca3741b40d726a03351944a7652a28893e09be4c625692508e64621fd8f887603971be8d944a41ee0eb06f433e1860b6855c27c12604e01dc0c005602a812408203f014009004602200f0074036013006002c012008002000c004000⟩⟩
theorem candidate01057_checked : Checked candidate01057 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17489270409216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01058 : Description := ⟨81, ⟨13, 0x28494088c144c21cb09a7c5bc8ddb0ea6706b6e9b52d5069baa6d4a8a094eb26f91508473fe1f88f947373721b4cd1066732714ec9f04df25692508c44442168fec7923b01b28d206682fd1720b3853a26b12908803dc1d60dc06182da12408583c81ba06f030012406e03501900c4050025011808803601300600280120080028010006002⟩⟩
theorem candidate01058_checked : Checked candidate01058 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17493678753792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01059 : Description := ⟨78, ⟨13, 0x50222610e585bc269e14eb17533899bb6da96a834dd53aa54504a75137c8ad4171f28ea07053699a84cce64e29513e098c4ad23991887f63e21d80e5c6fa3651a40c6c5fa2e41670a744d625211007b83ac19f0c305b427a10b0790374138077030010407e03501900c40500240118088036013006002c0120080028010006002⟩⟩
theorem candidate01059_checked : Checked candidate01059 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17497839503360 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01060 : Description := ⟨87, ⟨13, 0x8afc4b61f70e2858425dea4f20783bb55d78ea3744b829b7eda6544a95d44aa0c4ed27050f884a4189ffcfcc7cd3d99cd0dd26d029394389ea4dc26192a892247822f911085a3fb1e48ec06fc3651a50c605fe2e61670a744d6252110081c3dc1ba0d086202de15709f82040ae05602a812403e01e00e806c022010007803801a00c0050024010005002000c004000⟩⟩
theorem candidate01060_checked : Checked candidate01060 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17558120169472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01061 : Description := ⟨87, ⟨13, 0x87dc2c212ef6b79cbc1dddcebc751ba19caae237053761b7eda6512a769382895431a0c50307e63e69ec0efe74d39a1c08dd26d029f149c9ea4c325511e08be44520a0f887923971bf0d946302ff1730ad853a284135894847222010387b83a61a10c405bc2b006802c015c0ac055018008003e01e00e806c02200f007003401600a004802000c005002000c004000⟩⟩
theorem candidate01061_checked : Checked candidate01061 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17566970150912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01062 : Description := ⟨96, ⟨13, 0x146ca10d0221fd0b384d3c29d7eea674139c5cb0e3f7133835be8ddb6e136a5ad2d5069ba8893ae9be4171f8cf947ac3cd9e08ed275039b9c78e0a6ec3699ae8d42680333993898c47b23110b48283fb1f10f247603971bf0d9462c2fd1720ad853a284135894847222010387b833e1860b6855827a12408583c81ba07703400fc06603201880c0048023011006c01800b00500240100060028010006002⟩⟩
theorem candidate01062_checked : Checked candidate01062 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17583596242944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01063 : Description := ⟨87, ⟨13, 0x87dc2c212ef0475cba81d04e7172c38fdc4ce0d6fa376db84da9512a76938282e3f19f28f5879b3c11da4ea073738f1c14dd86d326191e08be42d20a0fec7c43c91d80e5c6fc36518c0bfc5cc2b614e8a104d625211c888040e1ee0ea86f02ac13d092042c1e407703401700b605a01f80c0048023011006c01e00e006803001600a004802000c005002000c004001⟩⟩
theorem candidate01063_checked : Checked candidate01063 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17583613018112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01064 : Description := ⟨61, ⟨13, 0x272d32688cbc95adcd296883301888b0451ba44108670232997b0b1255728813d09b24c220b0f9075e37d1980c005d029f13688e040c1b90c485c427808f04482180aa054028814009c04501a009404001d00e006803001600a804c01c0080038008002000⟩⟩
theorem candidate01064_checked : Checked candidate01064 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17787283079168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01065 : Description := ⟨62, ⟨13, 0x567645f1f48af4372070fce79c3ba1cbae287062d252ac77b3a59cd8e0469e30117b0b8459029613e89484111f20f1c6fc31a14f89a04a21ee0c504f024a10d04602240f606902d01540a805001e80c4058022010007403801600680280100070018008002000⟩⟩
theorem candidate01065_checked : Checked candidate01065 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17848351097088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01066 : Description := ⟨63, ⟨13, 0xacec8be070e5d7143831a20b4958f2a2140c95647c218902477b3a59cd8e0469e30297b0b7e58d29493dc94e4111f20f1c6fc31a14f89a04a21ee0c504f024a10d04601a40b405502a01440a004301e80c4058022010007403801600680280100070018008002000⟩⟩
theorem candidate01066_checked : Checked candidate01066 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17848351162368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01067 : Description := ⟨58, ⟨13, 0x511e08702d801bf45edaf3b772b95dc4a96d4aba4b51f6897432a03cf0274f2090f8072e33314e09a840e1ee0d1862827c12608682b013c08c04401a40c605a02a81500a0031015808803a01c00c805c02c00d005802000e0040018008002000⟩⟩
theorem candidate01067_checked : Checked candidate01067 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17848479056128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01068 : Description := ⟨59, ⟨13, 0x816b95dc4ad1050325c12ae92a47c22510c48123c09d3cc0a5bf2c694a49ee4a72090f8072e33314e09a840e1ee0d1862827c126086823011006903181680aa0540288140086031015808803a01c00c805c02c00d005802000e0040018008002000⟩⟩
theorem candidate01068_checked : Checked candidate01068 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17848487444480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01069 : Description := ⟨58, ⟨13, 0x40b1cace0c6882c79510a064ab23e10c48123c01cd8c0a5bf2c694a49ee4a72098f1c6fc31a14d89444401ee0de062827e125086823011006903201680aa0540288140086031016008803a01c00c805c02c00d005002000e0050018008002000⟩⟩
theorem candidate01069_checked : Checked candidate01069 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17848619565056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01070 : Description := ⟨67, ⟨13, 0xa1a4ca65dd22c8e13d5dc56d79693b441886c185a52bb13e68753fe1d24e0469c32897b0b76589293142c9bc4c125491e082c3fa1ef8f2075e36519a8b9853e26d11c06e434413c086036c11205a02a81440a004701d809404402000e806803001600a803c01a0090040008002000⟩⟩
theorem candidate01070_checked : Checked candidate01070 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17852730998784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01071 : Description := ⟨60, ⟨13, 0x15b6a24c9223ef145828bf45e3ee76720b831bd6b72590a9bd2f68fb4249e80ed673638a94309b44912098f1c6fc33218d09a84a21ee0dd862824a10d04a023011006902d01540a8050018808803a01c00c805c02c01000680280100070018008002000⟩⟩
theorem candidate01071_checked : Checked candidate01071 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17856668434688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01072 : Description := ⟨61, ⟨13, 0x24711f086f40e1f9cf2271f3831bdcb72590a9bd2ac8453fe1e00e6c69d30117b0b84590288137884e4001e38ea86fc31a14f89a04a21ee0dc862824a10d04602240ec07103481680aa05402800c4058025011007403801600680280100070018008002000⟩⟩
theorem candidate01072_checked : Checked candidate01072 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17856672596224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01073 : Description := ⟨62, ⟨13, 0x49223ef0387913831a20b6258d29bd41095647c2114ff87803b41cd8e3069d30297b0b7e58d28813788543fd1e38eb46fc31a14f89a04a21ee0dc862824a10d04601a40b405502a01440a003e01c80c4058025011007403801600680280100070018008002000⟩⟩
theorem candidate01073_checked : Checked candidate01073 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17856672661504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01074 : Description := ⟨62, ⟨13, 0x5d5e3e904581c3f29e44eea737b831be0a6f4bda5591f68453fe1e00e6c69d30117b0b84590288137878e37e18d0aec53e27e13409444661ee0dc862824a10d04602240d206503101680aa05402800c4058025011007403801600680280100070018008002000⟩⟩
theorem candidate01074_checked : Checked candidate01074 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857201078528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01075 : Description := ⟨61, ⟨13, 0x228b0517e8bc7dc18d1058f29bd2de8f4424a050f3273638d1814b7e58d28613689224131e38df866431a15c0a044d425111b07b837618a092843411808803481680aa054028814006202d015008803a01c00c805c02c01000680280100070018008002000⟩⟩
theorem candidate01075_checked : Checked candidate01075 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857205305344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01076 : Description := ⟨65, ⟨13, 0x27d905081bbf39e3ee0f6882c794de9704aba4a91f087b4249cc8dd268531e9884c085eb2c4936895249121710547963af1990adc53c283135093c4701ee0dd862824610d04601a40b405502a01440a0031015808803e01d00e006002e01500800340100070018008002000⟩⟩
theorem candidate01076_checked : Checked candidate01076 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857211547648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01077 : Description := ⟨63, ⟨13, 0x9f347d228afce78fb831a20b1e537a3e109273631d1884b765892861368952491216104c78e3af1bf0cc863428313509444701ee0dd862824a10d046022411006902d01540a805102800c404401d00e006803201800b805802a01000680280100070018008002000⟩⟩
theorem candidate01077_checked : Checked candidate01077 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857213628416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01078 : Description := ⟨56, ⟨13, 0x17d068830616c4b1a542a8213ae95647c21e90607803b41cd8e306822f59634a1e4c520a8ff47963ad18b88803dc1bc0c504fc21a08c03481900b405502a01440a003e01c80cc06202c0110074038017006802000e0050018008002000⟩⟩
theorem candidate01078_checked : Checked candidate01078 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17860967612416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01079 : Description := ⟨60, ⟨13, 0x12328a3bf45c4ad1060c2d2563ca6c4eba5bd1e88934182050f3274f39b1c68d045eb2c6943c98a4101f00f2c72e33318b8a044d42360f7062827c10d04601a40b405502a01440a003d01980c405a02a0110074038017006802c0100070018008002000⟩⟩
theorem candidate01079_checked : Checked candidate01079 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17861231853568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01080 : Description := ⟨59, ⟨13, 0x9f63f39a20c1858f275d2ac8f843d20c0f0073634118f4c426042f59624a5050f26292a485c4151e58ebc62e28311c08803dc1bc0c504fc21a08c03481900b405502a01440a003301880b004401d00e006002e015006802000e0050018008002000⟩⟩
theorem candidate01080_checked : Checked candidate01080 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17861504417792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01081 : Description := ⟨60, ⟨13, 0x10fa7a83891a20c18576289135098f449a1e90287673a71c68c0a5bf2c694349824781f08f206ca3191808ae053628613488d84401bc0d104fc21808c04401a40b405502a01440a0031015008803a01c00c805c02c00f00680240100070028008002000⟩⟩
theorem candidate01081_checked : Checked candidate01081 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17861564235776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01082 : Description := ⟨63, ⟨13, 0x9f6470a07cf537123441830aec51225552548783f19d38e6a68431e9884c085eb2c494a0a1e4c52548fe87c23af1b28c0456e29913489504702200de068027e10c04601a40b405502a01440a0031017009004401d00e006002e01500680240100070028008002000⟩⟩
theorem candidate01082_checked : Checked candidate01082 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17861570478080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01083 : Description := ⟨76, ⟨13, 0x13e99e84ede6733208fa476df9cfb56ac3505a52d1367d33858c6c4a58f2c151f08df34119acca663a3109818bda5d62dd9688b1257029314349e84db26190b08263af1cb0df86002e814189a847021f0f706882e212508681ac0b605502a00cc04601d00e006803201800b805402800f00700280100070018008002000⟩⟩
theorem candidate01083_checked : Checked candidate01083 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18272751714304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01084 : Description := ⟨66, ⟨13, 0x4e662971167abbaedc56da86b7344d986cae534a8e52208de43a9f94e926d230317c4ab252628593788ec4161fd0f7c6c633018c8c0453e26d11c08183da1b90d105c427810c07a023c10c08402a013809804701d80d004a02000e0068030015009804801e0090038008002000⟩⟩
theorem candidate01084_checked : Checked candidate01084 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18300498116608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01085 : Description := ⟨64, ⟨12, 0xfe6f1ce56dbcd41d29d13b19a88a0b9108f885d8468177806e666b65360a5ed5ba5a358d5294f24db4ac41331a3002e829b2202061ee1bc17113f12510d06f06405b05505404e04603702c02301d01c01901701300e00a008007005003002001000⟩⟩
theorem candidate01085_checked : Checked candidate01085 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18328582160384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01086 : Description := ⟨64, ⟨13, 0x12e98e13d5de44e1d6bcb4ada26c135fe2c115d89f343aa114d3865530317c4b1252628593789524161fd0f7c75e37d1b28cd45cc29f14189a03721a20c505c02780f306d825810c07902b013808e04101d80b004a02000f0068030015009803c01a009004000c002000⟩⟩
theorem candidate01086_checked : Checked candidate01086 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18333766811648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01087 : Description := ⟨70, ⟨13, 0x54b62270af8033f45e3eebb6d33509a52d1357628f53b292447a224d0927e53b29c68da066c3299828bda5ba2d196349b44761f08df46ca33218c8c045d02b814089a846c2060f706ec34418a0b881fc0ac05502a013808e02d015007803a01c00c805c02601000780240100070018008002000⟩⟩
theorem candidate01087_checked : Checked candidate01087 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18335087525888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01088 : Description := ⟨71, ⟨13, 0x9f4c70a2270af7e73c7dd76da66a134a5a26aec51ea7651f08493f29b40cd865331d1884c0c5ed2d19624a4c4da23b0fe87c23af1be8d946643191808ba050626a11c08183dc1bb0d106282e208603f81580aa054027011c03c01d00e006803201800b805402601000780240100070018008002000⟩⟩
theorem candidate01088_checked : Checked candidate01088 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18335095848960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01089 : Description := ⟨65, ⟨13, 0x2ac91458033f45e34dbc6a0b4a5a26b19537a4911e885f4221e64e346e6335994cc145ed2dd168cb1a50c2098cc86343001740ae050226a11b08183dc1bb0b8849421a07d037816c0aa054027011406e02d015008c03a01c00c805c02601000700280100070018008002000⟩⟩
theorem candidate01089_checked : Checked candidate01089 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18337167900672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01090 : Description := ⟨66, ⟨13, 0x4fa63df1457e73c69b78d41694b44d632a6f47c2110dcc66b32998e8c426062f6968cb1250c27a10b08263af1990c686002e814189a84702060f706ec2e212508682180fa06f02d81540a804e02280dc04601d00e006803201800b805402601000700280100070018008002000⟩⟩
theorem candidate01090_checked : Checked candidate01090 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18337176223744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01091 : Description := ⟨76, ⟨13, 0x13e996a48fe44d145889c2b9f9cf1f6e0b509a50d135ff2da56a0a6f51ea7611f084937599b0ca463a3109818bda5a32c494309b44a924891dc8584131fd0f8479237c1990c686022e714189a84702060f706ec31412507a02180b405602a013804401e00e006803201800b805402601000680280120070018008002000⟩⟩
theorem candidate01091_checked : Checked candidate01091 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18338216411136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01092 : Description := ⟨65, ⟨13, 0x2c4f1158574019c54dc169e34a1a26be65b4ad314749d849223d10be8143e51e64eca74a3759948b745a326e91dc7bc37c1998c685fc2e715c09b046c2060c384f824a10a07a02340ea05a02a013807a03b01900b40540230110078038019009803401600a0038008002000⟩⟩
theorem candidate01092_checked : Checked candidate01092 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18344382111744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01093 : Description := ⟨66, ⟨13, 0x54ce96b1f08de456df92f5779138f9bdcda56ac34a5642af253523710ea8453c01b3cd3a6823299834be25c22c2942c9bc4272000ea86fc3641740a7c4d01b90d106282e212508682100ec071035817c0aa05402380cc058027012807403801200780280100070018008002000⟩⟩
theorem candidate01093_checked : Checked candidate01093 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18368847446272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01094 : Description := ⟨72, ⟨13, 0x152d889c13a0650037e8bd45e3eda66a1344d5d8a3d4b8a57124c8f443da12502876538d1b40cd860a2f696fcb1a50c26d12447c23651990c0456629c14089a84a423610387b83761a30c5049811806902d01580aa05401880bc05a02a011007803a01c00c805c02000d004802000e0040018008002000⟩⟩
theorem candidate01094_checked : Checked candidate01094 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18407026130944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01095 : Description := ⟨75, ⟨13, 0x9f4c70a22704b8194001f9cf5178fb699a84d1357628f52ea95c49523e10f684936819b0c7462130317b4b7658928613689524911fd0f8475e3651990c0456a29c14189a84a423810387b83761a30c5049811806902d01580aa054018808803c01d00e006803201800b805402000d004802000e0040018008002000⟩⟩
theorem candidate01095_checked : Checked candidate01095 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18407034454016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01096 : Description := ⟨67, ⟨13, 0xaa5d2762c31327f6bee1b78d41694b44d636b0054229412168db42ea118f007683809b98d6866b3299828be25a12ba14a49e442a1fe8d246343001740a7c4d021d10307b82e212508681bc0b605502a013408c03e01b80d4058029011807403801300700280100070018008002000⟩⟩
theorem candidate01096_checked : Checked candidate01096 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18465484275712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01097 : Description := ⟨67, ⟨13, 0xa4b4a8e3b6fb575039d9c82d41689af3560aa5546fa17cf947943b21c6cd6e66b30517b4b4457026d92408be42a2098ff472c37e18d0c00570281135087c3dc155092843411806902d81680aa05401f00c405a023011008403a01c00c805c02800e00680280100070018008002000⟩⟩
theorem candidate01097_checked : Checked candidate01097 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18550305652736 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01098 : Description := ⟨65, ⟨13, 0x2d5346b8a3c401fa2dd56a0b4a59f4c5e58f2c054d8a1e4b7a3d112685f4159e64e6c71a37f9a08cd66532f81634a1e4c02080f2c6663171800ba050223610f87b82e213e08681c00b605502a014408803d01c00cc05a02a0118074038014007002c0100070018008002000⟩⟩
theorem candidate01098_checked : Checked candidate01098 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18822230786048 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01099 : Description := ⟨63, ⟨13, 0x87abd41baed3f694b3e98bcaec50fa6a128289343d2184ece71a38099a4ca66052f716fcb4458d2868f2072c36518c8ba057029b14308d83781a20c485c427e10c03e01a80c205502a014408803201500a403a01c00c805802800f00700240100070028008002000⟩⟩
theorem candidate01099_checked : Checked candidate01099 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 18822563168256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate01099_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch010

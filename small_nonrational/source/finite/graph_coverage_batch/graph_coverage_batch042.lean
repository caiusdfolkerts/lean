module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch042
open Papers.RationalityTen GraphCandidateCoverage

def candidate04200 : Description := ⟨82, ⟨13, 0x556621aff87cc3c69e06deb6df35c5a82d29599ac6153ca374b9230908882d3d69e58dd06b734d99acca65ef2dd155c9844431f00eb472e37d1800ba056626a11b07b83761a30b8855427c12608682a412807d036018c0c005b02a815009c04501f80e406802f01580a8050023010807403801700b004c02000e005802000e0040018008002000⟩⟩
theorem candidate04200_checked : Checked candidate04200 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6791622623232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04201 : Description := ⟨88, ⟨13, 0x12098f745d221affb7cc3c69e06dee6df35c5a82d29599ac6153ca37492a30908882d38c1ba0d3666b32998e0c406072f79750aae53f26110ac7c03971be8d306002e815a89a84701ee0dd868c2e215709f049821a08603e81dc0e206c03181800b605502a013808a03f01c80d0056028011807403801b00d005c02c015009804001c00c005802000e0040018008002000⟩⟩
theorem candidate04201_checked : Checked candidate04201 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6791630946304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04202 : Description := ⟨76, ⟨12, 0xf99f02debda5d71d5ad29b33a9e9729268f68c389182c7ad7966cf6b769b6846535ef57155850e4da4c14433e03ad3973643192e82b326a2362071bb18a17115513e12610d09406c06305f05c05505403f03903402f02b02a02702402101d01c01701601201000f00b008007004003002001000⟩⟩
theorem candidate04202_checked : Checked candidate04202 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6823834877952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04203 : Description := ⟨79, ⟨13, 0xa7c518a11ce9a701b6fdb40d5b69e2f2956ea38510a30d08882d3749a14c705d42dd94fc9b04a924891708583c51d78df86c433218d0bf856a24e11c081c3d61bb0d1861c2140af04d825412208d04601a40b405702a815008a04001d00d8064031015809c04602200f807803a01c00d806802a01000680280100070020008002000⟩⟩
theorem candidate04203_checked : Checked candidate04203 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6825520930816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04204 : Description := ⟨75, ⟨12, 0xf02eb9e20e09da6d27c91c2dc14b7fb33a9aa0488f82c8127e374a7337186d06515ef53d52450e4da4c14a74914784433c83ad3973653312e626a2071ee1bb18a13e1260db07306305c05a05605504904804303f03b03902b02402201e01d01701601000f00d00b009008004003002001000⟩⟩
theorem candidate04204_checked : Checked candidate04204 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6839899062272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04205 : Description := ⟨67, ⟨13, 0xb374ba9ef4f6470eb81dbe0da6693ad3914a8454079ff0e627023681a70ca252126092908f03df1bf0d946302e613409444661ee0e786e434418a09e04941b60a404f025810007b03901880bc05a02b015407603a016009404402000f007402c00f00680280120080018008002000⟩⟩
theorem candidate04205_checked : Checked candidate04205 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6840291197184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04206 : Description := ⟨72, ⟨13, 0x1224772b881c0eda6693b24585ac145a7229d11c74a3989c68da06512f794f4a4850e26d130494e49123c105072e37e1b28cc46302e6135094446c1ee0e906ec34418a09f04941b609e03981c80b405602a812409004301d80e8054026011007803a01700b004001e00d00580280120080018008002000⟩⟩
theorem candidate04206_checked : Checked candidate04206 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6840295424000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04207 : Description := ⟨75, ⟨12, 0xe20e09da6d22c91c2dc14a9ca39a069f088f82c8127e374a7336d069b68466c6386206075ef5d45bb53b5224a54453c83af39736532f2e42b526a2382071ee19f16d13e1260d808c07306305605504904804303b03403102b02402201e01d01c01b01a01701601500b009008004003002000⟩⟩
theorem candidate04207_checked : Checked candidate04207 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6840419092480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04208 : Description := ⟨67, ⟨13, 0xaba437a090ffc77fba01cd8d2562428dd3e095a42120a4f5674b38a9c08d3464f26c91e08be3aa1980c646002b013408cc40e1ee0d086202de15209e049821a0da04d02500f8071034819c0c606202c815408a04401a00c405802b010007402c00f0070034010007002000c004000⟩⟩
theorem candidate04208_checked : Checked candidate04208 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6854969426176 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04209 : Description := ⟨72, ⟨13, 0x120977e37b9a44c48599aa7946ea084f82110fc67ca38c1a6cd0866b31c1880c0e5ef2ea16ec9ae4be2158f8072e32f1720ad44d423810387b833e1860b6855c27c126086836013e08c03b81c40c6055022811007e03901a00c4056024011808803a01c00d806802e01600a8030016008002000c004000⟩⟩
theorem candidate04209_checked : Checked candidate04209 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6854981715968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04210 : Description := ⟨85, ⟨13, 0x221f0c67813ae5c40e096d335c5ab4d4251ca7c10587e33a51cccda069b34219b0c7062030397bcba85bb29f9498a1c4da26092a49224782228f2075e3971b28c646022b513508e040e1ee0dd862827c12604601cc0d806903181700b405602a815007603401880ac04802200f007403801b00d005c02c015008003c01a00b004802000e0040018008002000⟩⟩
theorem candidate04210_checked : Checked candidate04210 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6857598959616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04211 : Description := ⟨71, ⟨12, 0xf1adbcd87d41d29c79b1ba9ba848a786084479471b6e666b6535ef5a457055753d4c248f42a3c739634933231a3002e826a25121f2061ee1d21bb17115512510d09007d06f05b05505404904503e03703502602302101d01c01701601401301000e00a008007003002001000⟩⟩
theorem candidate04211_checked : Checked candidate04211 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6912018022400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04212 : Description := ⟨72, ⟨12, 0xecfe07da6d27c91c2eb66a818a788e8157f979476673171b6d06b56515ef57053d52450e4da4c147842a3e139637e3653182e626a25121f1ee1d21bb1a218a1551250db07a07205a05605504904804203e03a02602202101e01d01701601401000f00d00a009008003002001000⟩⟩
theorem candidate04212_checked : Checked candidate04212 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6977465942016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04213 : Description := ⟨75, ⟨13, 0x861bb3db7eda66adb50985c9ed4b9229d1208153fc9e5cdd26d035b1a14cd85ef2b814f49b43e11cb0df86ca33218d0c0456626a10f881c3dc1d20dd868c31409504601e80e406903181680ae05602a815009204201d00c405e02b013008803e01e00e807002e01600a004001a00a004802000e0040018008002000⟩⟩
theorem candidate04213_checked : Checked candidate04213 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6982278905856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04214 : Description := ⟨79, ⟨13, 0x982430dd9edbf6d3356da84c2e4f69fe4dd26d034299b0c7062030397bcbaa570292936895442c1f08e586fc3651a58cc863430115a89a843e2070f707503761a30c5025411808103d01c80d206302d015c0ac05502a012408403a01880ac04401f00f007403801b00d005c02c014008804001a00a004802000e0040018008002000⟩⟩
theorem candidate04214_checked : Checked candidate04214 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6982287228928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04215 : Description := ⟨72, ⟨13, 0x10f3768b75da4ec605b32a0543a940454a23902a7fb3d79e50e3670135a9944bde570292136c92047822f90a87c23961bf0d946302ff1730b304d21d20de068831215509f84942180db03e01c80c205a02a812008803e01d00c0052026011008403a01700b005001e00e00680280120080028008002000⟩⟩
theorem candidate04215_checked : Checked candidate04215 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6983905247232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04216 : Description := ⟨86, ⟨13, 0x469618af657813ae5c40e096eab699ab4d42567a7bd11e82c3f19d28e666ff3681a10cd8638310181cbde5d52b814f89824aa24811e088a3c81b28d2c6663191808ad44d421f10387b83a818a09f049811808003981c00d206302e01680ac05502a012007603801880ac04802200f007403801b00d005c02c014008803c01a00b004802000e0040018008002000⟩⟩
theorem candidate04216_checked : Checked candidate04216 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6986447978496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04217 : Description := ⟨82, ⟨13, 0x4315e06ea07043755b7ed5b6a0a7bd05a7ca3991bfcdd268533598e0c406072f79754ae053e29293d49b64c225512408be44521610507c03c71bf0d2c66631a1800ad44d421f10387b83a81a309f0434118070034818c0b605a02b81540a803801880ac04602200f807403801b00d005c02c014008803801a00b005002000e0040018008002000⟩⟩
theorem candidate04217_checked : Checked candidate04217 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6988528353280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04218 : Description := ⟨79, ⟨13, 0xa1743da15aecc703b699ab0d4251027b53ae98b4a0236d1548453a61cc4e026d034e9a08cd8607293130491c4782160df86ca3011658ad050826812888e443a1ee0ea86e434418a0ac049413a08c03901ac0d205a02b01540a804201d00cc06203001600a404a02200f007403801a00b003c01a00a004802000e0060018008002000⟩⟩
theorem candidate04218_checked : Checked candidate04218 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6995161677824 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04219 : Description := ⟨82, ⟨13, 0x430e090ecf736b6fdb4cd5b6a127b52e47f93cb9ba4da068533618e0c406072f79754ae053f26d10b07c23961bf0d9466431a1808b3450826a11c887c40e1ee0ea86ec34618a0ac025411807a03901a40ce06302d015c0ac05502a010807403101780ac04401f00f007403801b00d005c02c0140080034014009004001c00c0040018008002000⟩⟩
theorem candidate04219_checked : Checked candidate04219 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 6999458709504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04220 : Description := ⟨84, ⟨13, 0x11a5862bc09d72e20704b755b4cd5a6a12dfd668acf4f7a5c912282c3f19eb4f2c7663a51ccce366ff3681adcd0866c2f795c098249023c110c7903651998c646022b3135087c40e1ee0c5055427c12604601cc0e006903181700b405602a815007e03b01c00c405e02b012008804201e00e807002e01600a003c01a00b004802000e0040018008002000⟩⟩
theorem candidate04220_checked : Checked candidate04220 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7003082653696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04221 : Description := ⟨88, ⟨13, 0x10307d8bc09da2eb97113825baeda66ad35092b48db4161fecfc674c3999c04da068433618e0c406072f79754ae052626092408f04442158fec7c23c81d80e586ca34c18c8c0459c2b514e881c3dc1bc0c5055c27e12604601a40c806303081700b405602a815006202c01580a404802200f007403801b00d005c02c0140078034018009004001c00a0040018008002000⟩⟩
theorem candidate04221_checked : Checked candidate04221 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7003355217920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04222 : Description := ⟨89, ⟨13, 0x234b0c58243d9de04eb97103825baada66ad350959e9ef4b922450587e33a51cccdfe6d034219b0c7062030397bcbaa57029313049204782228f206ca33318c8c0459a28413508e443e2070f7075431415809f049811807303801a40ce06302e01680ac05502a00ec07003101780ac04802200f007403801b00d005c02c0140078034016009004001c00c0040018008002000⟩⟩
theorem candidate04222_checked : Checked candidate04222 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7003619459072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04223 : Description := ⟨98, ⟨13, 0x41e60c30488184059f62f677813b45d72e22704b75db4cd5a6a1268d3169724ad25011b68914161fecfc674c3999c04da068433618e0c406072f79754ae052626092408f03e11e40e586ca3191808a7450823910387b83aa1bc0c5056027e12604601a40d0067032018c0c205c02d01580aa05401880c005e02c01580a404802200f007403801b00d005c02c0140078034012008003801800a0040018008002000⟩⟩
theorem candidate04223_checked : Checked candidate04223 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7003883700224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04224 : Description := ⟨69, ⟨13, 0x29b116e86fc121ffaf9874039b1be2dbe6c4b495532a374f825691848423d59d2ce046e834d193caae4d926111dc8be37d1a30cc06002b013407b831016f0a904f024c10d06d02e013406d034819c0c606002c815408a03401880b0056028010007402c0130070034010007002000c004000⟩⟩
theorem candidate04224_checked : Checked candidate04224 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7048242954496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04225 : Description := ⟨82, ⟨13, 0x443e18cf9875c3881c12dbe6d335c5a84a9c51ca7c12e4927461229d1208153f11d28e666e83681ad8d3666c2f7955ca7a4da24891dc7903971be8d946022b313507b83a41bb0d1862827c12604601cc0d806903181800b405602a815009203b01a00c405e02b014009804401e00e807002e016009804001a00b004802000e0040018008002000⟩⟩
theorem candidate04225_checked : Checked candidate04225 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7050864164864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04226 : Description := ⟨76, ⟨13, 0x1431856ba7db4ad6e6ac29b53e09d74c5a3711548453fe1f24f6074b3811b3cd046072ac149898247822f10b078e37e1b20cc05962b414209a04a22390ea86e434418a0ac04f024a10d04782300d606902f81680aa05401a00cc062030016009c04a022010007403801a00b004801e00d005002000e0060018008002000⟩⟩
theorem candidate04226_checked : Checked candidate04226 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7098039566336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04227 : Description := ⟨71, ⟨12, 0xf9aeb7da4d5ad42cf5cddc91c2ac11b7fb30acca82a399258da8c488f7e174a6ce6b469b68466c5ba56f5595244763df36334933031930125218a1711260f40b806005f05c05605404f04e04b04904803f03b03503402802702401e01c01301200f009007004003002001000⟩⟩
theorem candidate04227_checked : Checked candidate04227 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7150227259392 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04228 : Description := ⟨71, ⟨13, 0x8ab3eb5b48d586a133d59bac91615304562ea9b49f22a108a7fa3a61b38d6869d34119b0b7456f2ac94908ec42a1e48df06c634918089a043a2060dc868831417109283d016e0a6035817c0ac054027813809604902400f806a03301600a404e02500f007002601200780280120070018008002000⟩⟩
theorem candidate04228_checked : Checked candidate04228 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7150359379968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04229 : Description := ⟨66, ⟨13, 0x5305f5ed5569fb3d59bac1158ba95144493e492a43d1b288f3f09e54dce6b4334974c9b645d1f08d8c69231713488103da1bc0d006242e213f09184301e80b7047020c0d406102a013c09c04b02400f806a03301900a405002400f807002e01400900380120070028008002000⟩⟩
theorem candidate04229_checked : Checked candidate04229 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7156800765952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04230 : Description := ⟨71, ⟨13, 0x87c3561a7ecf566eb045598a8351d28892488d9454a2390267b03a49c00d6c69e34119a4b7456f2ac949098647622e8f7c79237c1b188d843a2060f687483441890b884f024a10c07a02a80d606a02a013c09c04b02400ec06603201800a8052026010007002601200780380140090038008002000⟩⟩
theorem candidate04230_checked : Checked candidate04230 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7157062926336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04231 : Description := ⟨69, ⟨13, 0x2ca54c48d14441aaad3f67ab375822acc541a8e944493d4099f84f2e6e735b19a4ba64db22e8e546c633318b88d843e2040f687483401890b884f824610c07a02a414608e04181cc0d4054027813809604801d80cc06402f01500a004c02400f807002e01400900380160090038008002000⟩⟩
theorem candidate04231_checked : Checked candidate04231 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7157065007104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04232 : Description := ⟨63, ⟨13, 0xb28d43282b3fe972467decaeb2710367dab4d42691b03959288f3ee1d28d926843361934c7062029f111469633318c8c0456a26a129075031413e093031c17409c048823010007302e01580a804801d809003c01c00d806802e011007802c012007002000c002000⟩⟩
theorem candidate04232_checked : Checked candidate04232 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7158246674448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04233 : Description := ⟨62, ⟨13, 0x55565ff29f8f63c69cd0e0a6ddb501852bc958b2110f2473437299a8b4857023b917c7c23c91cb0d945fe2e6135094840a1bb0d185c01e60db06402f413207d03d01bc0b605702b0114084037011807c03c01700a004c02000e0068028012008002000c002000⟩⟩
theorem candidate04233_checked : Checked candidate04233 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7185770283264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04234 : Description := ⟨68, ⟨13, 0x11ec78bb829b76d4067ab1e5824bc9598a8111507f83ca9d30e686e533516e89b24a724711dc8be42a1e48eb46ca2ff17309a04a42050dc868c2e00f306d832017a0a0037816c0ae0560278138092045021810807c03901b80b004a02300f807802600e0068028012008002000c002000⟩⟩
theorem candidate04234_checked : Checked candidate04234 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7185774510080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04235 : Description := ⟨61, ⟨13, 0x2aaf34f97ec7a9e34e6b70536e1a80c295e4ac590887f93f11f28e686d03351944a7448d2138f8479237a17f89a84a42030dd868c2dc0f106d832017a09204081f40ec05b02b815808a04201b80a004602200f807803a0170080038014009002000c002000⟩⟩
theorem candidate04235_checked : Checked candidate04235 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7185778086144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04236 : Description := ⟨61, ⟨13, 0x282f3ff9e5cbf23deffb7053699a76d2263cb09d47084439a1b88d0a64d31c1880b9c5b529d935c8583e11e48ddc5fa2b513509484001860770360190092046823010e08603781800ae05602a812408a032011807c03c01c00d806802e00a0048010006000⟩⟩
theorem candidate04236_checked : Checked candidate04236 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7186298177552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04237 : Description := ⟨70, ⟨13, 0x47b1e2edba69eb3d58f2c2a598aa6d508a5451c281d27c925487a36d1507fa372199cb744d92150f2475a3651a48c685d026812908743dc1b90d185c424810b079036417a0a003781a80c005b027813809204501f00e406e03501900b0052028012808c02600e0050024010007002000c004001⟩⟩
theorem candidate04237_checked : Checked candidate04237 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7186831081472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04238 : Description := ⟨59, ⟨13, 0x9e5cd3e6011ef8873fede34e0a6d3356da52cf563cb0a9632a38492a110e686d0342994cb9a5b429b934c6ea2f80ff060423a104075834812408d043821810207d03781a80c005b02b81580aa054027813809204501b80c805002300f807803a01c⟩⟩
theorem candidate04238_checked : Checked candidate04238 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7187371917313 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04239 : Description := ⟨73, ⟨13, 0x221cf1a7053699ab6d2967ab1e5854b1951c24950887343681a14ca65d32dd1690ae053d2478f847923961b28cc86342e8135094843e1ee0dd868c2e209204681f40de06a030016c0ae05602a815009e04e024811406e032014008c03e01e00e807002e014009804001c00a004802000e0040018008002000⟩⟩
theorem candidate04239_checked : Checked candidate04239 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7187371982848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04240 : Description := ⟨69, ⟨13, 0x2f8af1c71135019eac2b598aa054089d2447a11905c7df3ca9d30e686e534199a8ba657026d929c92047522f8f8475a3961bd8d945fe2e610f06f034017009f848c1e60db06382f40c805b02b013c09c048021810407c03901b80b004802300f807802e0140070034012008002800c002000⟩⟩
theorem candidate04240_checked : Checked candidate04240 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7190069460992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04241 : Description := ⟨70, ⟨13, 0x593e34ae206a033d5856b3258cac0d59e9d2491a18105c8113ef9e5ce947343729a0ccd45d32b8136c94e49023a917c6f636517f8b984d41d20d005c027c123079836c18e0a303981c00b6056027813809004302080ec070037017809804802300f807802e0140070034016009004000c002000⟩⟩
theorem candidate04241_checked : Checked candidate04241 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7190333702144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04242 : Description := ⟨66, ⟨13, 0x594682b3ff9e5cb8e4111a57fdbac5c40dd56df3699a76d2260728e911e82e3ee1d28d0864d31c1880b9c5b529111147202fd15a89a84a42000cf861827c126077036018e09c046823010e08603981c00c005602a8120076032012008c03c01c00d806802e00b0048010006000⟩⟩
theorem candidate04242_checked : Checked candidate04242 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7190458927120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04243 : Description := ⟨66, ⟨13, 0x4f2e5cf2088d2c441ff6f657823addc40dd56df3699ab4d2967ab045664acf51d249511e82e3f09d28dfe6e83681a10ca65cd2da14787b238e17c07f833418108203ac1a408d043821810007303801a80c005c02d81580aa054027813809003b01c00c8050024011807803a01c⟩⟩
theorem candidate04243_checked : Checked candidate04243 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7191532666881 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04244 : Description := ⟨80, ⟨13, 0x11a58883c11d6ee206eab6f9b4cd5a694b3d5822b32567a8e924a88f4171f84e946ff3741b40d086532e996e8b48570292136c9864761be8d9466631917409a84a421f0f705c427c12604681cc0e006a03001700b605602a815009e04e02400ec070032014009004601e00e807002e014009803c01c00b004802000e0040018008002000⟩⟩
theorem candidate04244_checked : Checked candidate04244 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7191532732416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04245 : Description := ⟨78, ⟨13, 0x51da216ffb7823addb7cda66ad34a59eab32567a7b924a8444171f84e946ff3741b40d366843299748a4c4d926191d87be3af1ca0df46ca33018c8ba056a25211c07b82e212605a023410c06a03001700b605602a815009e04e02280ec07003401900a004802300f007403801a00a804c01e00e004802000e0040018008002000⟩⟩
theorem candidate04245_checked : Checked candidate04245 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7200122634240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04246 : Description := ⟨79, ⟨13, 0xa0bcffe21cf1a70536e1ab6d2367ab0b1792b1951c27b53ac9be492a110ff27e23e51cd0da068531c1880ba25b829f92348583e11e48de866431a1728ad44d425210186ec34616e078824811a08c03e81a80b605702b015009e04e022810806e03201880a004602200f807803a01c00d806802e0100070028012007002000c002000⟩⟩
theorem candidate04246_checked : Checked candidate04246 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7203478048768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04247 : Description := ⟨68, ⟨13, 0x12fe97547c238115786d3d95cd6e0a6d13565852bc756723610f28453fc1d30e686cc34195bca424a424711e08bc4271e48ea86fc31817309a04a41ec0dc86282e00f306d832010007b03b01c40dc05c02b815809604201b00b004a02400f807802400f0068028012008002000c002000⟩⟩
theorem candidate04247_checked : Checked candidate04247 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7217986699520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04248 : Description := ⟨75, ⟨13, 0x8d1bec1e08e9e6eab6fdb4ad41694b375664acd541a36911e82e3e41bfcdd26cf335994cba652426d930c8ba4141f00df86c83331800ba04d425210f881c2e213e0868238106070035817c0b805b02b81540a804f0258120070033013809004601f00e807002e014009003c01c00b005002000e0040018008002000⟩⟩
theorem candidate04248_checked : Checked candidate04248 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7225825361920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04249 : Description := ⟨79, ⟨13, 0x94e3ec1e34f0474f36fdb4ad41694b37578cb3158d2a151b48444171f20f2a7183749b3ccd66532e9943898648f22e90a875a3961bf0d9066430017409a84a421f10386ec2e210d047020c0fa06b02f81700b605702a815009e04b02280f8072033013809004601f00e807002e014009004001e00e005002000e0040018008002000⟩⟩
theorem candidate04249_checked : Checked candidate04249 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7234146861056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04250 : Description := ⟨77, ⟨12, 0xf04e9edbfda5d41d29cddbc6b32acda6da379ee8da84482e7c86ff6e96cf69b66b6535d25bb58b56f5264d94c345d42c3af39437e3643303002e82b525223820717110d08e06b05f05c05b05705505404f04b04503803403302702402301f01d01c01a01501200f00e00a008007004003002001000⟩⟩
theorem candidate04250_checked : Checked candidate04250 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7234415263744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04251 : Description := ⟨76, ⟨13, 0x14189ff3829b3ed42691b375858bc756727b53ae9bd46d1fe4fc67c939a1ba4cd86383101744ada53f29314389b448d2160f847923611990c045ca2b513509483d41bb0c505b81e209104702300d605c02b81580a804f025810806c033018809c04802200f807803a01c00d806802e0100078028012007002000c002000⟩⟩
theorem candidate04251_checked : Checked candidate04251 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7235690303488 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04252 : Description := ⟨87, ⟨13, 0xa31d0627ff0f8856c251e08eb97503829b7eda6511275d37c82e3f19f28e686e936818e0c405bb2b814989b64c325492408f045f2160f847923af1cb0df86ca2b5135094847021f10387b811c08d046021c0d606a03481700b605a02b81580aa05402780cc064031012008c04401f00f007403801b00d005c02a014007803801a00a004802000e0040018008002000⟩⟩
theorem candidate04252_checked : Checked candidate04252 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7276492488704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04253 : Description := ⟨61, ⟨13, 0x2ca336797249562e0f657593881b3ec105682310f9274a3741944a7452128713688e84401b08cc44d425210187a837618a0b704f824c0f106d831c13809104082000ee07302e015808203b01b00a004e024011007803a017008003c016009002000c002000⟩⟩
theorem candidate04253_checked : Checked candidate04253 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7286575599872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04254 : Description := ⟨66, ⟨13, 0x5f166cf2e48f5455defcf1b711367d820b1655c27491b88453fe1f80f9274c3731944a7452128713688e84271f08f246f436118c07a834418a0b704fc24a0f106d831c17a09104082000ec06402e815808203701b00b004e025011007803a017008003c014009002800c002000⟩⟩
theorem candidate04254_checked : Checked candidate04254 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7286707720448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04255 : Description := ⟨70, ⟨13, 0x4b95c38be45d92c655a0ab84e926e511e8464171f7cf8c77f39a1b94d986833351750b7253e29191d48b84451ef0ebc72e37b1b10b9859c2670ea06f03401870b8048c2140f306d831c12c07b02c0138090043020810007603701b00b0048023010007c03c01b00a804401a00b0040014002000⟩⟩
theorem candidate04255_checked : Checked candidate04255 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7293417054208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04256 : Description := ⟨64, ⟨13, 0x17cbb05d04a7f90a57d93c55d30dee6de3695a44b14542a740f8669d34119acc9a63831016d49ae4441d48ddc62c2ce0f386e030c15709f849421a0ee06c02f41600a004d823010c07603881bc0c805f02a811407c033016009404601c00d806802e00c0050014006000⟩⟩
theorem candidate04256_checked : Checked candidate04256 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7301790435344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04257 : Description := ⟨84, ⟨13, 0x110d7cd3c69e08eb774f36f9b4ad716ad3505a52b3358c2a7946e925462211105c7e13e41c60dd06cf34d9a10cd66532dd15c4ab250e26191d88ba4431f00eb472e37d1b20c646002e8135094837617109f049821a07d03601800be05c02d81540a804e02280fc072034014009c04802300e807002e013009004001e00e005802000e0040018008002000⟩⟩
theorem candidate04257_checked : Checked candidate04257 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7302732120064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04258 : Description := ⟨80, ⟨13, 0x14159ff443dd64e206cfb5c5ab4d42691b04d5a0a394f8275137a9254621f24e946e834d9a10cd863831016e0a7e52628713688e84451b08c646022e515a89a84a42030f506ec31416e09f04981e209c04882300e606c02e01580a804e02080ec06c03401880a004e024011007803a01c00d806802e010007802c012007002000c002000⟩⟩
theorem candidate04258_checked : Checked candidate04258 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7304275562496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04259 : Description := ⟨89, ⟨13, 0x282f3ff8f7c43a1590947fdbc69d70ea07053699ab6b1951c275937c9254221f88f947343681a14c706202ea14fc95249123b917c8583e11e48ebc6ca33218d0ad44d425211c07b83761a3049023411808603e81bc0d4069030016c0b405702b01540a804e02280dc064031014008c04401f00f007403801b00d005c02a013008003801a00a004802000e0040018008002000⟩⟩
theorem candidate04259_checked : Checked candidate04259 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7340916998144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04260 : Description := ⟨84, ⟨13, 0x14129ffc3e2128f1c75b3a81c44dbc6d33561826b1951126f931693f49221190287e03e51d30e346e63681a08b744db261917c7c23c91b28b3046c22010307b83781a209f849416008d04601e40de06b03501a40c805b02d01580aa054027010406e03301900c406002c015008c04401e00e807002e013007803801a00a004802000e0050018008002000⟩⟩
theorem candidate04260_checked : Checked candidate04260 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7345201545216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04261 : Description := ⟨82, ⟨13, 0x53e682f3fe70536e1b3ed5b6a1348d85cbc75672ae13da9d64dea3691887f93f11f24e6868533618e0c4056d292936891a42c1f08f246f43611a58cc86343011728ad44d425210187a83a81bb0d186282dc0f1049024411808102b81580a804b024810806e03601880a004e02200f807803a01c00d806802e0110080028012007002000c002000⟩⟩
theorem candidate04261_checked : Checked candidate04261 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7428963831808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04262 : Description := ⟨82, ⟨13, 0x543282b3fe8cfbd95d64e206cfb569a84d2360aa7bd3a89bd46d231111e7c93a51bfcdd068433618e0c4056d29f11d088a3931b08d2c6663191808b9456a26a129080c3d41d40c505b827c12607882e813809104602000e605c02b015009604802080ec07003601880a004e024011007803a01c00d806802e011007802c012007002000c002000⟩⟩
theorem candidate04262_checked : Checked candidate04262 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7433124581376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04263 : Description := ⟨79, ⟨13, 0xa0bcff1d32db86adb505a46bc8581ab353de9d64dda3691887e237f9b3cd0a66b31c1880ada53e29293d49b645b22290b08283e01c98de869633318d0c005ca2b513509484061ea0ea068c2dc13e08683c4136092046016c0ae054025810007003701880a004e023011007c03a01c00d806802e011007002c014007002000c002000⟩⟩
theorem candidate04263_checked : Checked candidate04263 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7435204956160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04264 : Description := ⟨92, ⟨13, 0x1079830c059ecef1c7823a79cdadd76dfb695a82d294d1a62d28089142320b8f907973809ba4d9e66b32998e0c405d5293136c98645d2160e586fc3641800ba053a28412908e440e1d50de05c42b013f086829811c08303581a00ce064030817c0b805b02b81540a804b01980c005e02c014809c04802300f807403801b00d005c0280120078038014008003801800a0040018008002000⟩⟩
theorem candidate04264_checked : Checked candidate04264 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7518138925056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04265 : Description := ⟨70, ⟨13, 0x4a7dcd0e0a6dfb699922c796172f2550288d3b31cd0e366e936815c0a7a524287130c8f045f2150f847923961bf0d946302ff1730acc4d425210f881c3dc1a10c405bc2aa09903e81e80ae05602a812409004502100f805e02100f807803a01700a004001e00e0068028012008002000c004000⟩⟩
theorem candidate04265_checked : Checked candidate04265 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7525072437248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04266 : Description := ⟨90, ⟨13, 0x4695ecaf0475cba81c40e0a6eab6fdb4cd596a0349d59e88f4171f8cf9474a39a1bfcdd26d034199a8ca26383101754ae053e27a936c9864aa24811e08be445216105079237e1b28c605fe2e615a89a84a421f10387b83a813e06d82000e607002e016c0b405702b015409003b01c009004602200f807803a01b00d005c028011007803801a00b00500240100040018008002000⟩⟩
theorem candidate04266_checked : Checked candidate04266 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7533938868224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04267 : Description := ⟨85, ⟨13, 0x21f10ad84a3ec5c44e0a6ebb6fdb4cd5769f3495506a224eba6f934698b4a0236d11a7973a61cd0e026e93681a04cd064f2b814909b64c324811e08be3e11e48e586fc3651660acc53a25210387b83421880b784fc1b406b03501a40c806102b81580aa04801980c806203001780b005201f00f007402e014007803801a00a004802000e005002000c004000⟩⟩
theorem candidate04267_checked : Checked candidate04267 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7534178271232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04268 : Description := ⟨85, ⟨13, 0x21f10ad84a39b5c14dbf6d3355da7cd255e4a8e14449ed4eba6f934698b4a0236d0847f73cb9d30e687013749b40d0266832794989b24c324711e08be42c1e48df86ca2cb14209a04a423910e881c3dc1a10c405bc2b00da03581a80d206702b81580aa04502100cc06403101800bc05802900f807803a01a007803801a00a004802000e006002000c004000⟩⟩
theorem candidate04268_checked : Checked candidate04268 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7542768173056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04269 : Description := ⟨85, ⟨13, 0x28c74189ffc3e215b0946a934e5a40a224eba6f934698b4a0236d1228464171fecfc67ca3cb9d30e687013749b40c706202ea95c0a4c4db26192408f045f2160f847923961bf0d945942b1133086c33c1850b604842100ef06b023811a08c03581a80d203301900c406002f01600a4048023011007c03c01d00e006c03401700a003c01c00d0050024010007⟩⟩
theorem candidate04269_checked : Checked candidate04269 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7551357813248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04270 : Description := ⟨104, ⟨13, 0x1079830c059f62f6778e3c11da2eb975039b5c44e0a6ebb6fdb4cd596a0349d34698b4a0236d1228464171fecfc67ca3cb9d30e687013749b40d0666a32898e0c405d52b814989b64c324811e08be42c1f08f2472c37e1b28c605fe2e614e8a104a423910387b83aa1bc0ac04fc1b606803381900c205c02d81680ae05602a80c005e02c014809004602200f807803a01b00d005c02800f0070034014009004001800a0040018008002000⟩⟩
theorem candidate04270_checked : Checked candidate04270 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7551374589952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04271 : Description := ⟨72, ⟨13, 0x16baa6dc7c62aef7a7b23cd9e2ee9e74039a9be2dbc6d2b62d1b88a53e41eace967023731b3cd38559290936498647622e909c6c8318134081839e1b90d105c42a413c09284341b60a40500268100076037817c0bc05b02c815408a037016009c04a023010007402601200780380140080018008002000⟩⟩
theorem candidate04271_checked : Checked candidate04271 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7560302199040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04272 : Description := ⟨76, ⟨12, 0xf1ae9edbcda5c91c79b97b1ba9aa818a788e8608447c87ad79471b6e66cf6b557155953d52450e4c347645d44342a4143e039736433131826a2061d21bb1a217115513e12510d0db07d06f05f05b05504904804503f03e03702702602302101d01701301201000f00e00b00a008003002001000⟩⟩
theorem candidate04272_checked : Checked candidate04272 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7560306425856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04273 : Description := ⟨75, ⟨13, 0x8b6be69b7cda5648b1e5504a37462223d08882e3f09f20dd06cf35a1a6cd0866b32998e0c405bc2b89564a7652226b90ac7c03b01cb8df46c83481978ad44d42520cf86182ae13e09304341b00b803b81800be055024812008a03f01a80d0050027012008c03a01c00d806802e0130090030016008002000c004000⟩⟩
theorem candidate04273_checked : Checked candidate04273 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7560430094336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04274 : Description := ⟨75, ⟨13, 0x8f8c551f64f156de3695922c7958daa6d3aa8dc4541f20dcc6cf35a1a74d0466b32998e0c405bc2b89564a7652226b91107603641a40c5859c22010306e030c15709f849421a0d805b82800ec06f032017c0aa049024011407c03701a80cc058027012808c03a01c00d806802e0130090030014008002800c004000⟩⟩
theorem candidate04274_checked : Checked candidate04274 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7560562214912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04275 : Description := ⟨84, ⟨13, 0x11a6887be69ec4eb771036f9ae2d5a6a134a5922ad054e28e524e8c44539f84e946e835b1a6cd0866c32995c4ab253d29214389b44761cb8df46323011740acc4d42520e906ec31417109f049814609103981b80d806002f81700ac05502a012409003b01b00d005e028013809804801e00e807002e013009004001e00b004802000e0040018008002000⟩⟩
theorem candidate04275_checked : Checked candidate04275 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7563039014912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04276 : Description := ⟨89, ⟨13, 0x26cf1a68b9443df34f6575bb881b7cd716ad3509a52c915682a714728c44479f84e946e834d9a10cd865331c1880b785712ac94389b44762228e5c6fa34b18c8c045d02b513509483a81bb0c505c427c126048820410007303701b00c005f02e01580aa054024812007603601a00a004e02400f007403801b00d005c026012008804001e00b004802000e0040018008002000⟩⟩
theorem candidate04276_checked : Checked candidate04276 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7563047337984 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04277 : Description := ⟨70, ⟨13, 0x5aeaab94dca62cd3e3e31718ad3de1e28e656db36111b88c44529f20f246cf3589a74d0a66b32995c4ab253a22e909c6c83461990c686002e813308083d21b70c284841de0d6052028013209204802040fa07603781b408a03701600a004e025011807c03a01c00b804c0240100070028010007⟩⟩
theorem candidate04277_checked : Checked candidate04277 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7564846695168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04278 : Description := ⟨79, ⟨12, 0xfb2f9ae9eda5d73d5bd41d29c79b1ba9ba848dc8c48a87c87956cf6b469d68566b65357155953d45d42a36434933231a3002e829d2522201a317113f10d0a009207d06f06406005f05d05b05705505404904503e03703502c02802702502301f01d01c01701301201000e00a008007005004003002001000⟩⟩
theorem candidate04278_checked : Checked candidate04278 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7564855148544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04279 : Description := ⟨81, ⟨13, 0x221af9a78d3a79b4ad716adb505a52c7954e28dd24e8c4453a2410c08443e41e5cd9e6b634d9a14cd66532b89564a7a45d20a0f8072e36418d0c005d02b313509483a41bb0d185c427c10d04901f40de06c030017c0b605702a815009204501b80d005e028013809804601f00e807002e013009004001c00b005002000e0040018008002000⟩⟩
theorem candidate04279_checked : Checked candidate04279 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7565119389696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04280 : Description := ⟨86, ⟨13, 0x4d3e2e510d7cd3c69d3cda56b8b56da82d2963caa7146e8c44221f20d9e69b34299acca663831016f0ae255929293d48ba44521610507c03971b20d2c6343001740ad44d42520ea06ec34617109f043412408103e81bc0d806002f816c0ae05502a012408a03701a00a004e02300f807403801b00d005c026012008804001c00b005002000e0040018008002000⟩⟩
theorem candidate04280_checked : Checked candidate04280 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7565127712768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04281 : Description := ⟨87, ⟨13, 0x8884241d70e9d72ab87db7ad746adb4fda50a3a4dd1f88f8e77f3a49b9cd3c6853349948c706202de15c4ab253e29293d49b64aa23b91148584141e48df06c634b1998c685ce2ce15a8a744d22200f687503781a30c484301e807803981a80c005a02c015c0a804001d80c8050022010007c03801b00d005c026012008803801a00b005002400e0050020008002000⟩⟩
theorem candidate04281_checked : Checked candidate04281 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7572607205376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04282 : Description := ⟨81, ⟨13, 0x29bf4788f8c56e156f1774f3a01cd4df16de3695b1ad6e6ac3505a52a6d51ba7551b87c83d59d2ce046e63679a08cd66532ac936498647622e909c6c83301800ba04d02060dc86882e215209e049421a0a004d023c0ec06f035817c0b605902a815008a03701a00cc058027012808c04001d00e004c02400f00700280100070018008002000⟩⟩
theorem candidate04282_checked : Checked candidate04282 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7577465291008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04283 : Description := ⟨83, ⟨13, 0xa3c42ade2ee9e6de3695adcd586a0b4a54daa374eaa62d1b88aa3e41ec0e967023731b3cd0466b32996f0ab252626c930c8ec45d2160d906603001740b2c56828413408e440c1d50dc86882e215809e049421a0a004781bc0d605f02d81540a804501b80d0066030016009c04a023010007403801a009804801e00e005002000e0060018008002000⟩⟩
theorem candidate04283_checked : Checked candidate04283 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7578002161664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04284 : Description := ⟨81, ⟨13, 0x2ed53f9853bacdd3adb96d1b555a7ebb255c28893469274489f1cf2e6cd3349880ae24db23a8f846f631715909a447222010207b43aa1bc0d006242b013f09184301600af04e024811c08c03c01b80d406903401680aa054020810006e03601980c806203001780a004802200f807403801b00b804801c00d004802000e0060028008002000⟩⟩
theorem candidate04284_checked : Checked candidate04284 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7585718616064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04285 : Description := ⟨64, ⟨13, 0x15c0975bff5ec6eb474039b1c78e1d6f8b6f9b4ca364211f78f567023741b40a424d9261917c7be37d1b28bfc5cc2b013409483dc1a10c405bc2a413c093026812c08003c819c0c005902b015408a04101d80b005002000f007402600f0070034012008002000c004000⟩⟩
theorem candidate04285_checked : Checked candidate04285 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7593653469440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04286 : Description := ⟨73, ⟨13, 0x2218eb471036f9b4cc9163cb0556fea9a51b249d11a7de3d69e58ecc74a38d9ba0da053d292143898649122f910c72e37d1b28cc45fe2e615989a84a41ee0d086202de15509f04980fa07903981800ac055024812008a04101f80ec05e028010807803a017009804001e00e006802c012008002000c004000⟩⟩
theorem candidate04286_checked : Checked candidate04286 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7593657696256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04287 : Description := ⟨72, ⟨13, 0x1255758b881b7cda6648b1e582ab7f54d28d911e8444171f28e946e836819a8ca263831016f0a7652226b91cc8563fb1d80e5c6fa36515a89a84a41ee0cf86182da15709f049813807703981800ac055024812008a04101f80ec050024011808803c01d00d806802e013006002c012008002000c004000⟩⟩
theorem candidate04287_checked : Checked candidate04287 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7593665759232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04288 : Description := ⟨63, ⟨13, 0xb5d47c60f30617febde5e2ae696dd28e13ac9be4529ff0fc47ca372199cc9c4d72138f8479236517e8b905922b014e89484401ee0dc06182da12408583c81480a003b01bc0d0067032018008a03701900c4058028012808c04401700980280120080028010006002⟩⟩
theorem candidate04288_checked : Checked candidate04288 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598065715456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04289 : Description := ⟨73, ⟨13, 0x23e2f156dd31e5636a9b5422951470a094eb26f91507fc3f11f28dc866732718e0c405bc29d935c8883fb1f08f247603651a40bf45c82ce15a8a744a42200f706e030c16d092042c1e40a003b01bc0c8060024811407c03701a80c806202c014009404602200d806802e01300600280120080028010006002⟩⟩
theorem candidate04289_checked : Checked candidate04289 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598074103808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04290 : Description := ⟨61, ⟨13, 0x2d7555c9a7c7c5ef0f14732b6d914a7fc3f11f28f2474c39a1b40cd465129d12448ee45f2138f8479236517f8b984cc2020db86142d812108403bc1480a004c824810207d03b01bc08a03701600a004a023011007c03c01d00b804c02000e0068028012008⟩⟩
theorem candidate04290_checked : Checked candidate04290 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598082360064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04291 : Description := ⟨74, ⟨12, 0xed2eb8ea0e22e0ada6d40d27c79b1b8a87fc7e27ca79574c7346d066a65153d49147745f42a3e13c93652ff2e629d2522201ee1a313f0db0a009207d06f06406005d05b05a05705605504904503e03702c02802502302201f01e01d01701301000e00d00a009008005004003002001000⟩⟩
theorem candidate04291_checked : Checked candidate04291 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598090813440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04292 : Description := ⟨80, ⟨13, 0x110c78d3ae1d40e207053699a80d2763ca8d924e8a744821810888153f11f28f2e74a39a1b40cd465129e92448ee45f20a0f2472e3651988bfc5cc2b313509483dc1d20dd868c27c0db04901f40e606f030016c0b405702b015409204501d80dc05e028013008c04401f00f007402e013008003801a00b00500240100040018008002000⟩⟩
theorem candidate04292_checked : Checked candidate04292 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598355054592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04293 : Description := ⟨84, ⟨13, 0x134f8863c69d70ea07103829b4cd40693b1e546c8443f11f28e9473436819a8ca263831016f0a4a4f525512448ee45f22290b08283c91cb8d946622ff1730ad44d42520f707503761a309f036c12408103e81cc0de06002d81680ae05602a812408a03b01b80a004602200f807803a01b00d005c026011008003801a00b00500240100040018008002000⟩⟩
theorem candidate04293_checked : Checked candidate04293 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598363377664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04294 : Description := ⟨66, ⟨13, 0x5aea8f34179ffcd3e21d0ac84a3de1e28db669cb48134698b493a28d07e7973a61cd0da066532618e0c405bc29c13508583e11e48d945f42e11650ac44cc20209084201de0a4050024811a08c04081f40de06a03480dc06002f01600a003e01e00e806c0340170098028012008⟩⟩
theorem candidate04294_checked : Checked candidate04294 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598602453512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04295 : Description := ⟨79, ⟨13, 0x88742b2128f187113829b4cd3e692b1e54709d64df268d3169274532108f2e74c39a1b40cd064f29e92448ee45f1f08f246ca33218d0b3056629d12908803dc1ba0c405bc27e0da04901f40de06a03481900c005702b015409204501b80c806203001780b005001f00f007402e013008003801a00a004802000e005002000c004000⟩⟩
theorem candidate04295_checked : Checked candidate04295 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7598602780672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04296 : Description := ⟨87, ⟨13, 0xa0bcffe15909478e3ae1d40e227053699ab69d64df2118fc47ca3a61cd0da068531c1880b7853e29293d49b64aa23b917c8583e11e48d9469631a1670ad453a25211007b83a81bc0d184fc12408d04601bc0d406903201800b605a02b81580aa05401b80c806202c014008c04401f00f007403801b00d005c0260110070034014009004001c00a0040018008002000⟩⟩
theorem candidate04296_checked : Checked candidate04296 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7607200776192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04297 : Description := ⟨82, ⟨13, 0x443a15509478c3ad1c44dbe6d334f9a4aa384ea26f934698b493a108fbc7af3cb1d98e9871b3741b40cd064f287130c92245f1f08df46ca33218c8b3056629d12908803dc1ba0d086202de15509f84981b407d03c81a80d206403001580aa04502080c806203001780b005002100f007402e013008003c01c00d004802000e005002000c004000⟩⟩
theorem candidate04297_checked : Checked candidate04297 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7611085029376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04298 : Description := ⟨82, ⟨13, 0x51de150f1775b3a81c3adbc6d33501a4ea364e9262d1547fc3f01f28f607023731b40d3866a32896f0a4c4d9261917c8583df1e48d946302ff1730b2c56828413408e440c1ee0ea86e434415809e04941b60a004b01e40de05b02d01580aa04502080ec06e0300160094046022010007803a01a009803c01c00d00500240100060018008002000⟩⟩
theorem candidate04298_checked : Checked candidate04298 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7611237826560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04299 : Description := ⟨85, ⟨13, 0x22190a878d3ad9d40e206de3699a80d2751b27490887e03e51d28dcc6d03351944c706202de14fca4c50e26192448be44521610507923971b28cc46302ff1730b3456828413508e440c1ee0ea86ec34415809f04941b607d03c81cc0de05b02d01580aa04502080ec06e023011007803a01b00d005c026010007803801a00b00500240100060018008002000⟩⟩
theorem candidate04299_checked : Checked candidate04299 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 7611241988096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate04299_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch042

module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch040
open Papers.RationalityTen GraphCandidateCoverage

def candidate04000 : Description := ⟨65, ⟨13, 0x291b12484a41d5fc6e366ebb699a7cd2552726f933e90d3b01c04da06683279688a1a4c324811e08be3961b28c644d625210387b83421880b784fc24c0da05a82b812e06a03481980c205602a80c806202e014807803a01900a003c01c00d004802000e005002000c004000⟩⟩
theorem candidate04000_checked : Checked candidate04000 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2036217479424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04001 : Description := ⟨73, ⟨13, 0x23aef307503755b4cd40693b23d8beb96580a23902a7ca3b29bfcda066a32898dcb4452428693c898649023c117c7c43c91bf0d946302ff1730a0443e1ee0e9068827c12506d82840ea07002d81680ac055029812008c03d01c00b404c023011007803a01900a003c01c00d00580280120080018008002000⟩⟩
theorem candidate04001_checked : Checked candidate04001 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2036374503424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04002 : Description := ⟨69, ⟨13, 0x266b12784a41d208ef63798b8edba4da669f34953de9be4cfa434efa74d36819a0c9e521277930c8f045f1ca0d946322b014d09f84a421d10387b83421880b784f024c0da057024c10007e03501a40ce06502b015407003201880b805202000f007401e00e0068024010007002000c004000⟩⟩
theorem candidate04002_checked : Checked candidate04002 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2036485882112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04003 : Description := ⟨73, ⟨13, 0x27fedd56d334eda44c8f62fa9453de9be447a17505c7e33e51bfcda068430f9818baa5a229113c088a4121fd0f886ca2fd1720ad4538283129087c40e1ee0cf86182da13e093036011a08c04581c00ac055029812008c03801900c4048023011007803a01c00d806803201800a002c012008002000c004000⟩⟩
theorem candidate04003_checked : Checked candidate04003 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2036498171904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04004 : Description := ⟨79, ⟨13, 0x9ffc251fc6ed17503951c14dd76dfb699ab6a514df268921a85d3fd9f28efc7343809ba4da068531b96889e449022f904c7923961bf0d9463426b129081c3dc1bc0d184fc11a08c03501a40cc06102d81680ae05602a81500a604601900c405c029011808803e01e00e80700320140070034014009004001c00a0040018008002000⟩⟩
theorem candidate04004_checked : Checked candidate04004 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2040923226112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04005 : Description := ⟨79, ⟨13, 0x9ffc30e128ecf7503829b7eda66ada7b537c9a14b8a17cff27ca3cb9d94e686e93681a14c6e5a228613708be4131e48e586fc3651990c6856629c140894843e2070f706ec34608d04601e80d406902d81680ae05602a81500a604201900c405e02d011808803e01e00e8070032014008003801a00a004802000e0040018008002000⟩⟩
theorem candidate04005_checked : Checked candidate04005 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2049508966400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04006 : Description := ⟨82, ⟨13, 0x4ffe187094767ba81c14dbf6d3356d3da9be3fc9f28e686e93681a14c3e6062ea9688a7e50c27a13708be42c2098fe87923961bf0d9466431a15a8a7050625210f881c3dc1bb0d1823411808b03d01a80d205b02d015c0ac05502a014c084032018808c04401f00f007403801b00d0064030014008003801a00a004802000e0040018008002000⟩⟩
theorem candidate04006_checked : Checked candidate04006 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2049517289472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04007 : Description := ⟨78, ⟨13, 0x42520eafe3768ba81a7ad245caad954a69be4c525c528090d42f9fecf947933b0999cc9c6372d112408be42a2098fe07923961bf0d946342cc1598a044d625210387b83781a3092042c1e40d905701a80d2066030816c0b405301f00f006403101800bc05c02d014808c04401900a003801a00a004802000e005002000c004001⟩⟩
theorem candidate04007_checked : Checked candidate04007 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2057557966848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04008 : Description := ⟨84, ⟨13, 0x13ff84a3f8dda2ea072a3829baedbf6d3356d72ab65529a6f934490d3fd9f28f2a77e3b19cd0e026e93681a14c6e5a2248117c8544131fc0f2472c37e1b28c684d625210387b83781a309f823411806a03481980c205b02d015c0ac05502a014c07c03c01900c405c029011808803e01e00e80700320140070034014009004001c00a0040018008002000⟩⟩
theorem candidate04008_checked : Checked candidate04008 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2057566224384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04009 : Description := ⟨83, ⟨13, 0x935c8ee25309483c3f8dda2ea069eb49172ab65529a6f934490d3fd9f28cce64e30f9818baa5a227a12408be4442098f247603961bf0d9469831a1670ad450626b129081c3dc1bc0d184902160f206c822c0ec07403501a40cc06102d81680a603e01e00c806202e014808c04401b00d0064030014007003401800a004802000e005002000c004001⟩⟩
theorem candidate04009_checked : Checked candidate04009 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2057566289920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04010 : Description := ⟨77, ⟨13, 0x27ff09483934e5a409be4c525c528090d42f9fecf947973bf1d94e687013749b40d0a61f3031754b444f4248117c8584131fd0f2472c37e1b28c685942b114c09fc4361850b604842100ef06b02b811a08c04581a80d205301900c406002f01700b4052023011007c03c01d00e006c03401900c005001c00d0050024010007⟩⟩
theorem candidate04010_checked : Checked candidate04010 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2058094641664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04011 : Description := ⟨88, ⟨13, 0x13ff84a41e1fc6ed17503951c14dd76dfb699ab69be4d12434ff67ca3bf1cd0e026e93681a14c3e6062ea96889e849022f90b08263fa1e48e586fc36518d0b3856a283135894840e1ee0de068c27e08d046022c0d406903301840b605a02b81580aa05402980c806202e014808c04401f00f007403801b00d00640300140070034014009004001c00a0040018008002000⟩⟩
theorem candidate04011_checked : Checked candidate04011 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2058103029760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04012 : Description := ⟨66, ⟨13, 0x449e129074823bff5e62e3b6df3699a7cd2551da7c137c99f4871df4e9a7023741b40d3466832793bc8ee45f1be8d946602b014d09f84a41ee0c405bc27812606d02b80fc06a034819c0ca06002b015406803201880b805002000f007402600e0068024010007002000c004000⟩⟩
theorem candidate04012_checked : Checked candidate04012 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2100910391552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04013 : Description := ⟨79, ⟨13, 0x9ffc44618d09475c3a81b7cda66b8a8ed3e09be4d0a5c524e85f3f11f28eca6e83681a6cc6e5a3286137092247722f90487c43971be8d9456629c14089483dc1bb0d184f824c08d04601b00d4069030016c0b405602a81500a603401900c405e02d014008c04401e00e8070032013008003801a00b004802000e0040018008002000⟩⟩
theorem candidate04013_checked : Checked candidate04013 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2118094225408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04014 : Description := ⟨62, ⟨13, 0x5b36a553637b13d31d72e9f71b349d91a88c43b1f8cf9276032892448f045e2090f8872e3311730a704a42070dd862827c12606d833014609704881fc0dc05f02e01680ac05502380d804e024011007803a019009004001e00d00580240100040018008002000⟩⟩
theorem candidate04014_checked : Checked candidate04014 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2132606517504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04015 : Description := ⟨69, ⟨13, 0x26c6f4c75cba7da4eb945bf2ba553488f43b1f8cf9276332898dca7a52424891e08bc4432090fe07c43971988b9853825210386ec31413e093036c19809103f81b80be05c02d01580aa053024812008e03f01e00d804e024011007803a019009004001e00d00580240100040018008002000⟩⟩
theorem candidate04015_checked : Checked candidate04015 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2132614905856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04016 : Description := ⟨60, ⟨13, 0x16cba954d8e1270757a538d9a4ac8d4dea67d0e876032792448f045e1990c6460226b129088040e1ba0d085bc27e12606d033015c09704881fc0dc069033017c0ac05502380d806202e013807803a019009004001e00d004802000e005002000c004000⟩⟩
theorem candidate04016_checked : Checked candidate04016 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2132854243584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04017 : Description := ⟨67, ⟨13, 0xb664d89f96f7a7b23cd1dd6e9f71db49d91aa68452a1d4ff87c93bd9d34e0469c3289484a1647822f104479237e18c0b984fc1cf0dc868831413c092836c1980a404882000dc06502f81780b405602a811c07a036013809404402000f007402400f00680280120080018008002000⟩⟩
theorem candidate04017_checked : Checked candidate04017 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2133007040768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04018 : Description := ⟨68, ⟨13, 0x136389f3a7da4eb9653423d514e88e42f2054f9276532898dca7a52424891e08bc3e21e48e5c6fc33118c0b985021d20dd868831413e092836c19809103f81d40dc05f02d01580aa053024812008e03d01b00b404e026011007803a019009004001e00d00580280120080018008002000⟩⟩
theorem candidate04018_checked : Checked candidate04018 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2133011267584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04019 : Description := ⟨66, ⟨13, 0x5b2e6c509383a411df96f6371db49591aa694f826f533e8743be9d34e0469a3279484a1647822f0cc06323011580a684fc25210386842de13c09303681980ae04882000dc06903381940be05602a811c06c03401880b804e02000f007402400f0068024010007002000c004000⟩⟩
theorem candidate04019_checked : Checked candidate04019 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2133122646272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04020 : Description := ⟨69, ⟨13, 0x27fd3606912a714d29f04dea23d0ec7e33e49a6cd0866c30f9818b1453b291142488a4121fd0f8872e32f1720ad4538283129081c33e16d09f04981b00cc048823011606e02f81580aa053024812008e03601a00c404e024011007803a01c00d8068032018009002c012008002000c004000⟩⟩
theorem candidate04020_checked : Checked candidate04020 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2133134936064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04021 : Description := ⟨73, ⟨13, 0x27f926a74c3695a44c905ca2a794d29f04dda1d905c7e33679a6cd0866b30f9818b1450922d10ac8243f91d80e5c6c832f1720ad4538283129081c33e1860b6855c27c126086836013608c04581dc0be055029811c08003f01a00c404e024011808803a01c00d80680320180090030016008002000c004000⟩⟩
theorem candidate04021_checked : Checked candidate04021 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2147697559552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04022 : Description := ⟨73, ⟨13, 0x27f31bf84641e1e8eda369132415d2a534d11ff0fc67c73669a74d0866930f9818b1450922d11108563b017e8b9059c2b5110081c3da1b80cf85b42ae13f09304301b00af051023011607403701980aa053023810007803601900c405c025012008803a01c00d806803201800900300120080028010004000⟩⟩
theorem candidate04022_checked : Checked candidate04022 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2147895740416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04023 : Description := ⟨81, ⟨13, 0x27fd13f863424de98eb974fb5c5ab4d4264829a53e09bd4d0a5c51ea89143b1f8cf9276534d9a10cd863724891e08bc4121f10e5c6323011598a7050225210386ec31413e093024411807f03701b00d205f02e01680ac05502a014c08e03601a00c405e02d013809004401e00e8070032012008003c01a00b004802000e0040018008002000⟩⟩
theorem candidate04023_checked : Checked candidate04023 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2150306480128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04024 : Description := ⟨85, ⟨13, 0x27fd36689fc31a126f4c75cba7dae2d5a6a132414d29f04dea1d8fc67c934d9a10cd861f3031628a7e52624891e08bc4452090fe87c439718c8c0456a29c141894840e1bb0c504f824c091046022c0fe06e03601a40be05c02d01580aa054029811c06c034018809c04802200f007403801b00d0064030012008003c01a00b004802000e0040018008002000⟩⟩
theorem candidate04024_checked : Checked candidate04024 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2150314803200 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04025 : Description := ⟨65, ⟨13, 0x21b908e7743a69b40d3c5a52b41474957461a0b4e9473331a17a894845c2090f7872e3621998bf853824e10387ac34618709f04982140af04d824411a08c04581ec0d205a02a81500a004001d80d8064031015809c04602200f0074038019006802c0100070020008002000⟩⟩
theorem candidate04025_checked : Checked candidate04025 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2418750267648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04026 : Description := ⟨61, ⟨13, 0x2f05476885431a11ce9a6d035c5a78a35461a0b4e666332dd92a48b83af1b10cb45fc2b512708e040e1eb0d1861c24c10a05a02bc136091046823011606c03481680aa05402000d8064031015809c04602200f007403801a00a80340100070020008002000⟩⟩
theorem candidate04026_checked : Checked candidate04026 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2427340202112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04027 : Description := ⟨71, ⟨13, 0xa22436605ae096d33509a1ac8e616aa6d2ae8123999c60da06b433618dca7a50c26d129c9223e11e40eb46ca3491990c0453826a10387b83761a30c5049816408c04401a40c605a02b01540a8053028012408603901a80c405602200f007403801900b805802000d004802000e0040018008002000⟩⟩
theorem candidate04027_checked : Checked candidate04027 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2446399176704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04028 : Description := ⟨68, ⟨13, 0x144486cb889c12da66a134353448123a61ccce306d035a19b0c6e4a71f08f2075a3651a48c044402070f706f034618a09f84981640ab04602200d2066032018c0b405602a81500a605002180e406a03101700b005602200f007403801900b805801a009004001c00a0040018008002000⟩⟩
theorem candidate04028_checked : Checked candidate04028 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2454984916992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04029 : Description := ⟨76, ⟨13, 0x144791040b5dcae20704b699a84d0d5a528193429724aba49912074a3999c68da06b633618dc94e4121e40e5c6ca3331808acc53826a11b081c3dc1d20d1862827c12604f0230110073034818c0b405602a81500a605002180ec06202f01580a804c02200f007403801900b805801a00b004802000e0040018008002000⟩⟩
theorem candidate04029_checked : Checked candidate04029 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2455249158144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04030 : Description := ⟨81, ⟨13, 0x27c722086e40b5dd0e20704b699a84d0d5a528192ae8123a51cccda066c310181cba85bb29f149488a4121e40ebc72e3651a58ccc6022b514e09a84702070f7075034618a09f049811808b04401ec0e606903181680ac05502a014c0a004301d80c405602200f007403801b00d006402e01600a804401a00b004802000e0040018008002000⟩⟩
theorem candidate04030_checked : Checked candidate04030 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2455257481216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04031 : Description := ⟨66, ⟨13, 0x5126632deb6d33509a1ac90621a8210287663681adccd863726d13049224781f08f2075a3651990c6460226a12888d83dc1bb0d106282aa09404602200fe06902d01580aa054029814008e03901880a804402100f007403801900b805802000f00680240100070018008002000⟩⟩
theorem candidate04031_checked : Checked candidate04031 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2459277787136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04032 : Description := ⟨67, ⟨13, 0x9ffc251d40da6686b3d194ea54504a6f92ac90b46da118ff67ca3a61c04da06b42f61684aae4c223b917c79037d1b28d244d025110e88183dc08d04601a80d205b02d01580aa054029814009a03501900c4058029011808803c01d00e005802600e00680240100070018008002000⟩⟩
theorem candidate04032_checked : Checked candidate04032 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2521559040000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04033 : Description := ⟨68, ⟨13, 0x144a6d3361da84d0d647aa0941288e40a9d98e366d033618dcb44570292143498249023c0f847903961b28d24632301135094443e1ee0e90688314155048023011006902d01580aa0540298140090035018809804402100f007403801900b805802800f00680240100070018008002000⟩⟩
theorem candidate04033_checked : Checked candidate04033 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2588126806016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04034 : Description := ⟨72, ⟨13, 0x144a74fb695b0ed0d6472e55536a84504a29d02a7c93ca1c6cd9e6372b89560a7a50c26d12448bc42a2098f1c6fc3641a48cc863426a128874837618a0aa849421a09004602200d205f02d01540a8053028012407c035018809c04c022010807403801900b805802401000680280100070018008002000⟩⟩
theorem candidate04034_checked : Checked candidate04034 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2686843944960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04035 : Description := ⟨58, ⟨13, 0x52568913c76f5b699b0ed296789c54da06b132997b4ae050d26d930c8ec3e11cb0df46ca31917409a843e2060f706882e20d004a024011a085035016c0ac05502a013406402300f007403801900b805002600f00700240100070018008002000⟩⟩
theorem candidate04035_checked : Checked candidate04035 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2793211494656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04036 : Description := ⟨57, ⟨13, 0x28893ff9e244aa1b0d8a691b3c54069be4861f88f946e836818d0bda59f26d8f8468c2e514e09a84a42030d185b824c0f106802c811a08c04581b40d405b02b015009a03201880a004602200f007403801900b8038012007002000c002000⟩⟩
theorem candidate04036_checked : Checked candidate04036 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2796438950144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04037 : Description := ⟨64, ⟨13, 0x14449ff4d962b10d87b2b67db14d5a6a1348d59ca034dea368fc67c934219b0c685ed2b69484a1a3e11b08d186323011728a704d42520f506282dc12607882c812208c04582000da05c02b0150096036018809c04802200f007403801900b803c012007002000c002000⟩⟩
theorem candidate04037_checked : Checked candidate04037 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2828651204864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04038 : Description := ⟨74, ⟨13, 0x4ffe128ea070536fdb4cd5b67930ad40c9be4091f28e686e93681a14c6e5ed2e99688ae04db25392408be4131f08f2472c37e1b28c6853826a129087c40e1ee0d1823411806a034816c0b405702b01540a8053027810c064031011808803e01e00e807003201700a003801a00a004802000e0040018008002000⟩⟩
theorem candidate04038_checked : Checked candidate04038 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2865561141248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04039 : Description := ⟨73, ⟨13, 0x27ff0947503829b7eda66adb3c9858bc951c27b537c8443fc9f28e686e93681a14c6c5d22dd936495248e22f90b07923af1bf0d946342b512908e040e1ee0d1823411806a034816c0b405702b01540a80530278114084032018808c04401f00f007403801a00a803801a00a004802000e0040018008002000⟩⟩
theorem candidate04039_checked : Checked candidate04039 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2874151043072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04040 : Description := ⟨67, ⟨13, 0xbe3d1127fd36597245621b0e226cfb629a84d23608280d3a89bd46e1f80f9274c33618d0bda52128691d07c23611a30c646022e514d87a83781a20c505b827e0f106382c812208c04582000da06402b015008203601880b004e02200f007403801900b803c012007002800c002000⟩⟩
theorem candidate04040_checked : Checked candidate04040 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2897368584448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04041 : Description := ⟨76, ⟨13, 0x13ff8884251d70ea071036f9b4ccf360928e940c9be492a048fc47ca3a51ba0da06372f696e8b464db25391dc8be4121cb8df46ca33314e09a84a41ee0d184f824c08d04601cc0d4069030016c0b405602a81500a604e02180ec064031014008c04401e00e8070032017009803801a00b004802000e0040018008002000⟩⟩
theorem candidate04041_checked : Checked candidate04041 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2934146400256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04042 : Description := ⟨73, ⟨13, 0x28ed3ff885c251ff6eb875036f9b4ccf34f826f924a8443f11f28e946e83681a6cc6c4d925491dc8be3df1d78df46ca33015a89484701ee0d1849816808d04602180d4069030016c0b405602a81500a604e02280ec06803201880a004602200f007403801a00a804c01c00d004802000e0040018008002000⟩⟩
theorem candidate04042_checked : Checked candidate04042 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2942736302080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04043 : Description := ⟨71, ⟨13, 0x9fe4245ca4dbf6d2b56da82be45cb28193768123be1ba4d9e68533598dcbda57126d929c7c03971bf0d9066631a1800a704d4252103868c27c10d04d82300f0075034817c0b605a02b81540a8053021810007a031013808c04401f00e8070032017009003801a00b005002000e0040018008002000⟩⟩
theorem candidate04043_checked : Checked candidate04043 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2968439029760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04044 : Description := ⟨72, ⟨13, 0x13fe849bae5d3ed5a6a132415a0a6951ca7c137a8763f19f24e9469b34219b0c6c5bb2c59498a164a923c11787be3af1980c646022b512908e040e18a093024411806e034817c0b805a02b01540a805302380ec06c034018809c04802200f007403801a00a804801e00d004802000e0040018008002000⟩⟩
theorem candidate04044_checked : Checked candidate04044 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 2974948556800 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04045 : Description := ⟨67, ⟨13, 0xa254ffa6cb1587b238f1b3ed42691b2a97f4ace4ea26f51b47e03e49ac4cd86342f6967cada52128691d07c23611a30c646022e513507a839e1a20c505b82a40f1048824011808b04001b40bc05902b015009a04b02080d8062027011007803a01c00c805c01e009003800c002000⟩⟩
theorem candidate04045_checked : Checked candidate04045 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3034803343616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04046 : Description := ⟨77, ⟨13, 0x29811567d83a79b4ad876ac3505a52c8f5caa36911c8603e41e50e366cf34119acca66372f69688a4850d26d930c8ba42a2098e586fc3641a48c005d026a10f87483441710aa849421a0b7048020c0d605f02d81540a8053025812007c035019809c04c023010807403801900b805002400f00700280100070018008002000⟩⟩
theorem candidate04046_checked : Checked candidate04046 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3102382030848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04047 : Description := ⟨70, ⟨13, 0x50627f329e8d241ce02cfaf768ba75baeda36aab4fd4449d74cf2244fc67c73cb9ba4d9a6692b60c5c5902b211c88683da1d50d006242b012308602bc15c08e046020c0f006e03501a40d006102d01540a804001b00cc064031017809004401f00e807002400e00680240100070030008002000⟩⟩
theorem candidate04047_checked : Checked candidate04047 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3118952628352 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04048 : Description := ⟨76, ⟨13, 0x13ff84a3a81c14dbf6d3356d37c9a1448218102a7ca3cb9cd0dd26d035b1a14c6e5ed2d115c09b649022f904c7c23c91cb0df86ca31a1598a704d425210f881c3dc1d20d1823411806a034816c0b405702b01540a805301900c405e026011808803e01e00e807003201700a003801a00a004802000e0040018008002000⟩⟩
theorem candidate04048_checked : Checked candidate04048 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3140430659584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04049 : Description := ⟨79, ⟨13, 0x9ffc251d40e0a6dfb699ab69be3e51cd0dd26d03429880bda5d52d115c0a7c52527a936c95449022f90b08263e11e48e586fc3651a58c6856a29c135094843e2070f7075034608d046022c0d406902d81680ae05602a81500a6032018808c04401f00f007403801b00d006402e014008803801a00a004802000e0040018008002000⟩⟩
theorem candidate04049_checked : Checked candidate04049 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3140438982656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04050 : Description := ⟨73, ⟨13, 0x27ff09475039b5c14dbf6d3356d792a384f6a6f93428443fc9f28f2e7343749b40d0a63626c92388be42c1e48df86ca31a14209484722070f7075434615804682300d4069033816c0b405702b01540a80530228108064031017808c04401f00f007403801a0070034014009004001c00c0040018008002000⟩⟩
theorem candidate04050_checked : Checked candidate04050 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3149020561408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04051 : Description := ⟨75, ⟨13, 0x9ffc3e215b0947503699ab0a224eba6f934098b4a0236d08c7fb3e51d30e026d034118d8a4c4c323c117c8583c91bf0d945962b414209a047221d0f70754344158092823411806b03501a40b605a02b01540a805301980c806203001600a404602200f007403801a007803801a00a004802000e0060018008002000⟩⟩
theorem candidate04051_checked : Checked candidate04051 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3153313431552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04052 : Description := ⟨79, ⟨13, 0x9ffc251d40e6870536fdb4cd5b5caa6f93427ca3b31cd0e366e93681adcd0a6372f69688ae04db248117c8544131f08f2472c37e1b28c6856629c135094843e2070f7068c2aa09904682300d406902d81680ae05602a81500a603e01900c405e023011008403e01e00e807003201700a003801a00a004802000e0040018008002000⟩⟩
theorem candidate04052_checked : Checked candidate04052 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3157073657856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04053 : Description := ⟨83, ⟨13, 0x9ffc2520eeea0736b829b7eda66ada6f93427ca3cb9cd0dd26d03429880bda5d52d115c09b649022f90b08263e11e48e586fc36518d0b34538284135094847221f10387b83aa1a30ac023411808b03501a40ce05b02d015c0ac05502a014c064031017808c04401f00f007403801b00d006402e0140070034014009004001c00c0040018008002000⟩⟩
theorem candidate04053_checked : Checked candidate04053 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3157610463232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04054 : Description := ⟨69, ⟨13, 0x26c6d876a134a5536a82453a238ecc71b336194cc6e5ed2d195c4ab253d29213688ec3e11be8d246643191808ba04d42060e906ec34418a0b8855419809104801fc0dc05f02b01540a8053024812008e03601a809c04c02100f007403801900b804c02401000780240100070018008002000⟩⟩
theorem candidate04054_checked : Checked candidate04054 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3164726165504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04055 : Description := ⟨78, ⟨12, 0xf1ae9edbcda5d87d41d29c8ec79b95b1ba9ba848a78608447c879471b6e66cf66b6536375ed5a357155953d50c45d42a41336434933231a3002e826a2061d21bb17115512510d09007d06f05f05b05505405304904503e03703502702602302101d01c01901701301201000e00a008007003002001000⟩⟩
theorem candidate04055_checked : Checked candidate04055 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3166806540288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04056 : Description := ⟨75, ⟨12, 0xf1aea0dbcda6d40d27c8ec79b95b1b8a78608448157ca79476671b6e66d06b566a6516375ed5a353d50c49147745f42a4133e13c93652ff2e626a2061ee1d21bb1551250db07d06f05b05a05605505304904503e03702602302202101e01d01901701301000e00d00a009008003002001000⟩⟩
theorem candidate04056_checked : Checked candidate04056 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3200042205184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04057 : Description := ⟨64, ⟨13, 0x1495a254ffe2550df84a41c9b08d3969026f933e9584872118fc47ca3a61ba0da06b131a17b4b464db23b917c7c237d1b28d1853026610106142d8108077835815c090046823011606d03501a406403101700b0050023011007803a01c00c805c02600e0068024010007⟩⟩
theorem candidate04057_checked : Checked candidate04057 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3208743224064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04058 : Description := ⟨77, ⟨13, 0x27ff0948173f91e38eb87503889b7cda652a282537c9a24ac243908c7e23e51d30dd06d035a18dcbda5a326d91dc8be3e11be8d9469225211007b83781a309f849811a08c03501a40cc064030016c0b405602a81500a603501900c405c02c014008c04401e00e8070032017009803801a009004001c00a0040018008002000⟩⟩
theorem candidate04058_checked : Checked candidate04058 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3208751677440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04059 : Description := ⟨77, ⟨13, 0x27ff11084a3ae1d40e206df36994749be4d0a49d12086040a9f88f9474a3741b40d6c6372f6968c9b647722f904872e37d1b28ccc56629c13509483dc1d20d184f824c08d04601cc0d4069030016c0b405602a81500a603b01900c405e028013008c04401e00e8070032017009803801a00b004802000e0040018008002000⟩⟩
theorem candidate04059_checked : Checked candidate04059 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3209015918592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04060 : Description := ⟨80, ⟨13, 0x13ff8884251d70ea071036f9b4ca3a4df1f88f9474a3741b40c405ed2de168ca7c52527a936c95447722f91148243971be8d9469633315a8a704d42520f7075034613e093023411808b03981a80d206002d81680ac05502a014c07603201880a004602200f007403801b00d006402e013008803801a00b004802000e0040018008002000⟩⟩
theorem candidate04060_checked : Checked candidate04060 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3209024241664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04061 : Description := ⟨74, ⟨13, 0x51da7ff10b84a3ff5d70ea06df36993e09be4d0a49d0887e23e51d28dd06d034d98d8b784d923b917c7be37d1b28cc050825211c87b83aa1a30ac049816808d04601a80d2067030016c0b405602a81500a604501d80d006403101780a004602200f007403801a009803801a009004001c00c0040018008002000⟩⟩
theorem candidate04061_checked : Checked candidate04061 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3217605820416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04062 : Description := ⟨76, ⟨13, 0x14799ffc2b2128f1775036f1b4ca384eb26f934098b4551ff0f9474c3731b40d3a6362de13648ee45f2160f246ca31a1658ad050826811c88183dc1d50dc856024a0a004682300de06a034816c0b405602a81500a604501b80c8062030016009404602200f007403801a009803801a00a004802000e0060018008002000⟩⟩
theorem candidate04062_checked : Checked candidate04062 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3217737940992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04063 : Description := ⟨82, ⟨13, 0x4ffe22109475c3a81c40dbe6d32e516fea3a4df268524e7e23e51eb4f2c7663a51c6cdd06d035b98dcbda5a326d91dc8be4432090e5c6fa3651998acc53826a12907b834615509f049811a08c03981a80d206002d81680ac05502a014c07e03b01900c405e028011808804201e00e8070032017009803801a00b004802000e0040018008002000⟩⟩
theorem candidate04063_checked : Checked candidate04063 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3225658916864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04064 : Description := ⟨86, ⟨13, 0x4ffe1290788173f91e38eb87503889b7cda64df26892b090e4231f88f9474c3741b40c405ed2de168c9b647722f91108563fb1f08ec06fa3651a60b3856a25211007b83781a30ab84fc24c08d046022c0d406903301900c005b02d01580aa05402980c806202e01600a004602200f007403801b00d006402e0130070034018009004001c00a0040018008002000⟩⟩
theorem candidate04064_checked : Checked candidate04064 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3225931481088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04065 : Description := ⟨84, ⟨13, 0x13ff88842520eeffd75c3a81c40dbe6d328e937c9a14939f88f9474a3741b40c405ed2de168c9b647722f91148243971be8d946662cd14e0a104d425211c87b83aa1a30ac04f824c08d046022c0e606a034819c0c005b02d01580aa05402980ec06403101780a004602200f007403801b00d006402e0130070034016009004001c00c0040018008002000⟩⟩
theorem candidate04065_checked : Checked candidate04065 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3226195722240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04066 : Description := ⟨89, ⟨13, 0x27ff094830c0b9ffafe478e3ae1d40e226df369937c98b4ac249d21c8463f11f28e986e83681880bda5bc2d1936c8ee45f1f08df46ca28412908e44401ee0ea86f034615809f849815c08d046022c0d4069034019c0cc064030016c0b405602a81500a603201880c005e02e01600a004602200f007403801b00d006402e0130070034012008003801800a0040018008002000⟩⟩
theorem candidate04066_checked : Checked candidate04066 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3226459963392 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04067 : Description := ⟨70, ⟨13, 0x4d8dd3ed275caaa0514e88e40a9f24f2876638d9ad4ca26372f695c4a7a52426d12448f045e215104c7c23c91bf0c605cc26a0e906ec34418a0aa84941b60cc04881fc0dc05f02d01580aa053024812008e03e01b009c04c022010807803a01900b804802000f00680280120080018008002000⟩⟩
theorem candidate04067_checked : Checked candidate04067 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3232254459904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04068 : Description := ⟨79, ⟨13, 0x9ff424dd3ee0a6dfb56da84c8e4dea68514e89040a9f24f2e7343749ad8d0a66c31b97b4ae253d286136892245e2098f8479237e1990c686022b314e09a84a42070e906ec34618a04882300dc06902f81680ae05602a81500a604901b00c405e027013008803e01e00e8070032017009004001a00a004802000e0040018008002000⟩⟩
theorem candidate04068_checked : Checked candidate04068 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3237067423744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04069 : Description := ⟨80, ⟨13, 0x13fe9b2424dd3ee0a6dfb56da84c8e4de9f24e686e934299b0c405ed2b89494a184da25512448bc42c2098f8479237e1a58cc863430115a8a704d425210387503761a30c5024411808b04081b80d205f02d015c0ac05502a014c092036018809c04401f00f007403801b00d006402e012008804001a00a004802000e0040018008002000⟩⟩
theorem candidate04069_checked : Checked candidate04069 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3237075746816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04070 : Description := ⟨75, ⟨13, 0x847ba75b46d27647ae555029b94d022a511c8153e39ebcf2871b3669ad4ca26372f695c4a4850d26d930c8f042a2098f8479237e18c0bfc5cc2cc14d89a44401ed0e906f03441890aa84fc24a10c06d81e00dc05a02a814c09004001f00d8060026011008403a01900b804801e00e00680280120080028008002000⟩⟩
theorem candidate04070_checked : Checked candidate04070 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3238693765120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04071 : Description := ⟨71, ⟨13, 0xb68530e8953fe9b2c5621bf0938393d7db3ad8469026f533e95846e22310f07e33e49d30d6268433618d0bda57129094348f045e1f08d1863230114c09983d219e0b604201de0d6057028c122090046022c10006e03681a406c03101700b004e024011007803a01c00c805c02400f0068024010007⟩⟩
theorem candidate04071_checked : Checked candidate04071 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3240955478784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04072 : Description := ⟨81, ⟨13, 0x27fd0938173ec9e9ceb974fb889ab4d42647aa094129bd4d125611b888f43c1f8cf9274c35a1a10cd86372f695c4a4850d23c11787c234918c8c044a422010386f031413f093024411806e03481980c805f02e01680ac05502a014c09003601a80c405c02c013809004401e00e8070032017009003c01a009004001c00a0040018008002000⟩⟩
theorem candidate04072_checked : Checked candidate04072 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3240963932160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04073 : Description := ⟨79, ⟨13, 0x9ff469a126f6275cba7dc40d5a6a1323d5a09bd4d0a054fc67c93a51ad8d0866c31b97b4ae252428691e08bc4121cb8ccc6323011598a704d4252103874831413e093028c12208c03981b80d205f02e01680ac05502a014c09003b01b00c405e027013009004401e00e8070032017009003c01a00b004802000e0040018008002000⟩⟩
theorem candidate04073_checked : Checked candidate04073 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3241228173312 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04074 : Description := ⟨83, ⟨13, 0x9ff4d9634d0937b2bae5d3ee206ad350991ead04dea23cfc67c93a51a10cd86202f695c4a7c50d25511e08bc4452090e5c69633318c8c0456a29c135094840e1d40c504f824c091046022c10007303701a40be05c02d01580aa0540298120076036018809c04802200f007403801b00d006402e012008803c01a00b004802000e0040018008002000⟩⟩
theorem candidate04074_checked : Checked candidate04074 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3241236496384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04075 : Description := ⟨76, ⟨13, 0x13fc848b949b7eda56adb50572c9bb4d0a2410c08153cb9df0dd26cf35b1a14cd66372f695c49b63e01cb8df86c833318d0c0056629c135094840e1d20d184f821a09b04601e00ea06902f816c0b405702a81500a604001e80c405e027013008c04401f00e8070032017009003801a00b005002000e0040018008002000⟩⟩
theorem candidate04075_checked : Checked candidate04075 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3243308548096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04076 : Description := ⟨80, ⟨13, 0x13fc9364245ca4dbf6d2b56da82b964dd9df0dd26cf34299acc405ed2b894f8a4a4f526d92a888a42c1f00e5c6fc3641a58ccc63430015a8a704d4252103875034613e086826c11808b03c01d40d205f02d81680ae05502a014c08003d018809c04602200f807403801b00d006402e012008803801a00b005002000e0040018008002000⟩⟩
theorem candidate04076_checked : Checked candidate04076 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3243316871168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04077 : Description := ⟨75, ⟨13, 0x9ff424deceeb974fb569a84c9056829a54729f04dea6851228763f19f24e9469b34219b0c6c52628591e08bc3df1980c6460228412908e440e1d50c5056024c09104601b80d206702f81700b405602a81500a604701d80d8068031017809c04802200f007403801a009003c01a009004001c00c0040018008002000⟩⟩
theorem candidate04077_checked : Checked candidate04077 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3249818075136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04078 : Description := ⟨77, ⟨13, 0x27fd0ad849ba7dab0d4264829a93ae9bd4d0262d1b88aa43aa114ff87c93a61a74d0466c31b1498a1647822f10b079237e1808b2c56828413408e43aa1b90d106282b012504882300dc06b034817c0b405602a81500a604701b00cc062030016009c04a02200f007403801a009003c01a00a004802000e0060018008002000⟩⟩
theorem candidate04078_checked : Checked candidate04078 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3249950195712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04079 : Description := ⟨75, ⟨13, 0xae94ff24d115b856c245d00e6a6f8b695b1ad586a0ae4d4d89d74dda37108c7ab3bd9d2ce046cf34f1a08cd64c323c109c82237e1b20c004d01a20a904f024a10d061026c13408c03c01d80d606902f816c0b405902a815008003d01980c4058027011808804001d00e004801e00e00680280100070018008002000⟩⟩
theorem candidate04079_checked : Checked candidate04079 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3255654449408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04080 : Description := ⟨59, ⟨13, 0x9e347ba2550dd6f73699b14d29678a42d08e7fa3809b40d3a6532db9684aae4c21e40ea86fa3651a30ba04a221d10307b8372171068023410c07103681a80b605602a815009a032014809404601e00e807002c01300700240100070018008002000⟩⟩
theorem candidate04080_checked : Checked candidate04080 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3338676502784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04081 : Description := ⟨75, ⟨13, 0xa15cffe181094781ba81c12da667930b1664a3b4df20b4ff27ca3999bfcda069b31b181cba45bb26112a491c45f1e40ebc7283651980ad44702070f7068c24c0b104682300d4069031816c0b405602a81500a604f02100e006803201880ac04602200f007403801a00b005401c00d004802000e0040018008002000⟩⟩
theorem candidate04081_checked : Checked candidate04081 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3423772639232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04082 : Description := ⟨70, ⟨13, 0x51f28633ff84a3a81b4cd6e679a8ed3e09be4239ff0f9474d3811b40c6c6072ab930895247722f8f2075e37d1b28cc04a223810307b837213c047823411808603501a40b605a02b01540a805302700d0064031012808c04402000f007403801a00b005402600e00680240100070018008002000⟩⟩
theorem candidate04082_checked : Checked candidate04082 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3492490018816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04083 : Description := ⟨72, ⟨13, 0x14319ff424dd3ed6e6a132414d29f04dea1d4ff87c93a69c08cd863630396ecb16558293142c9824a923c11787903af1980c6460225111c06e434418a09e024411e08c03701a40be05a02b01540a805302380d8068031013809404402000f007403801a00b005402400f00680240100070018008002000⟩⟩
theorem candidate04083_checked : Checked candidate04083 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3524702273536 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04084 : Description := ⟨81, ⟨12, 0xf99f03e9edebda5d71d41d29b94b33a9e9a19729268f68c382d7c87ad7966cf6b769b66b6536375ee55850c4dc4c245d4434123ad3973643002e82b329c2362071bb1a317115513e12610d09406c06305f05b05505405303f03903402f02b02a02702302101d01c01901601201000e00b008007004003002001000⟩⟩
theorem candidate04084_checked : Checked candidate04084 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3527447478272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04085 : Description := ⟨74, ⟨12, 0xe9eda5d87d41d29c8eb95a9ba848a78607c879471b6cf66b6536375ee5a257255853d50c4dc4c248f45d42a4133c739637e36434933231a3002e825121f1d21bb17115512510d09005f05b05505405304903e03502702602302101d01c01901601401201000e00a008007003002001000⟩⟩
theorem candidate04085_checked : Checked candidate04085 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3647842877440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04086 : Description := ⟨72, ⟨13, 0x15d5a6c45ba1bf09183a4121f32e9b74039b1be2da56c4b4955329f04dda67d2b28c33e29eacefa7023679a68c9e5582610d9068c3301800ac05342070c405bc2a413c09304341b40b805702680f006d034819c0c605f02c815408003401880b8056027010007402c0120070034010007002000c004000⟩⟩
theorem candidate04086_checked : Checked candidate04086 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3784067809536 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04087 : Description := ⟨81, ⟨13, 0x27fd0c6849be65d3ee096b8b50991ca9c4f826f5342972461a29d1208153e49cccd6c69b33618dcbdc55829e943092245e2090f887903971808acc5382070e906ec34618a09f049812208c03701b00d206302f81680ac05502a014c09203601a00c405e02b013809804401e00e8070032016009004001a00b004802000e0040018008002000⟩⟩
theorem candidate04087_checked : Checked candidate04087 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3786689019904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04088 : Description := ⟨56, ⟨13, 0x13c68b744a9ff6f9a74f3691b14cf154ca8ed2188c43e41b38d365b72d095648ba3631a30cc04a41a30b884981e80d005c023410c06d03501800be05b02b015009a03401900a004e02300f0070026012007002400e0040018008002000⟩⟩
theorem candidate04088_checked : Checked candidate04088 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3853839794432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04089 : Description := ⟨60, ⟨12, 0xf9ae9eda4c8ec2ab94b30a54a3b92590c8c47c86ce6b469b5ba5a155945d3633493302521a31711260f40d00b808d06a06005f05b05605405304f04e04d04903f03503403202802702301e01c01301200e009007004003002001000⟩⟩
theorem candidate04089_checked : Checked candidate04089 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3853839859712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04090 : Description := ⟨54, ⟨13, 0x525678ee9e6d2361d9e27c83671ac4ae4559286137091e45d2098f246f83631990c6843e2060dd85c424a0f4068024011a085035017c0b605602a0134064027011807803801900a004c02401000700280120070018008002000⟩⟩
theorem candidate04090_checked : Checked candidate04090 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3853967753472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04091 : Description := ⟨58, ⟨13, 0x4f1a3db15a8953a79b48d8a678a42d1ba8473fd1f20d9c69d2db9684ab245d2138f246f83631a30c6843a2060dc85c424a0f4068023410c07603681a80be05b02b015009a032014809c04a02300f007002601200700280120070018008002000⟩⟩
theorem candidate04091_checked : Checked candidate04091 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3853971915008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04092 : Description := ⟨65, ⟨12, 0xe9eda4c8ec2ab95b17a9ba84a5493e90b8dd8a88477fa7c86ce6b469d5ba5a155945d42a3c937c36334931a21d2061b91711250f40d008d06a05f05b05605405304f04e04d04903e03503202902702502301e01c01301200e00a009007003002001000⟩⟩
theorem candidate04092_checked : Checked candidate04092 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3853971980288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04093 : Description := ⟨57, ⟨13, 0x27fb3c49b245c6254d9f6c533c537890c4621f20dd065331a167ca7450c26e0d8468c33214e09484061ea0dd868c24c0f1068024411a08b04081b40d405b02b015009a03601900a004e02300f00740380190080038012007002000c002000⟩⟩
theorem candidate04093_checked : Checked candidate04093 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3854074646784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04094 : Description := ⟨52, ⟨13, 0x13c4846ba65b3ed2367726dcf866c932694f8a4a4f522290487c434b1998ad45382520ea068c27c12606802bc136091046823011606a02d81580a8053019008c03c01c00d8068032011007002c012007002000c002000⟩⟩
theorem candidate04094_checked : Checked candidate04094 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3861859274768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04095 : Description := ⟨54, ⟨13, 0x54ae7fb3c49b338f1bd4d9f6c6b3c57f09bc3e41c54ca66342cf93709863611990c643d41bb0d105481e20d004a024411a08b03f81a80b605902b015009a04701b00c804e02300f0074038019008003c01c009003800c002000⟩⟩
theorem candidate04095_checked : Checked candidate04095 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3866953257216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04096 : Description := ⟨60, ⟨13, 0x12ff950c23dd38e687053689a80c295e5a6e4f8c79239a1b30cd45a22b914309b84131e48e586fc2ff1730a704a41ec0dd868c2e00f306d832013207a03c01b80b605702b0108080036011807c03c01900a004802000e0068028012008002000c002000⟩⟩
theorem candidate04096_checked : Checked candidate04096 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3921595138304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04097 : Description := ⟨64, ⟨13, 0x12fe95d47c23810da847ba71cd6e0a6d13501852bcb4dca1dd08e7f83e31df8e686cc335129091c4271e48ea86fc2ff1730a684a41ec0dc868c2e00f306d83200f607803b01c40dc05b02b815808404001b00b804a02300f807802400e0068028012008002000c002000⟩⟩
theorem candidate04097_checked : Checked candidate04097 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3921599299840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04098 : Description := ⟨71, ⟨13, 0x847ba71c14da26a033c991cbe45e5ae55662b1a57528113729a245421dd08e7f83e31e54efc73436619a894e48e2150f2475a37e17f8b985342520f606e4346170079836c190078037016c0ae056029813c092043021010007c03901b00b804a02300f807802400e0068028012008002000c002000⟩⟩
theorem candidate04098_checked : Checked candidate04098 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3921599365120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate04099 : Description := ⟨62, ⟨13, 0x4fea6c92fd935ba65cd6e0a6cfb501852bcb4dc9fe4e686e93351944c6853a286137091a45b213904c79236117f8a704a41ea0dd868c2dc0f106d832013609104582040ec05b02b815808404001b009c04602200f807803a0190080038014009002000c002000⟩⟩
theorem candidate04099_checked : Checked candidate04099 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 6)) 3921602941184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate04099_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch040

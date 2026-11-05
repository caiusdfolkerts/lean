module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch080
open Papers.RationalityTen GraphCandidateCoverage

def candidate08000 : Description := ⟨74, ⟨13, 0x589aa5944a863410df32f6d7a8bcedd3ee7372bb905b4ad876b8a7c12da8c344ba1ed0ca7c93ce9e04ed66cf3589a6cbdc55828612448bc4121cb8d905382070dd868c31413e093043415809004601b00d206302f81680aa05401a00c4056027011007403801900b004802000d005802000e0040018008002000⟩⟩
theorem candidate08000_checked : Checked candidate08000 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179382046976 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08001 : Description := ⟨77, ⟨13, 0x218cf997a8ba7dcaeda56b8b2597cab9c575aa7d4129f04b8230d12887b4311f24f347813b41b3cd6869b30297b8ab052928613dc92245e21790487fa3971b20d245382070dd868c31413e093043411806c034818c0be05a02a81500a203501a00c4056027011007403801900b004802000d005802000e0040018008002000⟩⟩
theorem candidate08001_checked : Checked candidate08001 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179390435328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08002 : Description := ⟨81, ⟨13, 0x2c4d5b6a96512a49118f8b0c5160a303179dbb49d3ee7672b3905c18da56c3b5cd6e4ab9545a9bd2f695b4329ff0f927a03c01dace6c6cf3589a74bdc55828612448bc4131e38df86c833218d0a6c4d6251110062827e125086824011806902f81740b405502a00c404e025011007403801900b004802000d005002000e0050018008002000⟩⟩
theorem candidate08002_checked : Checked candidate08002 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179514167552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08003 : Description := ⟨82, ⟨13, 0x492231f1618a2c0c5da4e9f72b3831b4ad7364b2f956c4aeb55caa114dea094ada188ff87c93c01da0e6c6cf35a1a74c0a5ee2ac14a4a184f724891788544131fe8f1c6fc3641a48cc863429b135894444018a09f849421a08c034817c0ba05a02a81500a203e01a80c404e025011007403801900b004802000d005002000e0050018008002000⟩⟩
theorem candidate08003_checked : Checked candidate08003 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179522555904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08004 : Description := ⟨79, ⟨13, 0xb1350c657718f8af452208afcb79a3badd3ee6f72eb831b4ad8c6b72ae54d69f04bda56d0ca7fc3e49dece6c7023679808ab052c28813e88bc4111e38df86c833018d0aec53e27e128873c37218a09e049421a08f04602240d206502f81780b405502a00f4068031013809404402000e807002c01200680280100070018008002000⟩⟩
theorem candidate08004_checked : Checked candidate08004 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179782570240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08005 : Description := ⟨78, ⟨13, 0x589a31f1418634145e76e9f7063695ae2c965f2aae5510a6b4f825bd1ea85e40a9f24f327363679ad8d366052f71560a5250c27b92448bc3c71cb8df86c831a15c0a044a21d20dd862827c12508682300ea06c034817c0b405502a014407a03401880b404e026011007403801900b004802000d00580280100070018008002000⟩⟩
theorem candidate08005_checked : Checked candidate08005 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179786797056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08006 : Description := ⟨82, ⟨13, 0x53ea9672bb8634141e70e9f72e383db4ad7164b2f95572a88535a7c12e08c344a21ed0c47c93be1cc8dd26cf34d9a14c7a6042f81628a804f325512448bc42e2080f2c72e3641a58adc53c283127875037618a09f048c21a08c03601a40be05a02a81500a203d01a00c4056027011007c03a01c00c0048022010006802c0100070018008002000⟩⟩
theorem candidate08006_checked : Checked candidate08006 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179793039360 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08007 : Description := ⟨81, ⟨13, 0x2daf5b2a7ed3269612bb92244b212708182bbf35f02eeb76939c9cb2e3d709368db18d7355ba9bd37a97e462a25d0ee7fc3bf1cc0dd26cd34e9a14c205f027d12448bc4151e30cc86022be14c8a244a82200f6873c27e12308602300dc06902f01740b405502a00e806c031017009404401f00e807002401000680240100070028008002000⟩⟩
theorem candidate08007_checked : Checked candidate08007 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19179982831872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08008 : Description := ⟨80, ⟨13, 0x16b0b13533a96534595dc58e28efcb79a3badd3edd86d2b631ae8c6c5d9aae54d89d74bda56d13487a432a0c0f9277b39b1c08d9e69e3411840be052f28793e898a45e2080f2c72e3641998c5c4fc26b110073c37818a08682300d206502f81780b405802a815007a033018809c04402000e807002400d005802000e0050018008002000⟩⟩
theorem candidate08008_checked : Checked candidate08008 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19184077521152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08009 : Description := ⟨81, ⟨13, 0x296534595dc58e28ef3874fb761b4ad7462e2f95766ab9541a9b13ae95b43d21890607c93bd9cd8e046cf34f1a08c7a6042f81628a4650f279931495445e21710407963971b20d2c66631714189ac4401d40de062821a08c034817c0b405802a81500a204801e80cc062027011008003a01c00c004802200d005802000e0050018008002000⟩⟩
theorem candidate08009_checked : Checked candidate08009 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19184085909504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08010 : Description := ⟨80, ⟨13, 0x14af9a2caee259093840c15df9af617a9bbadc7add86d1b631ae8c6c5d9ad3d4dca244dea5f918a88c43c1f8cefa7353811b34d3c68430817c0a5e50f27d13148bc3e21cb8ccc6022be14c8a244a82200f6873c3781a0086028c11806e03481780b405802a815006c031017009004402000e807002400d00580240100070028008002000⟩⟩
theorem candidate08010_checked : Checked candidate08010 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19184143581440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08011 : Description := ⟨77, ⟨13, 0x2b6b52fa6446fe12708182bbf35ed8f4876938e1be2da36c6b5cd766b6f51226f52fc8c53fe1f8cf3a76e39a9b34d3a68430817c0a144c524891787ea3321808af853228912a08803da1a00a904fc2180a204601d00dc06902e81680b205502a011c06c031017009404802200e807002401000680240100070028008002000⟩⟩
theorem candidate08011_checked : Checked candidate08011 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19192465080576 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08012 : Description := ⟨80, ⟨13, 0x176bad953f6957418922452a1fb093840c15df9af6c7a43b49ce4e5971eb849b46d736aaadb94e8a274dea6ad3028f744b21c8ff879c3c19d9ce786cd34e99fcb1449122f0fe86643011678a084722200f687542b013f086028811c08c03701a40ba05a02a815006c031012808803a01c00c004802000d004802000e0060028008002000⟩⟩
theorem candidate08012_checked : Checked candidate08012 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19192867733568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08013 : Description := ⟨80, ⟨13, 0x1935b26554aa2b4a7970c79e35513c7d9bb41c46dd66d23509986c116042da561cabb541a99d4ac917479a2050c48174009f94f0e7073759b38d3068233616b0b1051627b92b092c47a20e0e707003631968c5c60221a0db06282e213907a02d811e06c030817c0ba05802b015009c04c02400cc04e01e00e00480120070018008002000⟩⟩
theorem candidate08013_checked : Checked candidate08013 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19245255704704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08014 : Description := ⟨81, ⟨13, 0x2a7f4ac962ca923cf1aa888bf79da0ea27273759b88da869fb30d7beb695872aed510a72528a49521289443f205d0027cc3bc9c1cdce6d234c1a14cd25ac2c413c895849622e90707383801b18cb454a21a10207b436c1890b884e424610c07a02a013008f03601a80c205d02c015009c04c02300c805001f00e004801c0090038008002000⟩⟩
theorem candidate08014_checked : Checked candidate08014 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19247402139776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08015 : Description := ⟨86, ⟨13, 0x64cac9753ca3fd0fe57f1d288a430612eff378ebb39c9ce236ea371dae4d40695b04980abe25b4ac655faaec4fda7052ea91a44a21f90ba8043f21de4e6870a3729a8ccd46552d616349e44a7245917c8383911bd8d946702ff1730a9444a2090db05c0272123079836c17809803d01c00ba05b02c015809c04602180dc04601f00f003801a009004000c002000⟩⟩
theorem candidate08015_checked : Checked candidate08015 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19280670834816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08016 : Description := ⟨75, ⟨13, 0xaa650da3c31c2893c38619704b7fdbf39ed4f33776b6f9b4cd2957fa8ed3dc90c43d9ff8f026ff3741b40d3665330696dcb4259029614409de4af249905872837d1b28cc05d02520f7068c2e212604682180fc06a030016c0ac05502a013407003401900a004601e00e807002600e004802000e0040018008002000⟩⟩
theorem candidate08016_checked : Checked candidate08016 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19281865638144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08017 : Description := ⟨78, ⟨13, 0x553286d1e1865b6f9b4cd2967bb259864aff5762945476a0b4f725d524a90c47c22510f685d40b9ff8f026ff3741b40d3665330516e8b4258d29494409e44ac249905872837d1b28cc05d02520f7068c2e212604681a80c005b02b01540a804e026811807003401900a004601e00e807002600e004802000e0040018008002000⟩⟩
theorem candidate08017_checked : Checked candidate08017 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19281865703424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08018 : Description := ⟨76, ⟨13, 0x17dca98523e89f33c97bc7ea38b164892439215efe17a83aedbaeda6694b199842b24577aa3949ca0e4eca42d0f47e53809b40ca650d26191d872c37d1b28c645d029b13588183dc1bc0d105c427e0b504682140d406102d81580aa05402680c805202300f007403801900a004c01e00e004802000e0050018008002000⟩⟩
theorem candidate08018_checked : Checked candidate08018 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19285890105600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08019 : Description := ⟨77, ⟨13, 0x266b2e78f0c70a24f0e1857bfb5f9cf33776baedba4da6694b199842aff537276521687a3f29d34da069e3299834b6e5a12c814849de4c325791d882c3941be8d946322e814f887440c1ee0d105c4278093046821810007e035016c0ac05502a0134070032014808c04001e00e807002600f00700240100070018008002000⟩⟩
theorem candidate08019_checked : Checked candidate08019 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19286158508288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08020 : Description := ⟨78, ⟨13, 0x4cf25ef1e1857bfb5d76dd26d334a59eec5f608abfd5d8a6e528a82d3b290b47c21e90ba8173f29d34da069e3299828b745a12c694909e44c325611d882c3941be8d946322e814f887440c1ee0d105c427809304681a80b605602a815009c04d0240118070032014808c04001e00e807002600f00700240100070018008002000⟩⟩
theorem candidate08020_checked : Checked candidate08020 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19286158573568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08021 : Description := ⟨78, ⟨13, 0x5a9ecc554ca0d4f4e5f51c2893c38600afec7e73dbde66eed75f3755b4cd2963330855fea6e4eca43105c7e13c09bfcdd06d0342194cb8a5a02c814bca1e4ef25791e87c43651998ba053c21f10207b834017109f02340fc070035016c0ac05502a0134070032014009004601e00e807002800e00580240100070018008002000⟩⟩
theorem candidate08021_checked : Checked candidate08021 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19286160589056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08022 : Description := ⟨82, ⟨13, 0x5e86cbf62aaa64ffe7ad2f98f3449e1cd0ca825c021fdef6a799bbc9d7ae576efb70da46c1e5f4abfd3de9be4861f88f9478137f9ba0da060d2e4167ca584ef25912488f24121f10e4c6fe3331728a704a4221101868c2dc13e09303c411a08c03f01a80b605602a013407003201880a004602200f0074038019007002c012007002000c002000⟩⟩
theorem candidate08022_checked : Checked candidate08022 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19289381802240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08023 : Description := ⟨82, ⟨13, 0x5932a6143399ccb7a3dd1be8aec4a615efed7e73d5ddaeebb71cb7b9b4cd295fc2c915de9f24eca42d0ea8473fd1f94e026d034e994cc1a5b72d09640a164c324991d88643f51d50df46ca3191740a7c43a2060f706e434417104682180e8071035016c0ac05502a013408e032014809404601e00e807002600f00700240100070018008002000⟩⟩
theorem candidate08023_checked : Checked candidate08023 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19294480007424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08024 : Description := ⟨83, ⟨13, 0xb2654c28672de8fd471615efed7abbb5dd76da6694b3dd8c6bf858c2ba150ea534f927652168f843aa11cff47e53b19c60e026d034e994cc145ba2d09634a164c324991d885e3f81d68df46ca3191740a7c43a2060f706e434417104681a80b605602a815009c04d02380f0072032014809404601e00e807002600f00700240100070018008002000⟩⟩
theorem candidate08024_checked : Checked candidate08024 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19294480072704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08025 : Description := ⟨85, ⟨13, 0x2f7b646a0bcffe7ad2e091fc7f23c7145866c2c60970087f7bd45db2ebd70536e1ab6d2367eaf99646b0a57627b537c92f48b23e0ff27ca3719b40c805d92e596c89e84dc25592348624181fd0ec47303861990b945742a114188e844220f0dd85b82400f1049023411806a02d815c0ac05402100c8062023011007803a01c00c004001c009003800c002000⟩⟩
theorem candidate08025_checked : Checked candidate08025 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19298105954368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08026 : Description := ⟨86, ⟨13, 0x5eaac61533a4ed13e80333c962c7de3b71c88ab44ca1c90967d9bd41d3ce566ebb695ab0d41694b1997deb21582abc9500a5c50727011ba87a3e41e00e026cf34119acca65a22b9143498645d2098e586fc3641800ba053626b0de06882e213f092843416e06b030817c0b605502a00cc052027011807403801900a004801e00e005002000e0050018008002000⟩⟩
theorem candidate08026_checked : Checked candidate08026 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19320182735104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08027 : Description := ⟨83, ⟨13, 0xb1852ca80333595ac7d23bd159870c259f92f33776ba79cbadd26d2b561a82d296332fbd602a6c4e023750f47c83bd9b3cd3c682335994cc1a5c22d31614a424ef26192bc8ba4111ca0df86c83001740a7c43a1a20b884f024a10d049821010007e035817c0b605502a00f4070033014809c04602000e807002400f00700280100070018008002000⟩⟩
theorem candidate08027_checked : Checked candidate08027 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19320451137792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08028 : Description := ⟨84, ⟨13, 0x1630a5950066792c58ef4259d3ce5d6e93695ab0d41694b3e98bebdf58f2c05506a6c505a7011e68dd43d217502e7c83bd9b3cd3c682335994cc145bf2d31620a484f226192b08ba4111ca0df86c83001740a7c43a1a20b884f024a10d04981ac0be05b02a815009804802300f4070033014809c04602000e807002400f00700280100070018008002000⟩⟩
theorem candidate08028_checked : Checked candidate08028 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19320451203072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08029 : Description := ⟨87, ⟨13, 0xbd25972c5b3fe963c72a35b144896439a195098825bf59ecaf387793a91caeddf6cfb569a84d2360daffd7d8ad153727bd37a9113f19f24f026ff34219b0c1a5962ba9484a1a4fa25912488c04121f10e4c6c233318c8c045ca29c12908843d418a0b704f824c0f1048823010005c02b0150070036018809c04802200f0074038019007802c012007002000c002000⟩⟩
theorem candidate08029_checked : Checked candidate08029 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19321594056960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08030 : Description := ⟨87, ⟨13, 0xb07d4ce96b433a00cce63e11bc8adc4ae12cfc97abbb5dd3ce3e6f73695ab0d41694af39642b0557929a93e49c046ea1d508e7fa3e41e00e026cf34e9a08cd66533069708b4c585285930c92645d213900075437e1b20c005d029f10e86e4344171092843410807603881ac0be05b02a815008e033014809c04a02300e807002400f00700280100070018008002000⟩⟩
theorem candidate08030_checked : Checked candidate08030 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19328772636928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08031 : Description := ⟨88, ⟨13, 0x160fa99d2d68674018fbc72212cf5776bba79b4ad586a0b4a59f4c635e72c6960aae6542a9a94aa9f24e023cd1ba8754239fe8f907803b41c60e026cf34e9a08cd665330516fcb4c588285930c92645d2150ff475a37e1b20c005d029f10e86e434417109284340d605f02d81540a804c02380f8072033014809c04a02300e807002400f00700280100070018008002000⟩⟩
theorem candidate08031_checked : Checked candidate08031 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19328772702208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08032 : Description := ⟨92, ⟨13, 0x1909becd8c2a914b2a0ed0065f52b58fcc7762c7147870c2ca12cfc9799bbb5d3cdd86d2b5d1a82d296653199842bef5daac094d89d54e024410f47e53e41dece046e63679a78d0466b3299714b4a585297943c9de4af23d11748203971bd8d906663171800ba04d62200de05c421a08403f017c0b605802a815007a037019809c04602000e807002400e005802000e0050018008002000⟩⟩
theorem candidate08032_checked : Checked candidate08032 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19389170598144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08033 : Description := ⟨91, ⟨13, 0xc84df66c61548a5950768032c58eec51e16509674f3761b4ad746a0b4a5986c5f608af7d76ab195812a0d4d8a0b4eaa7012208f343d217502e7e53e41dece046e63679a78d0466b3299694b1050f27912b08f445d2080e5c6f63641998c5c6002e81358880378171086817c0b605802a815009c04c024011807a037019809c04602000e807002400e005802000e0050018008002000⟩⟩
theorem candidate08033_checked : Checked candidate08033 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19389170663424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08034 : Description := ⟨89, ⟨13, 0x2f4962d9ff4eaa5c92c78e545122590e685a4261facf5079c3bc9d80ea4711b67dae8d42691b329820bec58229b93a89bd48821e8fc07c93a69c08d3c66c3069720b2c55c29094349f44b223a11808243e21bf8d846663191808b9453626b10407a83781a20c505b81e20c7048823010005802b0150082036018809c04402000f0074038019007802c012007002800c002000⟩⟩
theorem candidate08034_checked : Checked candidate08034 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19390311436544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08035 : Description := ⟨89, ⟨13, 0x2a674019cccce65171ee8de457629712b857c259f92f5775dba79c7cdee6d2b5b9a82d296652ed5648b0457929a53b29c048821d508e7e53e41c08d9e66b3299834b6e5852ac942c98647622e90c882c4001d50df46c833018c8c005d029f10306e434417109e043411e08604201c40be05b02a815008e034013809404602000e807002601200780380100070018008002000⟩⟩
theorem candidate08035_checked : Checked candidate08035 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19397357895936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08036 : Description := ⟨90, ⟨13, 0x54ce8033a0945c7ea39114b857c259eaeebb74f3695adcd41694b30d8c6bb55ce2c61608ae6543a9a54aa9d94e024411e68754239f94f9076838c1c08d9e66b3299828b745882ac942c98647622e90bc82c3fd1d68df46c833018c8c005d029f10306e434417109e043411e05f02d81540a804e026011c072034013809404602000e807002601200780380100070018008002000⟩⟩
theorem candidate08036_checked : Checked candidate08036 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19397357961216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08037 : Description := ⟨85, ⟨13, 0x2a674b5a0ed00639114a8594259e3ae9e6d2b5cda82d29661b18d76aae6542a9a94aa9d54e024411e68754239f94f907803b41c60dcc6cf34e9a08cd66532d29620a144dc23d117482a3fd1d68dec6c833218b8c005d026b11005c427e10d05e817c0ba05b02a815009c04c02380f8072037019809c04a02300e8070024010007002000e0050018008002000⟩⟩
theorem candidate08037_checked : Checked candidate08037 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19397492162560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08038 : Description := ⟨81, ⟨13, 0x2ac941da00c7762790b284b3f19d3cda56b8b505a52cc3631aed5632b024eaa70124889342f9f94f9079938d1b98d9e69b34119acca65a52c414289b847a22e904072e37b1b20c5c6002e814088d837617109f043416c0a7036017c0b605502a013809804701e80dc06803301680a804e02300e8070024010007002c0100070018008002000⟩⟩
theorem candidate08038_checked : Checked candidate08038 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19397756403712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08039 : Description := ⟨85, ⟨13, 0x2fab642a92cffa7552f68ffc6e22bb0e385a4261facf4b7603a91c72df86cfb5cda84d236652ff1648ae44ea26f52208753fe1f80f9269d3361834b905962ae11d08c04321fa8ee06fe3611990c646022e514d89ac4101ea0d106282dc13f07882ec12208c03f81d00ba05602a011c082036018809c04a02200f0074038019008003c012007002800c002000⟩⟩
theorem candidate08039_checked : Checked candidate08039 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19398632935680 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08040 : Description := ⟨87, ⟨13, 0xbdcdc2e96d4159ff4eaa5ed1ca89fc2d213104b8043f59f40f4c7593a91caedc36cfb5c5ab4d42691b075802ae74f826f525e8f34401f74f9269b3361900b96586295941c9564802300fe87c43b11b08c045ca2ba1508a0c47420f0f506ec33a18a0b704f81e209c04882300fe06c02e01580a804c01b00d0062027011007803a01c00c0040016009003800c002000⟩⟩
theorem candidate08040_checked : Checked candidate08040 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19398903468096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08041 : Description := ⟨94, ⟨13, 0x4ffe5a92bc8ed470a2230c684a412dff6fce7a8bae1d40e576df3699ae2bfe5f32c115d8a3b4f826f92ea92547c21ecfc47ca3c09ba0da069b321985cb685b02cd1474a024e525b1268908468211901c7d63bc1d00e286dc32a17c0b7c5842a9148096c48a1fe0fb87203581810b4052c25e104075834811a08c04301b00d4069030016c0b405602a815009c03401900c4050023011007803a01c⟩⟩
theorem candidate08041_checked : Checked candidate08041 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19435410685953 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08042 : Description := ⟨75, ⟨13, 0xa9452da92f44c89fc13a006fc67b13d31e76ef072bb5c5ab4d42694a9a52f092d47822310ec86540d1e04d36684336194c8243e21cb8c646022e814e094840e1bb0c505c427c126053828c12207f03701b00be05c02b01540a804701b00d004e02400f0074038019009004001e00b004802000e0040018008002000⟩⟩
theorem candidate08042_checked : Checked candidate08042 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19451508490496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08043 : Description := ⟨76, ⟨13, 0x14b689fbd31caed716ad3509a52c93573a9a54aca0b4baa4a91e688f43b218902e78134d9a10cd865330516fcb1052427b92b08243e21cb8c646022e814e094840e1bb0c505c427c12604881fc0dc06c02f81700ac05502a013009004701b00d004e02400f0074038019009004001e00b004802000e0040018008002000⟩⟩
theorem candidate08043_checked : Checked candidate08043 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19451516878848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08044 : Description := ⟨87, ⟨13, 0xb1852ca80333c962c50a12cf5074f3945bb0da56ba3561a82d2962faf7d63ca83536282d3808f343d217502e7c83bd9c08d9e69e34119acca660a2df9620a4850d279130c95845d1cb8df86c83331800ba053626b11006f034417109284340ea06b02f816c0b005502a013009004601e80cc04e0230100074038019009003c01c00b005002000e0050018008002000⟩⟩
theorem candidate08044_checked : Checked candidate08044 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19457890123776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08045 : Description := ⟨80, ⟨13, 0x162ca9950c67f32b78debff1f90f5479bbba9d3ae5a71eb7c1b46d6e69fa8ed3e092d47f21dcff87c73be9c08d9a6693069708b0a51020b0cc056029a14488cc40e1ed0dc868c31213c093043015e08f04602100f006e03501a40ce06202d01540a804001b00d0064031017009404402000e807002400e00680240100070020008002000⟩⟩
theorem candidate08045_checked : Checked candidate08045 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19469758923008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08046 : Description := ⟨92, ⟨13, 0x14b0a00c7d228b096825c001f92f4d78eba79ca8dbf6d2b5cdab6d41694ac794de9c04baa4a91e68774239f20efc6e93679a74d0a66b32998e8c0c5bb28613d09b845d216104c75e37e1b20cc86343001740ad450626b12908e04402070d185c427e10d04201980be05d02d815c0aa05402600b804e025011807c03a01c00d0064030015009004001c00a004001c00a0040018008002000⟩⟩
theorem candidate08046_checked : Checked candidate08046 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19471041298432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08047 : Description := ⟨87, ⟨13, 0xa5950066731f48a14259f92f5074f3945bb0da56ba3561a82d29631ac794d89c0479a1e8f9077b3811b3cd3c682335994cc746062dd9498a1a4f426191748583af1cb8df86c83331800ba053628313588e04401bc0d105c424a10d04201d40d605f02d81600aa05402600f4066027011808003a01c00d0064030015009003c01c00b005002000e0050018008002000⟩⟩
theorem candidate08047_checked : Checked candidate08047 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19475069927424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08048 : Description := ⟨91, ⟨13, 0xb15500a6792f195fc3ee1610977a83a81ca2e236ec3699abad40693b17d828be25b4ac795d8a254ed27051f087a42ea048f9477b3a69c08da06873351944c145bf2c69490a1a4f2261929c8f045f1f10f2472e37e1b28c605fe2e614d89ac4401ee0de068824a0db03a816c0b405802b015409004602180f4046022010007803a019007803801a00b00500240100050018008002000⟩⟩
theorem candidate08048_checked : Checked candidate08048 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19491125788672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08049 : Description := ⟨96, ⟨13, 0x152da5dd20a86f40599ccbba5791c28a5c25208effc7e53d69e0eebc751b969c76df06d335f1ab8d3e692a9a54769f04df25e125a8fb43a21290627ff3f31f34efa74d3811b40d34686334193cc1a5c22c8142c98647822f90586ca33018c8ac053427e12908cc40e1ee0df068431016f09e04981b406a034819c0ca06202b015408e03401900c405c02000f007401e00e0068024010007002000c004000⟩⟩
theorem candidate08049_checked : Checked candidate08049 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19499822907648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08050 : Description := ⟨97, ⟨13, 0x296d3ff8e1454222f0cc84d412e000fce7acbc29d7eea672bb699af6d5f69db4898c6c185f32bb14d2a3b4f826f92ea92a47c21d905c7e33e51e04da069b34218e8c0c5bb2c494249be4c624a11ec8c44121fd0f8875e3971b28cbc6362fd1720ad453828312908e040e1ee0de867c30c16d09f04981b008d04601580aa04701a00c8062024011808803c01d00e006803201800a802c012008002000c004000⟩⟩
theorem candidate08050_checked : Checked candidate08050 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19499835197440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08051 : Description := ⟨86, ⟨13, 0x589ea5b3ff888c31a12904e801bf45ea2ea072bb699ae2be657628ed3e09be4b8a4991e887b42fa050f947813b29c68da069b30516fcb1a50c26e12448be4121f10e5c6ca2b314e0a044a423610387b83761a309f049811a08c03601a80d205b02d01580aa05401a00c806202f01680a804602200f0074038019008003801a00b004802000e0040018008002000⟩⟩
theorem candidate08051_checked : Checked candidate08051 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19504121839616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08052 : Description := ⟨92, ⟨13, 0x1627a04425209d0037e8ba81ca0e26706b76db84da96bbb579a7ad245f32da563caec4df26952e292647a217d0287ca3bd1d40e6e7053761b4cd426883339938c145bf2c6917c7c43c91cb8df86ca33318d0acc50226b12908d84402070f706f034613d092042c1e40d903a81a80d206602d816807a03201880bc05c02d015008c044019007003401600a004802000e005002000c004001⟩⟩
theorem candidate08052_checked : Checked candidate08052 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19512573493248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08053 : Description := ⟨98, ⟨13, 0x502257923f8fa470a12904b8003f39d40e507133835bb6dc26d4b5ddabcd3d6922f996d2b1e57626f92ea92a47c1f28ef475039b9c14dd86d33509a20cce64e31d1818b7658927a12a48be42c1fd0f887923af1cb8df86ca33318d0ad450626b12908e04402070f706f034613d092042c1e40d903a81a80d206602d816807a03201880b804602200d0064030015007003401600a004802000e005002000c004001⟩⟩
theorem candidate08053_checked : Checked candidate08053 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19512581816320 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08054 : Description := ⟨96, ⟨13, 0x17c0ab0d4b2997496a0ed0065c32a48f0452a1910b284b3b51d3ce416d2b505a52cc7631afe179cbb558dac015d6a8553529553e49d54e024a51ea89342f9ff8fca7c83ca1d90e366e63679adcd0466b3299680ae450a26e123c8f445d20a8ff472c37b1b20cc862e3001740a0443e1bb0b8855421a05f02d81540a804d02380f806e033016809c04602100e807002801200800380100070018008002000⟩⟩
theorem candidate08054_checked : Checked candidate08054 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19534926921728 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08055 : Description := ⟨85, ⟨13, 0x2c1f5529cec79229112b7f6bb5dd3ce5d71f3775b82d6e6a0b31d79cb9957f29ad4aa90b46ea11cff47c83bd9da0e006eb3359818b785a12c51564a204f424991748223f91cc8df069833018d0c0053e28310e88183721710ab84f024a10d07a023c0ec05f02d815009a03e01e80d0052027012808c04001c00d006002601200700300140070018008002000⟩⟩
theorem candidate08055_checked : Checked candidate08055 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19538991153152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08056 : Description := ⟨98, ⟨13, 0x554673b1f38f0c7062570cb84b412dfe0f9d7aa39c1cb4e3e6f03701b4ed6e6a0b31d79cb9c58eabfd5d6a554f727012ea90a470231d0ee8473cd1df4ed06fe3751b44cd66062de1684b1455928813d092645d21590587f23b01ca0df46c834c1980c005d02b514d0a0c4a422210287b03721a30ab84f024c10d079823c0b605402680e006802e012808c04001c00d00600260120070030010007002000c002000⟩⟩
theorem candidate08056_checked : Checked candidate08056 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19539090243584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08057 : Description := ⟨91, ⟨13, 0xaa64ffe5db1d5893c31612904b7f13da9e66eb8750395dbaadbe6d3305d5fea514f7a6f92ea90c44a2174fc47ca3c09bfcdd06d0321985cb9259b29b13b096649d24211a08464071f58e3871436e1ac0cf05f02df1610aa452025b11607f83ee1e10d606042d014b09784101d60d2046823010a07e03801a80d206002d81680ac05502a013408c03801900c4050023011007803a01c⟩⟩
theorem candidate08057_checked : Checked candidate08057 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19564259704833 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08058 : Description := ⟨85, ⟨13, 0x2943485a2047ce3c3129865c11dffafdf7aa3cd5daee376fa378db52d906bfb4f5a58aff51da7b92f08774239fe8ee275037e9b4cd3266732b1834b4251024990c882c3f51ca0df46ca3301740ac053427e12908743dc1b90d185c42ba14108583c81b20a803a01a80ce065030016c09a03801a00c805c02901400940460130070024010007002000c004001⟩⟩
theorem candidate08058_checked : Checked candidate08058 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19573374091520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08059 : Description := ⟨85, ⟨13, 0x290b4408f9c7862530cb825bf7dea8ed76f1b6a5afed3d6962e7163aaff529a8ed3dc97543ba11cff475037e9b4cd3266732b1818b785a128813d092642b20b0ec072837d1b28d306602e815a8a6850625210e87b83721a30b885042160f206c82a00e806a030016c09a03c01c00d006402e01480a004a02300d006002600e0060024010007002000c004001⟩⟩
theorem candidate08059_checked : Checked candidate08059 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19573382479872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08060 : Description := ⟨92, ⟨13, 0x1540a3e50be3ab11186242120b100a7ee3d79e84f26770b991c90e2c6e7b72db5ed6b69cb4c96169f54b8a49d21287e42fa004f0876537e1ba0da06983299818b7859e28993d092c4191fd0e446fa3651968ba05622a813f895447822b10107c43b01c70d306142e815b0a504a42100ef06b02a012608f04682140e006c03500c805e02d014008c03c01d00e00680300130070024010007⟩⟩
theorem candidate08060_checked : Checked candidate08060 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19573910798976 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08061 : Description := ⟨83, ⟨13, 0xc2a583e9793358ef47062af14e7abbccddaee9e72eb8f9ba4da56c7b5e5abac665e72c05522a6846ea1d508e7fa3e41decd9e69c3439834b4c52128593bc98649322e909c8224001ca0df86c835119a8c6053e21d0dc86882e213c09284341b609304001f80ec05f02d815408e03d01c00a404e025011808003a01200780380140080018008002000⟩⟩
theorem candidate08061_checked : Checked candidate08061 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19586219016448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08062 : Description := ⟨85, ⟨13, 0x2c1f4a7a17d0066e53468ebc59a276fb37ae3d01e46e516d2b5b5ac4d4662fac21506a674faa70110285d4009f20f0e6fc3679a60d0466b3299818b5258a29114649e04c6216103872237e1b20d346763161810a8850621a0eb071034818609c849421a0d805b024c11e07503801840be05802a812008c033013808c03a01c00d006002400a004000c004000⟩⟩
theorem candidate08062_checked : Checked candidate08062 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19586739079296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08063 : Description := ⟨82, ⟨13, 0x546287f2d895dc6fe1c50d1825bd95e92f3876d3a85ce0e5a71cb781b44d8f6bcb4ad7f6ad14f5a380ff07cb3be9d34dfc6cc34e1954c1a5a6290942c9f448e23c11788644161fa8e506a23351730a684a42220f606e431417009e04981e60db05102000e806e02e015808e04201c00d805c025012008003c0120078034012008002000c002000⟩⟩
theorem candidate08063_checked : Checked candidate08063 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19587358294272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08064 : Description := ⟨94, ⟨13, 0x5f12db5518a5e50fe5b12bb91fc77a29d0d18583d91eaef3476d3a85cdee5d71db781b44d796aeb4ad7f6b01568a9a13d69da47022690ea8653fc1f2cef674d37f1b30d3868732a9834b4c52128593e891c47822f10447923941bf0cd46302e615d8a7c4fc2220f6073c3721a20c505c0278125079836c10006e03281780ac04702100f4070036012808003c0120078034014009004000c002000⟩⟩
theorem candidate08064_checked : Checked candidate08064 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19587754656000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08065 : Description := ⟨90, ⟨13, 0x545694f42da004dca5c523f8d5459a2770d37d9bd71d94e51711b759b48d6d6b134b5804be55b4aa0d4cea564fc26fd1028623fb1f24f0e7073671a60d0466c3291818b5258a291146495a49c23d90b081c3fa1e48e706c634d19d8c585d22a214188683ac1c40d205b427212507a036016c09d04781d40c205f02c0158090033013808803c01c00d006002400a004800c004000⟩⟩
theorem candidate08065_checked : Checked candidate08065 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19587779266688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08066 : Description := ⟨79, ⟨13, 0xa95530e927164897c32209cfe77b13d31e76ed4739b8d9b0ed5a6a134a551ca594f925e122288c43b2194ffc79d3b01ac4d0866c3299688ae448f1cb0cc86323011740a704a421f10386ec314171093028c12e09104801fc0dc05f02e01580aa05402380d804e02400f007403801900a004802000f004802000e0040018008002000⟩⟩
theorem candidate08066_checked : Checked candidate08066 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19588679008512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08067 : Description := ⟨80, ⟨13, 0x14cfa4d459225f0c87f3bd31da8d5a6a134a5926ae954129493e4975488a23d0ec8623ff1e68ec66b434219b0ca660a2d115c8a484f724790bc7f03961a48cc86323011740a704a421f10386ec31417109302440fe06e02f81700ac05502a012008e03c01b00d404e02400f007403801900a004802000f004802000e0040018008002000⟩⟩
theorem candidate08067_checked : Checked candidate08067 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19588687396864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08068 : Description := ⟨81, ⟨13, 0x2db54cea5ad25e86723f8acc4b1f96f647abbcd1daee6f71db631ab0d42694ac154d49f246ea2690ea8653fd1e00e0269d34119b0ca660d2d31484a164fa2498f246fc3011740aec53e27e10e873c3721a20c505c424a09104001b80d606502f81780ac05502a011c06c033014809c04a01e00e807002400f00500240100070018008002000⟩⟩
theorem candidate08068_checked : Checked candidate08068 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19589079531776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08069 : Description := ⟨84, ⟨13, 0x136f8b1c52a2590c87b7bd59e70ed46aab509a52c935b4ac15506a6a52b27c92ea911447a1d90c47fe39a1ba4cd865331e9628ae454029194289e648f21710547f43961a58cc862e3011740adc53c28310f87503761a00c505c424609104701b80be05602a815009004701b00cc04e02400f807803a01c00c005002401100800240100070018008002000⟩⟩
theorem candidate08069_checked : Checked candidate08069 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19589090000896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08070 : Description := ⟨95, ⟨13, 0xa965316923401952476e2c3145899432212d04e7f3bdb5ea2f3076a3a79cd0e416dfb695b0ed5b6a0b4a579cb05545a9bd4b89f24e025e122289743da168ffc7c83c91dacdd26cf3589a14cd66532d115c8a184dc24791748263961bf0d9066431a1800ba053825210f881c3761a30b88434142099048017c0b605702a815004e02300f807403801900a004802000e005002000e0040018008002000⟩⟩
theorem candidate08070_checked : Checked candidate08070 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19590759383296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08071 : Description := ⟨96, ⟨13, 0x14cca4ed0065491db8b0c5162650c884b3f9dea2ed474f36fdb4ad5b6a0b4a592cbce582abad508a6f52827c9380975488a2510f685d3ff1f20f2a7683749b3cd68685335994cc145a22b914a4a184f226e123c8ba42a2098ff472c37e1b20d2466431a1800ba053825210f881c3761a30b884340be05b02b81540a804601f00d404e02300f807403801900a004802000e005002000e0040018008002000⟩⟩
theorem candidate08071_checked : Checked candidate08071 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19590767771648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08072 : Description := ⟨88, ⟨13, 0x152ca60524680333c8edc55a2650967d9bdc1ea0f3074f39d9cace416ebb695b0ed586a0b4a58ccb0554029713808dd44d21e90b47c83d01e00ed67013679ac4d0466b3299688ae450d26191748263961bf0d906002e814d89ac3781a20b884fc24a10d05b828412006b030817c0b605502a00cc052027011807403801900a004801e00e005002000e0050018008002000⟩⟩
theorem candidate08072_checked : Checked candidate08072 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595052253440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08073 : Description := ⟨87, ⟨13, 0xa4ed0066791db8ab44ca12cfb37a83a79cacdd76d2b561a82d2962fac155d6a504e023750f485d3e41e00ed07013679ad0d0466b3299828b4457229214349e44c322e90a88263fd1cb0df86c83491800ba053626b0de06882e213f092843416e06b030817c0b605502a012008c03e01a80cc052027011807403801900a004801e00e005002000e0050018008002000⟩⟩
theorem candidate08073_checked : Checked candidate08073 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595060641792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08074 : Description := ⟨84, ⟨13, 0x14cea59500666b1de8acc259f96f6474f39bdcbadd26d2b631ab0d41694b199602a6c4e0237513487a42d1f20ef66cf34f1a08cd66533069698a424ef26191748223941bf0d906002e815d8a7c4fc21d0e786882e213c092843414209304001f80d606502f81780b605502a00f4070033014809c04602000e807002400f00700280100070018008002000⟩⟩
theorem candidate08074_checked : Checked candidate08074 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595320656128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08075 : Description := ⟨82, ⟨13, 0x533a80333c8ebc50a12cf707983a79baada56ac3505a52c5f580aa0d4d89c047aa238f9079937f9b3cd6c682335994cc145a22b91490a1a4f226191746fc3641998c005d02b8140887c3a41a20b884f824a10d05081d40e006b02f816c0aa054024011807a03801980b404e026011807403801900a004801e00e00580280100070018008002000⟩⟩
theorem candidate08075_checked : Checked candidate08075 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595324882944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08076 : Description := ⟨85, ⟨13, 0x2d4f549a00c58e28f0967b7bccdd3ce5c6eab695aaad41694b17d602a8353627012ea911447a17505c7c83be1bfcdd26cf335994cc7a58a2b9148ca1e45d21710406c834b1998c5c6002e815b8a7850621f0ea06802e213e091843411c07e038017c0b605502a012008c03d01c00cc04e024011807c03a01c00c0050024011007002c0100070018008002000⟩⟩
theorem candidate08076_checked : Checked candidate08076 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595331125248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08077 : Description := ⟨86, ⟨13, 0x607aa8d4c4a4e50122c71278494205f9af617a9bcc9d44e7272cb8f5baeda36c63555a7ed296332c154449bc486a2310f08683e61df8e026e936699a4ca6572297943c9de45d20a8e5862e2e815f0a645121ed0e786f03401890b884fc24610c05182380fc06e03501840bc05502a00d806603201700a404801f00e807002801200700240100070028008002000⟩⟩
theorem candidate08077_checked : Checked candidate08077 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19595520917760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08078 : Description := ⟨92, ⟨13, 0x1626a8ad33a965497a19500257723f8acc4b212afcb7b23cd1dd6e9f737b975c76ddd6d23631ab0d426942ffd5a8a6c4f8a6fd1ba89a43d2194ff67c93bd9d34e006ce34f1a08cd86523069698a424fa23c11788223c91cc8d8c6022e715d8a7c4fc21d0e7868831413c09283d010006b032817c0bc05a02b015007a033014809c04402000f007002400f00680280120070018008002000⟩⟩
theorem candidate08078_checked : Checked candidate08078 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19596360843520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08079 : Description := ⟨91, ⟨13, 0xb13533a92f40096ac6aa2850c784abdc1e76e9f6ed3691ab0d426942ffd7cab6956a2a0d4d8a564f8a6fd1ea88e42f2054f927993b29c10d9c6b634119b0ca460a2d115c8a4850d27b92408f045e1f10f2472a3631998c045ce2b8140887c3a41a20c504f824a0f403a81ac0be05a02b015009003d01980b404e026011007803801900a004801e00d00580280120070018008002000⟩⟩
theorem candidate08079_checked : Checked candidate08079 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19596365070336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08080 : Description := ⟨86, ⟨13, 0x583294f42d9714aaa4df13b869becdeb8f237653a61ca2e3e6eb35b5ac4d46696b18d804a85533a9553f08813fb1e1ced070734c1a08cd665230316a4b1451926312708f645a2070fe473833b18b0c085d22a214188683881a40c305b42ae13909284341e80d805b027413608f03b01d40c205f02c010007c033013808c04401c00d006002400c005000c004000⟩⟩
theorem candidate08080_checked : Checked candidate08080 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19602341890176 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08081 : Description := ⟨90, ⟨13, 0x5a92b554639fc4b563b70ad84741edecef4e79d3b4dd50e6d72a3901bb2dae69e34993568e044b21f50be7fd3e31e70f067653819b30cfe6503201630a5651227b12408b843120c0ff072c36218a0bf859e2af14b0a0043c1f00ea86f033a1870b8056027e12008503cc15e08e04681ac0d206703301700ae05402000d8064031016808c03c01c00a00340100070030014002000⟩⟩
theorem candidate08081_checked : Checked candidate08081 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19611626512448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08082 : Description := ⟨89, ⟨13, 0x2bc152ca65d2ca92d40199cc77a38315b895c259f96f6979aba79cd4e5d71d37c5ba4da56c6b561a82d29580a9b13808dd43d1f20f4077b3b59b3cd3c682335994cc1a5a6261917484e4112000e506fc3641800ba057629f13f08743441710a904f024a10d04981d80d606502f816c0b205502a00f4070033014809c04602000e807002400f00700280100070018008002000⟩⟩
theorem candidate08082_checked : Checked candidate08082 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19611963654400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08083 : Description := ⟨95, ⟨13, 0xb5254b2991496a00c51212d04e7f3bc11d3ce7372bb905baada56ad3505a52c635ce2bad50ea6e52aa7012e291147aa2450be82e3e41e58f0276438d9bfcd9e6b734219acca660a2d115c8a1a4c322e90bc8243fd1b20ccc6323001740acc538281129087c40e1710aa84f824c10d038017c0b805b02a815007002f016809c048023010807403801900a004801e00e005802000e0040018008002000⟩⟩
theorem candidate08083_checked : Checked candidate08083 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612100001792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08084 : Description := ⟨98, ⟨13, 0x50066732728e0c57628912b84b412dfcef0474f39c1caee3e6eab695ab4d41694b18d738aeb543a9b94aa9c04baa44505c7c83cd1e04ed06ff3679a10cd665331d1818b4458a2b91498a1a4f4261917488c42b2090fe47603641a60ccc6323001740ad4538283129087c40e1710ab84f824c10d038017c0b805b02a8150070027012008c03a01c00d0064030014009003c01c00c005802000e0040018008002000⟩⟩
theorem candidate08084_checked : Checked candidate08084 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612108324864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08085 : Description := ⟨92, ⟨13, 0x152ca65d25a8031db84b3ecdea0e9e73b3959c82dd76d2b561a82d29631ac155d6a8552aa7013508f546ea24d0f485f3e41e50f0076438d9c04d9e6b734119acca660a2d115c8a1a4c322e90a88263fd1cb0df86c83001740ae053628113586f03441710aa84fc24a10d03581840be05b02a815007c03301680a404e023010807403801900a004801e00e005002000e0050018008002000⟩⟩
theorem candidate08085_checked : Checked candidate08085 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612232122368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08086 : Description := ⟨91, ⟨13, 0xa00cce63b71c18adc4ae12cfb37a83a79cace3e6ebb695ab0d41694b18d60aaeb542a9553808dd43d1f20f007683809b3cd0466b32998e8c0c5a22c515c8a4c50d27a130c8ba4131fc8ec072c37e1b20d306002e814d8a0c4d61bc0d105c42ae13f09284340ec06b030817c0b605502a00f8066029013808c03a01c00d0064030014009003c01c00c005002000e0050018008002000⟩⟩
theorem candidate08086_checked : Checked candidate08086 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612240445440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08087 : Description := ⟨86, ⟨13, 0x50066731d78a14259f96f6979aba79cdedd56d2b561a82d29631ac054d89c047aa24d0be7c83cc9bfcd9e682335994cc746062d11628ae452628693d098645d2160df86c83331800ba056823910f87543441710ac04f824a10d03a81c00d606502f816c0aa05401e80e006602d013808c03a01c00d0064030014009003c01c00b005002000e0060018008002000⟩⟩
theorem candidate08087_checked : Checked candidate08087 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612504686592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08088 : Description := ⟨92, ⟨13, 0x1546a02424a102fcd7b63d4de6eea27393965c7add76d1b555a7ed29631ada560aa224de269521a8f7448a1e10c27cc3cb9df8ece7013749b34cd265331e9628ae452828793d08ba42e20a8fe872c3171740b3c56429914108e43da1d50de06803121710ac04fc24610c04701b80d406102a815006c03301900bc05c029012007c03a01c00c005002400e004802000e0060028008002000⟩⟩
theorem candidate08088_checked : Checked candidate08088 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612700786688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08089 : Description := ⟨94, ⟨13, 0x50066731db84b41f9f96fb37b4bd41e6ae9e737b959baeda56ac3505a52c63582a7013508f546ea24d0f485f3e41e64f007013679a08cd665331d1818b4458a2b91498a1a4f426191748584131cb0df86c83001740b3c56829b13588e43aa1bc0d105c42b013f09284340d6065030817c0b605502a00cc05a029013808c03a01c00d0064030014009003c01c00a004001c00c0050018008002000⟩⟩
theorem candidate08089_checked : Checked candidate08089 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19612768927744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08090 : Description := ⟨86, ⟨13, 0x593666b2d8892c38a1a3097825bfa9eb4f0776ebaf1d46e7072d38e5ba4da66332fed4bea3e4f5a70521a87442520c4fee7e63e69df4e9a6d03069698a4250b277930c91c47822f90c882c3f51ca0d946a233517f8b9853425210e881c3dc1be0d086202de13c093024c10007e03a01580aa04702100e005c029010007803a00f0070034012008002000c004000⟩⟩
theorem candidate08090_checked : Checked candidate08090 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19619570286848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08091 : Description := ⟨87, ⟨13, 0xbe252f28ff42ca014dca68d2e291fc75deb8f40791bb29d4ce51711b6998bec025b4ac214f0a254fda76938288142e9fd8f9478737e1b40d466873351944c0c5a929114649e04c625692708f646221610387f43c91c88df86ca2a214188683dc1d60e2069030c16d09c849413a09303a81c00c205802b0154090046011808803c01d00d0060014009004000c004000⟩⟩
theorem candidate08091_checked : Checked candidate08091 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19619974744192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08092 : Description := ⟨88, ⟨13, 0x15a6a4851368052428edc4d612f04e7f3bdb5ea2f30767ba81cd0e3670536fdb4cd926a0349d6d8b0552fa7052f091144ba1ed0b47f93e51e48ec07343749b40d7866a3289688a184dc22f904c7923961bf0d945fe2e614e094843e2070f706ec3460db050826412e07a02d81680ae05602a810804602200f807803a01900a004001c00d00500240100040018008002000⟩⟩
theorem candidate08092_checked : Checked candidate08092 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19623995048192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08093 : Description := ⟨89, ⟨13, 0x2b5b4a0a01490a3b713584bbf9dea2ecf7503829b7eda66a0349d92cb65582a93d4189c14baa44512887b42e9fe4f947953b19cd0dd26d035c99a8ca260a2d114a4a184f226e117c8544131fc0f2472c37e1b28d385fe2e614e094843e2070f706ec3460db03d016c0b405702b015408c04201f00f004602200f807803a01900a004001c00d00500240100040018008002000⟩⟩
theorem candidate08093_checked : Checked candidate08093 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19624003436544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08094 : Description := ⟨92, ⟨13, 0x13ff91fc76e2690d084d412dfcef4076e3a99c14dbf6d334eda44c965b4ac15510a6f528a7b537c975488a2510f685d3fc9f28e686e93681a14c746062d1150c9e04df25692308c442c2098fe87923961bf0d9469a33417e8b9056a29c141894843e2070f7075837a1860b6836011a08c02b81580aa04602100c8062023011007c03c01d00e006803201800a0028012008002000c004000⟩⟩
theorem candidate08094_checked : Checked candidate08094 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19624523466752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08095 : Description := ⟨97, ⟨13, 0x30514d5a48513680533c96ac90a3b716789ac3ee1610977b83d41e60ed175039d9cace366ebb699b24d5d6a0349d8ccbff5b62c15522a5f512a76938289a43d2168ff67ca3d01e00ec07013681af0d0e66a3289688a1a4c324811e08be4131e48e586fc36518c0bfc5cc29b13587b83781a209f84941b60a104b81840b605a02b0154052023011007803a01900a003c01c00d00500240100050018008002000⟩⟩
theorem candidate08095_checked : Checked candidate08095 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628287918336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08096 : Description := ⟨97, ⟨13, 0x30514a0a014cf25ab2428edc59e26b0fb858425dea0ed17503959baeda66aeb501a4ec5f5ffad9560aa81527a8954189da4e0a1e90ba7fb3e51e00ec67013681ae4d0e66a3289828b4452428693c898649023c117c8544131fc0f2472c37e1b28d386302ff1730a6c4d61ee0de068827e12506d81840b605a02b015409004601f00f0052023011007803a01900a003c01c00d00500240100050018008002000⟩⟩
theorem candidate08096_checked : Checked candidate08096 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628296306688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08097 : Description := ⟨90, ⟨13, 0x5ac69a948da2850166792d58b2449212904e7f1bdcde82f0775e3a8dce6e366ebb699b2ad5c69f34958ccbff547293937c978486a2750d68313f31f34f3a7603809b40d7e686334193cb4450d26192408f045f1cb0d9463226b129081c3dc1a10c405bc27e12606d02d412e06a03481980c205602a80c806202e014807803a01900a003c01c00d004802000e005002000c004000⟩⟩
theorem candidate08097_checked : Checked candidate08097 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628403523840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08098 : Description := ⟨87, ⟨13, 0xa014cd647f1de87dc2c212ef64775ba81cdee5d71db749b4cd5d6a0349d8ccbff580a8953b49c144d21e90b47fb3e51dece9a6d034399a8ca260d2d314849de4c323c117c8223c91ca0df86ca31817f8b9857629f13f08743dc1cf0d104f024a0db050824c10007e03281780b605a02b015407a038014808c04402000f007401e00e00680280120080018008002000⟩⟩
theorem candidate08098_checked : Checked candidate08098 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628556321024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate08099 : Description := ⟨86, ⟨13, 0x500a6792d58ebc3ee1610977b83cc1d40dd56d33575a80d2762faffd6d2b01512a76938288e40a9f28f3276537f9b40d0e66a3289828b4452428693c898649023c117c7c43c91bf0d946302ff1730ae050221f0f7074834413e092836c142075038016c0b405602a812008c03d01c00b404c023011007803a01900a003c01c00d00580280120080018008002000⟩⟩
theorem candidate08099_checked : Checked candidate08099 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 19628560547840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate08099_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch080

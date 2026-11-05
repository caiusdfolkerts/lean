module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch012
open Papers.RationalityTen GraphCandidateCoverage

def candidate01200 : Description := ⟨62, ⟨13, 0x50c63e915e86e3f39e70f2277438a1c18d6e5a8a7c108a7fc3a59cd8e046022e11640a584fa26f12907c83c71bf0cc063426812887b837218a09e049421a08f04602240f606902d01540a803401880b004a022010007403801600680280100070018008002000⟩⟩
theorem candidate01200_checked : Checked candidate01200 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22237807673600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01201 : Description := ⟨61, ⟨13, 0x28930c6821c00dfa2f1f739b905c4adeb6b8a7c12da92d47da124f3a76b3a79c54d365ef26d12447c0397135081c3dc1bb0d1862827c12608682b012808c03601a40c605a02a8150068031015808803a01c00b805802000d005802000e0040018008002000⟩⟩
theorem candidate01201_checked : Checked candidate01201 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22254578630912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01202 : Description := ⟨65, ⟨13, 0x28631c288b4111ff8eea71eb8adc16df06b728e53e097e4aea4b4ff874939a9c08c045c22c813787be3c81b28cc06022b014489b44a023310386e434613c093043011e08c04481a40ce06202d01540a803b01a00c404a022010007403801600680240100070020008002000⟩⟩
theorem candidate01202_checked : Checked candidate01202 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22255045214464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01203 : Description := ⟨64, ⟨13, 0x10c6821c00dfa2f1f712b5c53e092647a212502874f38d1a6cc0a5ef2df96349b44911f00e5c56628113508d840e1ee0dd868c31413e093043415808c03601a40c605a02a81500a203401880bc05a02b015008803a01c00b805802000d005802000e0040018008002000⟩⟩
theorem candidate01203_checked : Checked candidate01203 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22255115501568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01204 : Description := ⟨65, ⟨13, 0x218d0468003f39e3ee256b8a7c12e092a47c2124e9e69b31097bcb7658926d12a49223e01d78e5c56a28313508e040e1ee0dd868c31413e093043411808903601a40c605a02a81500a203401880ac04401d00e006803001700b005402000d005802000e0040018008002000⟩⟩
theorem candidate01204_checked : Checked candidate01204 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22255123824640 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01205 : Description := ⟨62, ⟨12, 0xf1edd7db9d29cafc5da88a2395d90f89484882f7016856536216045be57055b4db42e3cb39637b34b3002e82b72692542041d41bc18917113f12309207e06105505405104603702902801f01d01c01801701401100e008007005002001000⟩⟩
theorem candidate01205_checked : Checked candidate01205 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22314310713344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01206 : Description := ⟨69, ⟨13, 0x2b4141991b444e0af002767b99dc70e126e23635a50caf5b0a8f53b097e3fc9f88f2476e3981b9cd0a65230815c0ab64da21a8fd47c23c61c00cc86022e715f0a244a821f10206ec2a412308603d018009903d01d00b405902a0108074028011007c03801700a004001a0090038008002000⟩⟩
theorem candidate01206_checked : Checked candidate01206 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22323399770368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01207 : Description := ⟨64, ⟨13, 0x15b5a64431dd66e446ed34a195eb805b1aa1d4489f14b7249d1227963b11cd4e086b73421948ae055b26292408ea3f81ca8ccc6022e7143095043e2040d0055427c10c07a02700e605a02a014408203c01d80bc050024011008403801700a00340160090038008002000⟩⟩
theorem candidate01207_checked : Checked candidate01207 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22327560585216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01208 : Description := ⟨65, ⟨13, 0x299141f862bc25d82e41712b49995eb8358eaa1d3de9d4448a0b0fbe7963b21d3cdd46b73421940ae055b26292408ea3fd1f00ccc50226a127882434018a0b8055427c10d07982b00e006902a014408203801880bc05a02b012008403801700a0034016008003800c002000⟩⟩
theorem candidate01208_checked : Checked candidate01208 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22327593615360 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01209 : Description := ⟨67, ⟨13, 0x832c15ded8ed37393765aaad265d9aae53ae98f4b725751227fd3cb9c0cca06213021628a504c5248117885c3cb1cb0d9062e2cf1590a084d225410f07543781a00b8056027e123079823810606902a014409603301880bc04801f00e006002e01400900340100070030014002000⟩⟩
theorem candidate01209_checked : Checked candidate01209 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22362621231104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01210 : Description := ⟨64, ⟨13, 0x142e91c456a1befb879c3c89d98e3e70636296e4a8b4f6a36d08a7363809a74c0457429613e89bc48e213900078e37e1a30c684d025110e87b837218a092843413a08c04481d80da06902d01540a804201880b0052025011007403801600680280100070018008002000⟩⟩
theorem candidate01210_checked : Checked candidate01210 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22374978191616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01211 : Description := ⟨69, ⟨13, 0x2b6d248861c145f6af1f767b9d9c82e0c5b127b52de8df4249fe4f2876439b1c6cd6e6052f795c09b442a1fe8f1c72c37e1990c68570281135094443e1ee0dd86282aa12508682300f406902d01540a805102100f806202d011008403a01c00b805802801000680280100070018008002000⟩⟩
theorem candidate01211_checked : Checked candidate01211 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22392153899008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01212 : Description := ⟨65, ⟨13, 0x215b06b7e13b79bc8d204eba6312de8db449a0c0ff679939b1c04d046212f795c0a4c4c124811e08583c71cb0df85a427f13308f04361f10ec06fc31a16c0ad85082200ef06b023011206b034814406603101680b005202200e807003401800b805802800f0068028010007⟩⟩
theorem candidate01212_checked : Checked candidate01212 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22396981477888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01213 : Description := ⟨70, ⟨13, 0x50727452a28cb41960aee726e3b5cda4ccc25e62ad13ac98f4b72574fc87973729a74d0a6503109810b7c58a2b895589b449122f10b879637b1b20cc859e2b214109a44a82090ea85c02b013f09183cc0d205d02a014409403701880bc04a01f00e006002e01200800340100070030014002000⟩⟩
theorem candidate01213_checked : Checked candidate01213 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22427045740544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01214 : Description := ⟨61, ⟨13, 0x28632ed8f9c37df38f3879138f9c50d8a6b727c118c8453fe1d2ce046022ab94b09f44de23b90c88003e41be8d1866026812888183dc1b90c504f021a08f04602240da06902d01540a803401880b004a022010007403801600980340100070018008002000⟩⟩
theorem candidate01214_checked : Checked candidate01214 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22443563450624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01215 : Description := ⟨67, ⟨13, 0x9dbc015e3cebe7123711aaad3f670b18d6d2a22492a43d0907e13a71b9ccd26212eb16e4b1257029413d09b647a2170fe87c238018b8adc4d223810206f03401890b884fc24610c07a02380d406102a013806603201480a004801f00e006002e01500a00380120070028008002000⟩⟩
theorem candidate01215_checked : Checked candidate01215 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22602039967744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01216 : Description := ⟨80, ⟨13, 0x152d8d4c44e19104e801bf45f6af1f76a3699ab4d42694b3855d8ad351ea7c92e292647a237d1228493ff1d94e346d034219b0ca660a2df9634ae050e26d123c7c23961b28cc86323011740acc50226a12908d843e2070f706ec31417109301700ac05502a00bc05a02a012007803a01c00b805002000f004802000e0040018008002000⟩⟩
theorem candidate01216_checked : Checked candidate01216 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22664412463104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01217 : Description := ⟨83, ⟨13, 0x9dbc70a353113864412e000fce7dabc7dda8da66ad3509a52ce15762b4d47a9f24baa4a91f08df4249ff8da0684336194cc426062eb16ecb1257029314389b448f1fd0f8475e3961b28cc86323011740ad450626a12908e043e2070f706ec31417109301700ac05502a009003c01d00e006803001700a805002000f004802000e0040018008002000⟩⟩
theorem candidate01217_checked : Checked candidate01217 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22664420786176 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01218 : Description := ⟨75, ⟨13, 0xaafc32209d0037e8bed5e34ed46dfb56da82d29670ac793e497149323d11be85f4221ff8f2e71a3749a14cd665330516fcb1a5702478e586fc33218d0c005d02b314089a84a423610f881c3dc1bb0d185c421a07d02d815c0aa05402280bc05a02a011807c03a01c00b805002000e005002000e0040018008002000⟩⟩
theorem candidate01218_checked : Checked candidate01218 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22666492837888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01219 : Description := ⟨78, ⟨13, 0x4ede3e90c8825c001f9cfb578d3b51b7ed5b6a0b4a59c2b1e4f925d52548f846fa110ffc6e934299acca66213031758b765892b813d091e42c1d78e586fc33218d0c005d02b514189a84a423810f881c3dc1bb0d185c421a07d02d815c0aa054022808c03e01d00e006803001700a805002000e005002000e0040018008002000⟩⟩
theorem candidate01219_checked : Checked candidate01219 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22666501160960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01220 : Description := ⟨66, ⟨13, 0x599699d3a097bc019f8cfb27b83cedde0ebb710b705ae8d5866530852608f046e22690ca81a3f29d2cdd669e34115c4ab247620a0f806f833311008183781a20c505c424a10d07a029c0d606402f81600a8033016009c04001c00b804c02400f005802800e0050018008002000⟩⟩
theorem candidate01220_checked : Checked candidate01220 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22689878180096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01221 : Description := ⟨66, ⟨13, 0x4e825eefb275db885b82d746ac330d822a83479a3710c48173f29d2cdd669e3411828b745882b89564a484f725611d88283e01be0ccc4402060de068831417109284341e806b032017c0b00540270130090033016009c04001c00b804c02400f005802800e0050018008002000⟩⟩
theorem candidate01221_checked : Checked candidate01221 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22689886568448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01222 : Description := ⟨66, ⟨13, 0x4e65ff4f697913aedcdee286e0b5b9ab0cca536a4c11e08dc4229f94e966eb3411834b6e5852ac93788ec3e41be0cc057627e13408cc40c1b90d106282e213c09284341e80a7047821810806b03281880be05401a00cc0580270128080038013009003c0140070018008002000⟩⟩
theorem candidate01222_checked : Checked candidate01222 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22698468081920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01223 : Description := ⟨69, ⟨13, 0x27411438033f19e3eebb712b705ae2d58661a9b52488934249f94f3274f3759a6cd0460a2dd1620ae255928713688ec4141f00df057028113508d840c1bb0d106282e213e09284341e80a703601ac0be054027013006803301680a804e01c00b804c024010007802c0140070018008002000⟩⟩
theorem candidate01223_checked : Checked candidate01223 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22698472308736 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01224 : Description := ⟨67, ⟨13, 0xb85c015f92f1f75f3895b88d716aab30d4da975492a3cd1888493f09d3cdce69b31096e4ae252826d11e885c3e01c00c5c56e28313508e04081bb0d006282e213e09184341e808e04201b00be0540270130068033014009c04801f00e006002e01500900400160070018008002000⟩⟩
theorem candidate01224_checked : Checked candidate01224 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22698478551040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01225 : Description := ⟨69, ⟨13, 0x22270057da3af9c48dc46d435cdaaacc35b4aaed47a92546f21e4fc274e3739b48d3a6212dc95c4a504da23d10b87f43e11c00d8c6643171808adc4d223811008103da1a00b884fc24610c07a023810805d02a0138098033014009404801f00e006002e01500900400120070028008002000⟩⟩
theorem candidate01225_checked : Checked candidate01225 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22698676731904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01226 : Description := ⟨65, ⟨13, 0x28f11ef8af44661c2fce799bc5dddae286de35b9a82d2951b9d2ce046e6335994cc1a5b72c814b09de4d92578f9066031a1800ba04d02060f706e42e213c092843414008f04301f80de05b02a815008a03701a00b004a023010007403801300700280100070018008002000⟩⟩
theorem candidate01226_checked : Checked candidate01226 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22717770268928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01227 : Description := ⟨71, ⟨13, 0xa13c7162270b278dbaf9b94da96b33515a58b655742a1547a9d54baa4951f08794229f84e6e6e43699a00cde6562c693688f43f81f08eb46f63651990c5c6022e811008103dc1a00c505c425010b079036417a06402e813807c03c01c80dc06602c01400940480170080024010007002800c004001⟩⟩
theorem candidate01227_checked : Checked candidate01227 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22732465192960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01228 : Description := ⟨70, ⟨13, 0x521221b04e7fc3f45e34e256df35c5a82d2951ba5c51e885f4221d3ce346e834d99acca660a2dd16347c03971be8c005d02b314089a84a42360f706ec34617109f049821a0a903e81b00c005b02a815009c04501a00bc05a02a014008c03a01c00b804c02000e005802000e0040018008002000⟩⟩
theorem candidate01228_checked : Checked candidate01228 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22735078096896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01229 : Description := ⟨71, ⟨13, 0xa424436096ffb7e73c69c4adbe6b8b505a52a374baa4951f08443a79ba0d3666b3299884c0c58927a0f8075e3971be8c005d02b514189a84a42380f706ec34617109f049821a08603e81b00c005b02a815009c04501a00a004601d00e006803001700a804c02000e005802000e0040018008002000⟩⟩
theorem candidate01229_checked : Checked candidate01229 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22735086419968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01230 : Description := ⟨65, ⟨13, 0x2a271f48acc385f92f387913bb5c50da56b73561a52ad2536a37108a74b3811b3cd046533069708b0a52127d137895e3e41bf0d906602e813406e434418a0b884f024a10d047821010006b02f81540a803401980b004e025010007403801200780280100070018008002000⟩⟩
theorem candidate01230_checked : Checked candidate01230 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22749982523648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01231 : Description := ⟨72, ⟨13, 0x15628fbc72212cfb478cba89b7ed736adb4a5634ae652aa7012548de4219f30f2a7183749a74d0a65330516fcb1057122e90a87fa3ad1bf0d9066431a1800ba053a269110081c3da1a30c485c427e07d02e815c0aa054026011407c039012807c03a01c00b804802000e005002000e0050020008002000⟩⟩
theorem candidate01231_checked : Checked candidate01231 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22769040424960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01232 : Description := ⟨73, ⟨13, 0x2abf1f488cc259ff8fc879bbc95d44e6d6f836fdadcd5b694ab4946e9c0496a3f91bc8433e61dfce046e9342994cc1a5c22c293648ba3e41bf0d9066031a1800ba056028913688cc40e1ed0dc868c31217109e023c108067031015c0aa05402280d004a02000f807403801200700280100070020008002000⟩⟩
theorem candidate01232_checked : Checked candidate01232 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22769300439296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01233 : Description := ⟨74, ⟨13, 0x52128031f48003f4de48ea56dfb5c5ab6d2958f2b4946e9c04baa4a91e68443e41d3cdd26cf34d9a14cd665331216ecb0e57327b13608c242c20a0ebc72e37e18d0ba056a28513608e040e1eb0dd868c30e17109f01b00ae05502a013008a034013808c03e01d00e006802a01000580280100070020008002000⟩⟩
theorem candidate01233_checked : Checked candidate01233 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22769311948800 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01234 : Description := ⟨67, ⟨13, 0xa25ca8a09d0037e33c7dd3ee68720b895becd716adb4a1798978496a3c10927c93c91dace9e72034d9a14ca457126d12448bc4141f00c685ce26a129081c3761a30c504f821a0f405382640d805f02d015c0a8034013808803e01c00b804802000d005802800e0040018008002000⟩⟩
theorem candidate01234_checked : Checked candidate01234 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22769874043136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01235 : Description := ⟨68, ⟨13, 0x12a278fba7dc4ad716adb4a1798b8350525d52548f34249f24f2a7683a79c74d366853291828b7e5882b8936892245e21510507fa3e01d90c685ce26a129081c3761a30c504f821a0f4036017c0b405702a013007c034013808803e01c00b804802000d005802800e0040018008002000⟩⟩
theorem candidate01235_checked : Checked candidate01235 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22769882431488 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01236 : Description := ⟨76, ⟨13, 0x12a2921472e2270957da3b49c48da86b9b56da50bcc5b2ab9547aa0a4dfa4a91bc7fc3ca9d38e3a6d234e9a14ca460a2df9620ae24da24891788543f81f08f247643631990c686022e714e89a44402070f6868c27e10c07a01740b405702a013007c03c012808803e01c00b804802000d005002400e0050020008002000⟩⟩
theorem candidate01236_checked : Checked candidate01236 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22770080612352 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01237 : Description := ⟨70, ⟨13, 0x48fe22d0957fe3f21dd4e6d71eb8adb50d6e6adb4a1798a394dfa4b51fc8de3fe1dfce926d23429948c1a5c22c293788bc3df1e48d8c66031a1808b9c56028913688cc40e1ed0dc868c27810c07a023c10806703101680ae05401d80d004a022010007c03801200680280120070020008002000⟩⟩
theorem candidate01237_checked : Checked candidate01237 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22770340626688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01238 : Description := ⟨69, ⟨13, 0x254510f84ac00dfa8da86b8b56da50bcc5b4a8e537e9264792050f2e7673691a6cd0a65230516fcb1057126d12448bc4141e48d8c6343011738acc50c23610387b43761a309f04301e807303601680ae05402600ec06802f015008803e01c00b804802000d00580280120070020008002000⟩⟩
theorem candidate01238_checked : Checked candidate01238 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22770344853504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01239 : Description := ⟨71, ⟨13, 0xa40d002000fd371536adae2d5b6942f316d2a394dfa5d52548f34249f24e947343671a6cd0a66c3291890b765872b992a492242c20a0ff07bc36718d0b9c56a28513608e040e1eb0dd868c27c10a07a01b00b405702a0130076034013808803e01e00e006802a010006802c0140070020008002000⟩⟩
theorem candidate01239_checked : Checked candidate01239 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22770352136192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01240 : Description := ⟨76, ⟨13, 0x12428fbc716226f1b7693835b84da96af3515a48b6558d2ba147aa084baa4a91f08453fe1cdcdd86d334419bcc9c60a2df96349b44912150fe07c23c91d68df86ca33218d0c0453a252110081c3dc1a30c504902160f206c81a40c805d02d00f807803901880b004a02200b804001a00a004802000e005002000c004001⟩⟩
theorem candidate01240_checked : Checked candidate01240 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22804405878784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01241 : Description := ⟨65, ⟨13, 0x29831558943ebdedeebe73ab891b88da86c535556d8abb540296521e8d93f09d38dce6d229793e88f44351fa8f847003631a30c5c60226910207b43781a00b884fc24610c07a02dc11c08303a01b40c205402580cc052028012007c03801700a00480120070028008002000⟩⟩
theorem candidate01241_checked : Checked candidate01241 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22826988880128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01242 : Description := ⟨68, ⟨13, 0x14ce9cec565ffefcb7d6bd91e68ebb737b8a1bbadc16c6356160c89a4329f94e967003759a78d0460d2b79564a424fa23b0f9073237c15d89f84d021d103073c34418a0b884f024a10d07a029810006b032817c0bc05402580cc0580290138080038013009003c0140070018008002000⟩⟩
theorem candidate01242_checked : Checked candidate01242 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22827317100800 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01243 : Description := ⟨71, ⟨13, 0xa674771f60f7079dbaedc4adda6e0b56198eb06541a4a51ea8da4472178fca7993a79c10dd66b63411828b4855929213dc8ec4141f00e546f833315c0a044d421f103074834418a0b884f824a10d07a020c0d605f02a012c090033016809c04c01c00b8050026012007802c0140070018008002000⟩⟩
theorem candidate01243_checked : Checked candidate01243 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22827321327616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01244 : Description := ⟨69, ⟨13, 0x22c6fb07b7bce1d7ce256ed3711aaacc75832a0d2ea8da462223d0c47e13a79c10dce6212df1628a464f323d10b87c03951c00d2c66631715b8a0c4d421f102075034018a0b884f824610d07a023810605f02a012c090033014009c04801f00e006002e01400900440160070018008002000⟩⟩
theorem candidate01244_checked : Checked candidate01244 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22827327569920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01245 : Description := ⟨69, ⟨13, 0x22c712c7d7bdbdd7ce246e236a1aaacc75b4aaed506a56487a36511e7e13a71b9cda46212df1628a464f323d10b87f43e11c00d8c6963171808adc4d22040f687503781a00b884fc24610c07a023810606102a012c09003301480a004801f00e006002e01400900440120070028008002000⟩⟩
theorem candidate01245_checked : Checked candidate01245 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22827525750784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01246 : Description := ⟨68, ⟨13, 0x149da19c7c62b51267dc3ccde2eed771f36f1b14d41694aa2d4b89f246d9fe8e026e634e99acca660d2ba14b09de4d9249909c80034618d0c005d026810e88183dc1b90b8849421a0a003f01d80de06d02d81540a804501b80b0052025011807403801300700280100070018008002000⟩⟩
theorem candidate01246_checked : Checked candidate01246 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22854940786944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01247 : Description := ⟨73, ⟨13, 0x293547e976c8ee2b51288573ee1e70f2276638e5b82d8a6a134a16d8a8b52ca8f53b08db4229d30dd669d3361948c1a57429613e89bc48e23b909c7ea3c91be0d1863430117389a043a2060f706e431412507a02740ec07403681680ac05402100b0052025011007803801300680280120070018008002000⟩⟩
theorem candidate01247_checked : Checked candidate01247 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22855980974336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01248 : Description := ⟨69, ⟨13, 0x29394808d6449dffaf6679938f5c56dd26df3631a7ed29567a8e921e8974342120e926e834f19a4ca660d2ba14b09de3df1ca0df46ca2e81580a244da21d0e7868c31217109e049821809303f01a80ce06002f01540a803b01c00c8052028010007403801300700240100070020008002000⟩⟩
theorem candidate01248_checked : Checked candidate01248 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22863856828672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01249 : Description := ⟨70, ⟨13, 0x444a09cfb57b6bcc1c4add56df3505a52a3c4b8a49d1be8903a79bfcdd06b6335994cc145a42b814a49e44db1f00df46663001740acc50226a129087c3dc1d20d185c427c12608682840e006002d81540a804601c00bc05a028013008c03a01c00b805002600e005802000e0040018008002000⟩⟩
theorem candidate01249_checked : Checked candidate01249 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22863927115776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01250 : Description := ⟨71, ⟨13, 0x889412df6af6a799b895baadbe6a0b4a547897546fa2510ba74f37f9ba0cd66533109818b785a42b814949b63e01be8d2c6663001740ad450626a129087c3dc1d40d185c427c12608681f80e006002d81540a804601c00a004601d00e006803001700a004c02200e005802000e0040018008002000⟩⟩
theorem candidate01250_checked : Checked candidate01250 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22863935438848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01251 : Description := ⟨75, ⟨13, 0xb2c525e18f04e7dabdb5e76eb87103769a84d2860ba9593e2971493a37d12085e40a9f88eca74a3821ad8cd86523051690ae052927b92408ee3951998c045ce2b314089a84a421f0f7074834618a09f04981e807303001680ac05401d80bc05a028013008803c01c00b805002600d005802400e0040018008002000⟩⟩
theorem candidate01251_checked : Checked candidate01251 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22864967303168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01252 : Description := ⟨76, ⟨13, 0x12ed896431e096fb57b53ce1d70e206ed3509a50c1752b27c52ea8df44a2188fc474a38219b0ca462130316f0b4857029293cc95449023b8fe872a34b1998c045ce2b514189a84a421f0f7075034618a09f04981e807303001680ac05401d80a004401e00e006803001700a004c02200d005802400e0040018008002000⟩⟩
theorem candidate01252_checked : Checked candidate01252 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22864975626240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01253 : Description := ⟨72, ⟨13, 0x1561a4b4321f6af1a76a39d9c82dbc6a0b4a5636a554f924a51be85f4221ff8f2876438d9b98d6e66b3299828b4857024790a87fa3961990c686002e815c0a044d421f10307b83761710aa849421a07d037816c0aa05402280f806e02d011808403a01c00b805002601000700280100070018008002000⟩⟩
theorem candidate01253_checked : Checked candidate01253 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22872116494336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01254 : Description := ⟨71, ⟨13, 0xae3d266901432894bff5e6eeb873638e1c56ddd6c6b4fda50bcd51d27c521e8483fd9f88f3a76e3a49c00d3c6693291834ae847722f90c87ea3df1cc8b9c56028913688743461890a904f024c10c07a01d00d406703001680b205401d80c8052028011008003801300700340120070020008002000⟩⟩
theorem candidate01254_checked : Checked candidate01254 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22879459639552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01255 : Description := ⟨70, ⟨13, 0x546a99d4368d7c566196fcb7b23cd1cdeda56c63561a52acd536a7b91b489a432a124ffc74f37f9b3cd366823299834ade52127d13789263e41ca0df86c83301740aec4fc1cf0d106282e212508682000d606502f81780aa05402580e0068033013807403801200780280100070018008002000⟩⟩
theorem candidate01255_checked : Checked candidate01255 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22887417282816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01256 : Description := ⟨71, ⟨13, 0xa8d533a86d1af865bdc1e76da56ac34a58faacd541a9b53dc8f546d22390bc8493ff1e64e9e6ff3679ad8d366823299828ade52427b93789263e41ca0df86c83301740ae05021d20d106282e212508681ac0be05502a012c09003801a00cc05a027013007403801200780280100070018008002000⟩⟩
theorem candidate01256_checked : Checked candidate01256 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22887417348096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01257 : Description := ⟨77, ⟨13, 0x2c354cca19cab22c313284b3eede4aed775136fdab6d2963d2f195d6a8452827c93808d944a210cff47cc3ca9c04dd26b434e9a14ca660a2b794a49e44d924991748543fd1bf0d9069231a1800ba04da21d10387b43721a30c485c40ae05502a012c08c04501f00d405202500f807403801200700280100070020008002000⟩⟩
theorem candidate01257_checked : Checked candidate01257 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22889299542016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01258 : Description := ⟨72, ⟨13, 0x14cf99ac70635f1588934259f76f6575139c1ba4d8a6ad34a58ccacd54729714789c046ca120f9869e342194cc1a56f29093bc98645d21910007c83941b20d1863230017409b443a2070f686242e213c093024c10007e03681700aa05402580e0052024010007403801200780380100070020008002000⟩⟩
theorem candidate01258_checked : Checked candidate01258 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22893460226304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01259 : Description := ⟨73, ⟨13, 0x299f33c8d7c5922650967ddba89ba4d5a694b17d706aeb566aa094a0a3c4e0236511e8483e61e68d6869e342194cc1456f29213c898645d2178ff47c83941b20d2463230017409b443a2070f686242e213c093024c0b805502a012c09004601c00d4052024010007403801200780380100070020008002000⟩⟩
theorem candidate01259_checked : Checked candidate01259 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22893460291584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01260 : Description := ⟨66, ⟨13, 0x53062650967d7bc79d44dd76aab4a58beaeb52827011b288f4241f30f2a7013749ad0ca64f226d91747fa3961b20d2462e30017409a43da1bc0d006242e213f09182dc11c08303081540a804b024011807c03501980a404801f00e807002e01400900380100070028008002000⟩⟩
theorem candidate01260_checked : Checked candidate01260 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22893594492928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01261 : Description := ⟨70, ⟨13, 0x546a99d4018acbf41f74f64797ba95cdedd56c63561a52c66566a8f13808da44d2168f9074f37f9b3cd0466b32995b8a424fd26e918482837e1998ba057628c136087c3d61cf0d1061c2e213e092828410007003581780aa05402580e00660270118074038014007802c0140080038008002000⟩⟩
theorem candidate01261_checked : Checked candidate01261 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22893859709184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01262 : Description := ⟨68, ⟨13, 0x11af8b1c259f76f6f7513749aaad2962fab35506a3c4e0236511e8483e61dfcdd269e3299628ade52322e90b87c83941b20d2c62e3001740adc4da21d0f687503401890b884f024609304701f80aa054025812008c03801980a404802000f8074038018009004401c0080038008002000⟩⟩
theorem candidate01262_checked : Checked candidate01262 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22893862895616 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01263 : Description := ⟨72, ⟨13, 0x14cc921458625f0957d7bb45c48da86adb4a17cab65542294937e8d944a1fecf2a74e3691ad0d0a65230514a49ee49022f10a87f03e11e48d8c69231a1808b9c53a26910387b43781a309f84301e808303081680ae05402580f8078035014808803e01c00b805002400d005002400e0050020008002000⟩⟩
theorem candidate01263_checked : Checked candidate01263 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22898929631232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01264 : Description := ⟨77, ⟨13, 0x2c3543395647062c112b84b3eede4aed775139d5aaad29631af195d6a8552aa7c93808d943ca10cff47cc3ca9c04dd269d3299628ade52827a136492645d2148fe47603641a60c5c6002e815b89b443a1ed0dc86803121710ab848c11c05502a012c08a03e01980a404a02400f807403801800900380180080038008002000⟩⟩
theorem candidate01264_checked : Checked candidate01264 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22902184394752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01265 : Description := ⟨69, ⟨13, 0x253b242889c255d9ee6872236a1ab6d285e3ad9547a9bf47b9fe4ec46d235b9a14ca460a26d11788543f81f08f246c633218d0c045ce2b3143087c40e1ed0dd868c2aa10c07a026410607a02d015c0a804b02100f807802f011008403e01c00b805002401000680280120070020008002000⟩⟩
theorem candidate01265_checked : Checked candidate01265 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22907515371520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01266 : Description := ⟨69, ⟨13, 0x2c2740795444ba138ed1735b56da50bc85b2a94d3748d94241fecf8e7953a71b48d0a6693291890b1856e27b137492045c1fb8f8c6ce34c18d0bf85ce2b514e881c3781a30ab84fc1e807603081680ae054025810007c03c01900a404401f00e006802800d006002800e0050020008002000⟩⟩
theorem candidate01266_checked : Checked candidate01266 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22913961959424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01267 : Description := ⟨70, ⟨13, 0x545247715787142c1f70f387913b31c72da66c7b575a4eb6c569aa453b48db4229d30e026d03439944c1a57429093e89bc48e23c109c7ea3c91bf0d946a231817309a043a1ee0dc868831412506d827410007603a01680ac05502100b0052025011007803a00f00680280120080018008002000⟩⟩
theorem candidate01267_checked : Checked candidate01267 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22920388706560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01268 : Description := ⟨71, ⟨13, 0xa8a490a2cf0b07dc3c89d98da66aeb49d8fab65569aa054189da46da18908a7633a61c04da06b93439944c1457429213dc9bc48e23c10a87f03c91bf0d9469c31817309a043a1ee0dc868831412506d82740b405602a812008403e01e00b0052025011007803a00f00680280120080018008002000⟩⟩
theorem candidate01268_checked : Checked candidate01268 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22920388771840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01269 : Description := ⟨68, ⟨13, 0x14a3a26ca7e4851a989ac25dedaf3e767b9a1c88dbf6c93511a4ebc95b62b4d4be9c144ba1a0ff27923b71ba4d7866e32895c08be3e11e48e586fc36517f8b9843e2070dd868c31210c06d82640fa07a02d015c0aa045021008803e01d00b805002000e00680280120080020008002000⟩⟩
theorem candidate01269_checked : Checked candidate01269 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22922530980096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01270 : Description := ⟨69, ⟨13, 0x254d23b892c38a12ef6a792bb31cd6dbf6c7b511a4ebc95b62b4d4be9c14219d38e026e93371944c1a57429613bc9b248e22f909c7ea3c91bf0d946a22ff17309b443a2070dc868c31210c06d82740fc07603a01680ae0550228108052025011007c03a00e00680280120080020008002000⟩⟩
theorem candidate01270_checked : Checked candidate01270 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22922535141632 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01271 : Description := ⟨70, ⟨13, 0x4a9a48513584bbc95d98dbf6a2349d8f4bc95b2ab4d49ea0c4e0a2510867953a71c04dd26b93371944c1457429493c89b248e22f90a87f03c91bf0d9469c2ff17309b443a2070dc868c31210c06d82740b405702a811808a04201f00f0052025011007c03a00e00680280120080020008002000⟩⟩
theorem candidate01271_checked : Checked candidate01271 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22922535206912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01272 : Description := ⟨73, ⟨13, 0x2f2543c95348fe35911c868c25deccf32775b9b5c7adbf6a2349d792acf51b27ad3828974341fe4dfe6e935019b8ca260d2ba14b09de4d9247117c7be3c91ca0df86ca33517f8b98560289103873c346189086036c0fc06702f01680ae0550228108076038011007c03a00e00680280120080020008002000⟩⟩
theorem candidate01272_checked : Checked candidate01272 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22922799382784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01273 : Description := ⟨74, ⟨13, 0x5e4a8792a68d644721a30977b6bcf9b7ed44693b1e9792b69567a8d93d69c1448217102a7f93cb9d9cdfe6e935019b8ca260a2ba14a49e44d9247117c7be3c91ca0df86ca33517f8b985662861038748346189086036c0b405702a811808a04201d80e005e026011007c03a00e00680280120080020008002000⟩⟩
theorem candidate01273_checked : Checked candidate01273 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22922799448064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01274 : Description := ⟨78, ⟨13, 0x60a29a541b951c6a626b09778f3b45c48dd76b03511a4ec5f5e6ad955a6a81527a8954189da4e0a23d0907fb3f19e54e9c7013749ae4d0666e32895c09e44db248117c7f03e11cb0d9469c31c17f8b984d21bc0d0062427e123086036c0c205a02a812008c03e01e00a404802200f807402e01400700340120080028008002000⟩⟩
theorem candidate01274_checked : Checked candidate01274 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22926830157824 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01275 : Description := ⟨72, ⟨13, 0x160ea4ecd1a2a9137872c2cdf62f4075338f9baed946b13519a44c665e6aa014b89d746da118ff67ca3809a08cd660d2b814c8a004c623d918884e4001cb0df86a83161810b903dc1a40c305b427e125086836016e08c03b01900c205501980c4058029011808803a01c00b8050014008002800c004000⟩⟩
theorem candidate01275_checked : Checked candidate01275 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22926881458432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01276 : Description := ⟨68, ⟨13, 0x141b951c69612ef3e6eab581a88d2762faf356d2acf512a76938285c40a9f8cf2e76737f9ba4d0666e32895c09e44db248117c6ca31c17f8b9850c21f0e9068031213e09184301b60a303981c00b40550240118076038017809804802200f807402e01400700340160090040008002000⟩⟩
theorem candidate01276_checked : Checked candidate01276 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22927094398976 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01277 : Description := ⟨70, ⟨13, 0x506e3590977b7b8adba4d606a2349d8bebcd5b4ab3d44a9da4e0a23d0907fb3f19dfce926e934199b8ca257429192a88be42e1fd0f7c72836518e0bfc5cc2b713688743a81a00c484f024610c06d824c0fc05a02a812008c03b01c00a4048022010007c03a018008803801a0090040008002000⟩⟩
theorem candidate01277_checked : Checked candidate01277 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22927098560512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01278 : Description := ⟨68, ⟨13, 0x14cea18456615afb87b23cd1dd6e6f7143749b18d584f7a75d1b689a4329fece9669e3411834ae852127d11e07c83941bf0aec4fc26810e87b839e1a20c504f024a10d049823010006b03481940bc05a02a815007003301880b0052022010007403800f00680280100070018008002000⟩⟩
theorem candidate01278_checked : Checked candidate01278 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22929289019648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01279 : Description := ⟨74, ⟨13, 0x572aa4343d8d6457608efb87b3bae5c6ee2e6fa378db52d906a2b49159e9ef4bc236cff67e33b89d20dfa6d335099bcc9c60d2ba11e08643f51ef8e506ca3191808ac04fc268129087440e1ee0c5057428210b07903640e806903381940b805a01d80e006202c014809004400f0068024010007002000c004001⟩⟩
theorem candidate01279_checked : Checked candidate01279 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22945997160704 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01280 : Description := ⟨72, ⟨13, 0x12a3889431609cfb575039e5b84d5e6922f35706a5551e27bd2e28df42f9f28f2671e3761ae8d1064e30515c09b649022f90a88283fd1f00df866631a1800acc50226a129087c40e1ee0d185682480f206c81c00d205b02d00f807003101780b404602200b805001c00d0058028010007002000c004001⟩⟩
theorem candidate01280_checked : Checked candidate01280 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22948081762304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01281 : Description := ⟨71, ⟨13, 0xb07502225cf21768b709abcd4d6922f356caad3529a6f92ea8db4231fecf947373761b4cd1066732718909ec4dd2480fdc7c63b01cb0df869831a17f0ad453a285133881c3781a30c3849021e0f206c81d80d206102d00f807803201880b0052023011006802800d00600280100070028010004001⟩⟩
theorem candidate01281_checked : Checked candidate01281 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22948287225856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01282 : Description := ⟨74, ⟨13, 0x4a8e49913684ebc79da2e786e2b585a98d215e6ad955a6a534df2120ff67953a71c04dd26853349884c0c57027a136c92045f2140fd87983b31c08da069e31d17e0b8c56a29d134881c3781a30c4856424410e078035c11806102d00f807803201880a404401f00e807003401800b805001c00d0028010004001⟩⟩
theorem candidate01282_checked : Checked candidate01282 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22948288136192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01283 : Description := ⟨75, ⟨13, 0xbc2ca8e36d11d8694275e6ede26e2b585a98d215e6ada559ea3a4f7a6f90c27973b39bfcdd26853349884c0c57027a136c92045f20b8f747983921c08da066c31d17e0b8c50423910f881c3aa1a30c4850024410e078035c11806702d00ec07003201880bc04401f00e807003401800b805001c00d0030010004001⟩⟩
theorem candidate01283_checked : Checked candidate01283 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22948552377344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01284 : Description := ⟨70, ⟨13, 0x571e73b11684abff5f9aeb873638e1c56da86c6b5b9a50bcc51ca6fd1bc7fc3f11e74edc7493691948c1a55926f11dc8bc4321fa8f7c6c63301808b9c56028913687b43721a30a904f024c10c07a023c0e806703001680b205401d80d0050025011008003801300900340120070020008002000⟩⟩
theorem candidate01284_checked : Checked candidate01284 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22976096403712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01285 : Description := ⟨64, ⟨13, 0x1434975c7ce1c4f387913ad9c72e1d6d3363daf2d274f9a114ff87e03811b40d3865130694849f44de2190fd47be37d1b28d4466a2e613408183dc1b90d106282780db04b02000f207402d01580aa04101d80b004a022010007803a01300780340120080018008002000⟩⟩
theorem candidate01285_checked : Checked candidate01285 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 22988973965568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01286 : Description := ⟨68, ⟨13, 0x15b2a33cea648905780bbfdde6eed073938f5c24dc46b9b4fd9a0a214bf248921e82f3fd1cc0dce69d34299a4c205c52c8156c9b848f1e30e006642be14489504662040c485c427e12308603d015206a03101840ba05401d00c8052028012807c03801400800380120070028008002000⟩⟩
theorem candidate01286_checked : Checked candidate01286 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23147492425984 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01287 : Description := ⟨64, ⟨13, 0x13a687bc019da0dc16b9b4fd980b64510a5052488613fd1e64ece6eb34e99a4c0a5ba2d21634aae4dc261123c6f833218d0ae050c23610306242e213f09284301e807203501840ba054028813807403201500a404a01c00b005002601000700280120070028008002000⟩⟩
theorem candidate01287_checked : Checked candidate01287 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23147494572032 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01288 : Description := ⟨67, ⟨13, 0xa33cea64890057683849b88d7369fb3016c8a21492a43d05e7fa3981b9cd3a6853349810bac5b92c4956c9e84dc24790b87f43c61c00cc856e25411c081031217109f848c2180f403501840ba054028813807403201480a004a01f00e006002a01400800380120070028008002000⟩⟩
theorem candidate01288_checked : Checked candidate01288 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23147500814336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01289 : Description := ⟨64, ⟨13, 0x124487ebb41c24da86b9b555982b6451024a918a8793fd1cc0da469d3021758ae4528262923c85c3fa1e30d8c6643171808adc4a82380f686802e213f09184301e808e04201840ba0540288130074033014809404801f00e006002a01400900400120070028008002000⟩⟩
theorem candidate01289_checked : Checked candidate01289 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23179713069056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01290 : Description := ⟨61, ⟨13, 0x23e915e86e4301f9cf387743b31c18dd26b71cd8c045c22c814b09f44a42470f1c72837e1980c684a221d0f706e431413c092843416209d049823c11808903d81a40b405502a010807003401880a404a022010007403801600680280100070018008002000⟩⟩
theorem candidate01290_checked : Checked candidate01290 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23199880347904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01291 : Description := ⟨64, ⟨13, 0x10f3768375dabad4462f2d9163caec50ea5051268613fd1e64ece71a3809a1ccdc6052df9634a1c4dc2478e586fc36518c0bfc57028611b068831217109f84942180db03e01c80c205d02a814408803a01500a404a01d00b005002000f00700280120080028008002000⟩⟩
theorem candidate01291_checked : Checked candidate01291 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23211902304256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01292 : Description := ⟨72, ⟨13, 0x147199f49123851037863b41c24dd76b035118bcb6458f2bb143a92a43ca0a8ff47303809ba4d0666e3021758b1252827a137098048f2170fe878c3af1cb0d946382ff15b89504701a00c485c427e123086036c0c205d02a814408803a014809404801f00e806002a01400800380120080028008002000⟩⟩
theorem candidate01292_checked : Checked candidate01292 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23211908546560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01293 : Description := ⟨67, ⟨13, 0xa4b50da189043801bf45e06ed4739b905bd6dd56b8b505a529ee4b6a4b51f682d3ff1e74ed671537f9a6ccd665326e130891e300174087c40e1ee0dd868c2e213e093043415809403801b00c605b02a8150070034015808c03a01c00b005002000e005802000e0040018008002000⟩⟩
theorem candidate01293_checked : Checked candidate01293 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23215577563392 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01294 : Description := ⟨71, ⟨13, 0xa17c70a1970447fe3cdde0aed771eb82dbe0dd26b734fda52a3b4f725f925a82f3fd1cd4cd26533011708b204c22498f207283651980ba056028912808cc43a2070dc868c31217109e049821809304782240d406703101540a803801a00c8052025010007403801600700240100070020008002000⟩⟩
theorem candidate01294_checked : Checked candidate01294 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23216044146944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01295 : Description := ⟨64, ⟨13, 0x18238803bf9ba6d776b334b18bcb6259aac6950aa5550f25c12548f83c11bf4dd86a13401958b1a4c01fe8f2c75a33318b8c005d026b12787b83781a00b884f42500f206c827c0e006102d814408803e01c80e006602b0148090046014007002c010007002800c004001⟩⟩
theorem candidate01295_checked : Checked candidate01295 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23219742654464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01296 : Description := ⟨58, ⟨13, 0x4e524972008b03f25c7cdf365fadc964ea6d460a0c0fca7363759a08c205c52c2955898a47a21a90007963b51c00c5c4d62200c505c421a0f4067023c10806c02f81740b005402500d00660270128080038012008002c00e0050018008002000⟩⟩
theorem candidate01296_checked : Checked candidate01296 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23247695397120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01297 : Description := ⟨59, ⟨13, 0xa9cce5648b1cb87d4019fa8ebb72237d9b50cbf5b7abd544893047f1f94edc72036914389824761f10f206c6319180888040c1ed0d105c42180f4067023c10406c02e81600a804a01a009404001c00b004c024010007802c0120070028008002000⟩⟩
theorem candidate01297_checked : Checked candidate01297 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23247755215104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01298 : Description := ⟨59, ⟨13, 0x9ca46ee00afa275f37cdb50cbf5b7abd54488c043c9f84e6a6d23421840b8a5852ab13148f43f51f10ed46c630112a08804081ed0d005c42180f4067023c10807403601740b005402500d00500250120080038012008002c0120070028008002000⟩⟩
theorem candidate01298_checked : Checked candidate01298 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23247761457408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01299 : Description := ⟨59, ⟨13, 0x8e5be89d7cda85b1ab9550ea24492a3010f27e13cd1cd4e3a6d23421620aac4c523d0fe07c43b21b18c044a822010207b434017108603d019c08f03601740b0054028813809804a01e00d00500250120080038012008002c0120070028008002000⟩⟩
theorem candidate01299_checked : Checked candidate01299 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 23247761522688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate01299_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch012

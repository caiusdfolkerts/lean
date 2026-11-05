module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch003
open Papers.RationalityTen GraphCandidateCoverage

def candidate00300 : Description := ⟨80, ⟨13, 0x15e9ac150f681120f84a406dd40e95734b8fdc1adf46f1b709b52d906af34f5a48b9e4f7a6f93547fb3e51ef0f467823a81cdcdfa6ec3699a84d10667327117c89c4271e48e506fc36518d0b5c56025210e881c3dc1a30ae850424810b07903640ec06a034819c0b605a01c00c8062029011808801c00d0050024010007002000c004001⟩⟩
theorem candidate00300_checked : Checked candidate00300 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8654359265536 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00301 : Description := ⟨76, ⟨13, 0x140884a4201da2ea073cb835b84da96af34f5a48b364df268d2807fb3e51e4ced273738f1bb0da66ba344199cc9c63c248117c89042a1e48e586fc36518d0b3056629d135894840e1ee0de068c2b412408583c81b206a03481840b605a01f00c806203001780a404602200a003801a00a004802000e005002000c004001⟩⟩
theorem candidate00301_checked : Checked candidate00301 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8654627733504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00302 : Description := ⟨75, ⟨13, 0xa04483212907d768ba81c1adc26d4b579a7ad2459b26f934e7fb3e51cdcdd86d3344199cc9c6382ea92408be4441fd8f247603961bf0d9469831a1670ad453a26b129081c3dc1bc0d184902160f206c81d80d4069030816c0b403e01900c4052023011006c034014007003401800a004802000e005002000c004001⟩⟩
theorem candidate00302_checked : Checked candidate00302 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8654636056576 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00303 : Description := ⟨79, ⟨13, 0x9ffc25211502376f3aa5cf4e136f23721b5ed6469cb48137c9a34a01fecf9479739a1c04dd26d034298e0baa49022f90b07923961bf0d946342ca1588a8050e26e12a88f043620a0f8876037e1a60c285b02b614209084201de0d604682300d406901900c406002f014808c04401f00f007403801b00d005001c00d0050024010007⟩⟩
theorem candidate00303_checked : Checked candidate00303 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8655164408320 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00304 : Description := ⟨75, ⟨13, 0xa6ed00e5db17c849be75ef4f6675d3a85d16dc06d13631adcd4269327c137a9aa463a29512e7e43e59d34dd46cc3361940ab254829611dc8bc37d1980c045ae2b012908143d81cf0dc868c31417009e04981e60a404781b80d206702f01580a803601a00c404a02000f00700260120068024010007002000c002000⟩⟩
theorem candidate00304_checked : Checked candidate00304 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8665768165632 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00305 : Description := ⟨74, ⟨13, 0x53928010957cd3ae1d3ee8f739b691ae2d426942a7937e92746222b0fc47c93d69e58ecc6ce35b9a6ccd865231e156492247722f110c85e3e21b18c045ce2d115989483761a30c5055427c12607a01b00c005f02d01580a803f01a00bc050027011008403c01c009804802000d005802400e0040018008002000⟩⟩
theorem candidate00305_checked : Checked candidate00305 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8682448420864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00306 : Description := ⟨72, ⟨13, 0x14008ba4255f34eb874fb9c1b48d716a134a153c9bf4621f88f9279a3671a6ccd865231c16f0ab253f24891dc8bc42b1fd8f886c634c1808b9c56a2520dd868c31415709f04981e807703601800be05a02b015007e034014009c04401e00e006c034013009004001a00c005802400e0040018008002000⟩⟩
theorem candidate00306_checked : Checked candidate00306 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8682456743936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00307 : Description := ⟨74, ⟨13, 0x53aa905437a02cbb62f90947febe3de72eee751ba2db7cda66c735f1a7cd2551da7c137c9aa45b2128ffe7cd3a69c08dd06d034d19a0c9e54829611dc8be37d1b28cc05ae2b012907b83b41be0c405bc27812606d01a80d206703001580aa03401900c405002000f007402600e0068024010007002000c004000⟩⟩
theorem candidate00307_checked : Checked candidate00307 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8697980158208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00308 : Description := ⟨62, ⟨13, 0x423de0eebc74db245534a5751f28313e69b94d3a1f10948313ff9f98f8a7ae3cd1d34e0452426191e085e34e19a8bfc5cc25210386f83421880b784f024c09103c01b80be05602a812409004001f80d804e02000f007402400f0070034012008002000c004000⟩⟩
theorem candidate00308_checked : Checked candidate00308 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8727533289472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00309 : Description := ⟨66, ⟨13, 0x53ba89b36e8c04325f12f6275cba7dd1ee736c935d9a4ec9855527cd16688c3f19f24f7279d35e1a80ca250e24891e08bc3e21cb8cc45cc25210386ec31413e093036c146091037017c0b805a02b015406c027012008803c01d009004001e00d00580240100040018008002000⟩⟩
theorem candidate00309_checked : Checked candidate00309 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8729676284160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00310 : Description := ⟨66, ⟨13, 0x4dba3010c975cba7daecd27648aa694189f34479f8cf9279a35c9a80ca263c29e9490a1c49123c117888642f1f10e5c69c331173094840e1bb0c504f824c0db04881b80be05c02d01580aa04902400fc06c027012008803c01d009004001e00d00580240100040018008002000⟩⟩
theorem candidate00310_checked : Checked candidate00310 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8729684672512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00311 : Description := ⟨67, ⟨13, 0xa1a42c1ef4f64775ba7dd16e6f6bcb575a4ec9853827cd3b48a544d1ff0f9274d3811a70d0e6512a414848f045e1e48df866a3181730b5c5761cf0dc868831413c092836c14809104001b80be05e02d01580aa036013809404402000f007402400f00680280120080018008002000⟩⟩
theorem candidate00311_checked : Checked candidate00311 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8730076807424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00312 : Description := ⟨73, ⟨13, 0x26dd146864c2c1f12f7074fb5d9abad27648ae6d4e09f34ed229d11c8153e49ec8f326a03439944c7853d292143892247822f10507c43c91cb8df86623181730b445701d20dd868831413e092836c12206e02f81680ac055024812006c027013008803c01d009004001e00d00580280120080018008002000⟩⟩
theorem candidate00312_checked : Checked candidate00312 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8730081034240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00313 : Description := ⟨70, ⟨13, 0x5b8e9d54378be424df1ef637773af1d16d8e6be3571a4ac984f826f53548b644ea1f0ffe7e63a69c08d346863279520a4247822f0cc063230116b8ac04a42070ed06f834216f09e04981b409104001b80d206702f81580aa03601a00c404e02000f007402400f0068024010007002000c004000⟩⟩
theorem candidate00313_checked : Checked candidate00313 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8730192412928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00314 : Description := ⟨69, ⟨13, 0x27fd3788bfc331ee4ebf6bdb57da44c9154e27c137a88f3f19f24d3668433618e0a7652228892b492847b2228f8872e34d1978c6c5c82b5129081c3ac1bd0cf85b427c12606c024411806e02f81580aa04902400d8068031013809004401e00e807003601a009002c012008002000c004000⟩⟩
theorem candidate00314_checked : Checked candidate00314 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8730204702720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00315 : Description := ⟨68, ⟨13, 0x14d9a61cdba2df1647c4bd89d1ee736c3b5c5ab4d42694b261532a8e459a230f7279d3589a6cd0866c32994387c439718c8c045d025210386ec31417109f04981700a304882400dc06c02f81700ac05502a00d8068027012007803a01c009004001e00b004802000e0040018008002000⟩⟩
theorem candidate00315_checked : Checked candidate00315 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8730733248768 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00316 : Description := ⟨74, ⟨13, 0x5b669d14cf9b745f62c8f4f6b9b569a84d29648aa6d5049a7454223d0f27b33cd1ad0d3a684336194cc7853d292143889042f1a48cc86323011740a744d6252110081c31417109f849812206e02f81740b805602a815009204801b00d404e025012007803a01c009004001e009004001c00a0040018008002000⟩⟩
theorem candidate00316_checked : Checked candidate00316 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8731005878272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00317 : Description := ⟨67, ⟨13, 0xa73cdb9f12f626b8b569a84d29648aa7114e7b235b1a6cd0866c32998f0a7a5242870f8872e3191808ba05a22b3129081c3a41bb0c505c427c12605182440dc06c02f81700ac05502a012409003601a00bc04e026012007803a01c009004001e00b004802000e0040018008002000⟩⟩
theorem candidate00317_checked : Checked candidate00317 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8731270119424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00318 : Description := ⟨70, ⟨13, 0x4fda118f2376c3a61c1adc26d0b541a6ea9b54229514129a7454225108e7fc39b9bb0d966883339938c784df24a116889042a1e48df86682fd1720a744d6252110081c3701860b684902160f206e82bc13606e02f812408003e01b00d4064031013809404602200900280120080028010006002⟩⟩
theorem candidate00318_checked : Checked candidate00318 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8731945535488 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00319 : Description := ⟨69, ⟨13, 0x281508f7693a75b7eda36a2349d4aea0c4dca69d1508943fe1f1cf667953749b34d7266e32898f0a7a52926e124489042a1e48df869c2ff1730a744402070f6868c31213f086036c0f006e02e81680ae055024810007c036012808803e01d009004001c00d00500240100050020008002000⟩⟩
theorem candidate00319_checked : Checked candidate00319 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8731963228160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00320 : Description := ⟨75, ⟨13, 0xa76d14281317d8b0c246100f8c7903b55d36e8c73436fdb4ad956bab50da4aaa7545a6ed3548b64251ffcf8a7b63c91ba4d9e6bf34f99b4c9e4dc2488df86c833218d0c0053a26b129088040e1ba0c405bc27e10d06d02640f006902f815c0aa040018809c03e01d009004001c00d005002000e005002000c004000⟩⟩
theorem candidate00320_checked : Checked candidate00320 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8732004385024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00321 : Description := ⟨75, ⟨13, 0xa05445219308f7c4bdb5d3adbf6d1b5d9a88d275cda8f93e69b9453a24102a7c73d91e5cdd26cd35019b8ca263c29e94a49b849120a0f887923971bf0cc45fe2e61688acc40e1ed0e906ec34618909f04301b607803701680ae055024810006c02f013008803e01d009004001c00d00580280120080020008002000⟩⟩
theorem candidate00321_checked : Checked candidate00321 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8732227469312 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00322 : Description := ⟨73, ⟨13, 0x2bb94eaa1bd0262f915e848be3de72eee74dba2dcdadbf6d2b639af8d43692a7c13769aa45b2128ffe7c53bf9c08dd26cf34d19b4c9e5482960df86c833018d0c005ae2b0129081c3b41be0c405bc27810d06d01e00d206702f815c0aa04001a00c404e02000f807402400e0068028010007002000c004000⟩⟩
theorem candidate00322_checked : Checked candidate00322 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8732272787712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00323 : Description := ⟨73, ⟨13, 0x27f92718bfc33213ce986dfb695af6d466912e6d538a884f826ed1286e93679a6cd0a66b31c14ec9f04df25692508b4445216105072e37e1b20d3465e3021720ad44a42070eb06f430c16d09f04341b009b046017c0ae0550248100068031013808c04401f00e807003601a009002c014008002000c004000⟩⟩
theorem candidate00323_checked : Checked candidate00323 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8732285077504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00324 : Description := ⟨80, ⟨13, 0x14e8a6650062fb16184b3c75d3cdbf6d2b5cdab6d41694aa6d5089c04d3a2a11288473e41eccf2a6e93679ad0d3a685335994cc7853d29493708ba4482150df86c83491990c686002e814e89ac4a4220103868c2e213f086817c0ba05b02b81540a804901f00d404e025011807c03a01c009004001c00a004001c00a0040018008002000⟩⟩
theorem candidate00324_checked : Checked candidate00324 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8733086253056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00325 : Description := ⟨78, ⟨13, 0x539e99340184b3e25edae9e6dfb695ae2d5b6a0b4a5736a9c544270114e8904301f20f647973749b3cd6c69b34299acca663c29e94a49b845d20a0e5c6fc36418d0c005d02d1159894840e1d20dd868c2e213e08681b00be05b02b81540a804901a00bc04e026011807c03a01c009004001c00b005002000e0040018008002000⟩⟩
theorem candidate00325_checked : Checked candidate00325 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8733350494208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00326 : Description := ⟨77, ⟨13, 0x28032718b9457a12cf6a74f36fdb4ad716adb505a52b9b54e2a213808943e41ba4d9e69b34299acca663829293d49b845d22290b08283971bf0d9069631a1800ba056a25210387503761a30b884f821a081036017c0b605702a8150092034013808c03e01d00e006c034012008804001c00b005002000e0040018008002000⟩⟩
theorem candidate00326_checked : Checked candidate00326 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8733358817280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00327 : Description := ⟨79, ⟨13, 0xa64cffa2bd0938453de1eeeef476dbab1cf4e136e43675b32d806b2352da409bd4d5229512e7fc3e49cd0dd269d34299b0c7e53a29612448bc3c91bf0cc863430116d0b0454026e12a888c4141e90f006dc34c18d0b60508242108077835814809104602040dc06901b00c404e025011007c03c01d00e004802000d0050024010007⟩⟩
theorem candidate00327_checked : Checked candidate00327 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8734621303552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00328 : Description := ⟨74, ⟨13, 0x53a299917d8b0b829b7ed736adb509a52a9b542269d1508943d99e54e686e935a1a74d0a66c32998f0a7a52922410a879237e1a48cc86343011740a744d6252110081c34618a0b884fc12206e02f81740ae05602a815009203e01b00d404e02500f807803a01c0090040014009004001c00a0040018008002000⟩⟩
theorem candidate00328_checked : Checked candidate00328 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8735166627840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00329 : Description := ⟨73, ⟨13, 0x22bd07d7bf3da9c14dbf6b9b56da84d29544269d15089439a1ba4d3a685336194cc705252160f246fc34b1990c686022e81670ad453a26b129088040e1d40d186282e213f04882040dc05f02e815c0ac05502a012406c027012807c03c01d00e006c0340120088040014009004001c00a0040018008002000⟩⟩
theorem candidate00329_checked : Checked candidate00329 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8735703433216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00330 : Description := ⟨82, ⟨13, 0x501e4e31778af42420faf837b53a75caada86ba356da7ed285cdaa855109ba4d3a2b51287c73bf9b48d3c6853349948c7053e29293d495444521610507c43c91b18d2c66631a1738b3856a29d110081c3da1d40de068c31210c07a01e00d405a02c015c0a8040019008804001f00e006c034012008803801a00b005002400e0050020008002000⟩⟩
theorem candidate00330_checked : Checked candidate00330 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8740838309888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00331 : Description := ⟨75, ⟨13, 0x9fe433213cf0a75fba61ce0da56bdb57da8cd2264aaa7950e9f04dda0b8fc679a3679a6cd0866b31c14449be4c624a11ec8b442b1d80e5c6c832f18d8c085c82b5129081c37a19f0c305b42ae13e09304341b009b04601dc0be05502000fc068031013809004602200e807003601a0090030016008002000c004000⟩⟩
theorem candidate00331_checked : Checked candidate00331 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8744767326208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00332 : Description := ⟨80, ⟨13, 0x13fc938c5261990b384f3a61d10e6f6d2b5edac4d466913255736a6d4f8275d3768ac4499ec8f326cf34d9a08cd6638288937c98c49423d916888a42c20a0e5c6fc3641978c586042e41668ad05082390de869030c16d0ac04f824a10d06c026c11805f02a8100068033018809c04602200e807003601a009002c014008003000c004000⟩⟩
theorem candidate00332_checked : Checked candidate00332 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8745163687936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00333 : Description := ⟨75, ⟨13, 0xc26d37e9974018bcc56e12cf857b4ba79d00e6a6f8b695b1ad6e6ac3505a52b9e536a70108e7c83d59e80e046cf34119acca64c322e913884e37e1b20cc06002e816b8aec3721a20b88548278125086826811e076035817c0b605902a8150068033013809404602000e807002400f00700280100070018008002000⟩⟩
theorem candidate00333_checked : Checked candidate00333 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8745696395520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00334 : Description := ⟨70, ⟨13, 0x5392990e8f739b5c5ab4d42694b25553ca874562244f5a7963b31c6cd6e69b34219b0ca663c287110c85e3e21cb8c646022e81688acc4a42070dd86282e215509f049812206e036017c0b805602a815007e03601a00bc04e024010807803a01c009004001e00b004802000e0040018008002000⟩⟩
theorem candidate00334_checked : Checked candidate00334 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8747913117696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00335 : Description := ⟨76, ⟨13, 0x136b8bb45760faf4f744b9c1ae6d5a6a134a592aaa0543a69d0f27b33cd1a74d0866c32998e0a7e52628711108563fb1d80d306643191808ba059c2b514e89ac4a422010386282e215709f849812206e02f81740b805602a815006c027012809003c01d00e006c034012008003c018009004001c00a0040018008002000⟩⟩
theorem candidate00335_checked : Checked candidate00335 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8748185681920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00336 : Description := ⟨73, ⟨13, 0x2dad36b83cbe01ecef4f6b9b569a84d2964aa68d15489143c9a74d0866c32998e0a7e5262870cc86323011740a7450826b12908e44402070ea86282e215809f849812206e034019c0be05d02e01580aa05401b00c005e027012809003c01d00e006c034012008003c012008003801800a0040018008002000⟩⟩
theorem candidate00336_checked : Checked candidate00336 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8748714164224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00337 : Description := ⟨79, ⟨13, 0xa00c25a0f2f8078eba79cdadbf6d2b5cdab6d41694a7013468aa4239f20f2e6e93679a74d0a66b32998e0a7e4dc22e90b06fc3641990c686002e814e8a104d625211c888040e1d50d185c42b013f08681a00ce05f02e816c0ae05502a00c005e027012808c03e01d00e006c0340120080038014008003801800a0040018008002000⟩⟩
theorem candidate00337_checked : Checked candidate00337 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8750794539008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00338 : Description := ⟨65, ⟨13, 0x27ed27e845c1f572e9a73c11d40e6e7053761b2cd426883339938c70441214105c7fc3e51e60ecc7343811b00d3c66c31d17e0b8c59c2b514e89ac4a422010386f03460af04d81e00be05b02d010007e03e01b00c8062027011808803601a009003801a005002000c004001⟩⟩
theorem candidate00338_checked : Checked candidate00338 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8757446837248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00339 : Description := ⟨79, ⟨13, 0xa77526289b40293a46022290c984bbe25edaea0747b9a1c14dbf6d33649aecd40693ae79554a3e4f9a7051668973e51ee4f247343749b40d786a033519449b849122f90507c43c91cb8df86ca33117f8b984a42070f706ec34613e06d82640b605a02b81580aa023011007c03c01d008003801a00b00500240100040018008002000⟩⟩
theorem candidate00339_checked : Checked candidate00339 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8766049288448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00340 : Description := ⟨75, ⟨13, 0xa01425de3aed27503829b7eda66a0349d4aea0c4e0a69d1508944239ff0f947b33ca9cd0dd26d035c99a8ca263c29e94a49b849122f91208543c91bf0d9469c2ff1730a744d6252110081c3dc1a309f836c0ba05b02d015c0ac05502480f804a023011007c03c01d008003801a00a004802000a0040018008002000⟩⟩
theorem candidate00340_checked : Checked candidate00340 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8766321917952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00341 : Description := ⟨79, ⟨13, 0xa0144521930977c4bdb5d40e0a6dfb699aecd40693ae6d47c9f34e0a29d12086040a9f28f6479739a1ba4da06a03351944c7853d294937092245f20a0f887923971bf0d946622ff1730b4456625210387b83a41bb0d184f81b605b02d015c0ac05502480bc04c023011007c03c01d008003801a00b00500240100040018008002000⟩⟩
theorem candidate00341_checked : Checked candidate00341 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8766586159104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00342 : Description := ⟨78, ⟨13, 0x500a4e3114864c25ded4ea070536fdb4cd766a0349d736a3e4f9a7051287ca39a1ba4da06a03351944c7052527a937095449122f91148584141f10f2472e37e1b28cc45fe2e615a894840e1ee0ea06ec34613e06d82040b605a02b81580aa049011808803e01e00e806c034011008003801a00b00500240100040018008002000⟩⟩
theorem candidate00342_checked : Checked candidate00342 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8766594482176 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00343 : Description := ⟨79, ⟨13, 0xa02c252100f8c7903b55d46e0a6dfb699aead3e692aa2137c9a3453218d0948183ff9f34f2e7343749b40d7069f334193cc7853d294937092245f1e48df86ca33218d0b3056629d13589484402070f7075c3741880b784fc1b406a034815c0ac05502480c8062030017807c03c01d008003801a00a004802000e005002000c004000⟩⟩
theorem candidate00343_checked : Checked candidate00343 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8766833885184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00344 : Description := ⟨83, ⟨13, 0xa0149c612f07d7c1bda9d40e55711b829bb0dbf6d33501a4eb9b4e0a69d15a8943e51dfce9a7343811ba4da066a32898e0a7c52527a92a88be44521610507c43c91cb8df86ca2ff1730b3856a29d13589484402070f707503781a306d816c0b405802b81580aa023011008003e01e00e806c034011007003401600a004802000a0040018008002000⟩⟩
theorem candidate00344_checked : Checked candidate00344 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8775180222464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00345 : Description := ⟨80, ⟨13, 0x147fa1a500a1f70b084bbe15ed2ea074039a9c78df16d335e5abad40693ae794e0a3e512a7cd3b49c14239ff0f947ab3d01d34e046d034e1a1ccd465126191e08be44e2138f246fc36519a8c605fe2e616b8aec3dc1b90d1054827812506d82680ec05b02d01640ac055012808c04402000f007401e00e00680280120080018008002000⟩⟩
theorem candidate00345_checked : Checked candidate00345 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8778932060416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00346 : Description := ⟨86, ⟨13, 0x50161290807a93c81e0eed575e3a8dd18e736d335d5ab8d3e692b255540a874df268d0f884a4189ffcfcc7cd3d79e58ecc71b3681a7cd0c66832798f0a1c4dc26192448f045f22410bc6ca33218c8b3056629d13589484402070f706e83421880b7855427e12606d01a80d205602a80c8062030017808403c01d008003c01c00d004802000e005002000c004000⟩⟩
theorem candidate00346_checked : Checked candidate00346 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8779316133888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00347 : Description := ⟨92, ⟨13, 0x14029b5c9c628d11487dc3261610977c13da5d40e88737b699aecd5d6a0349d92ab9b53828f944a9f34ed27051588933e51ec8f326d03501a1ccd465131c14fca4c50e26e130c92247822f91148584141f10f2472e37e1b28cc46302ff1730b3456828411c87b83aa1bb0d1056027c12506d816c0b405602a808c04401e00e806c034010007803801a00b00500240100060018008002000⟩⟩
theorem candidate00347_checked : Checked candidate00347 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8779473092608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00348 : Description := ⟨83, ⟨13, 0xaf4d3b290b43aa0445e6128f857503a55cd2e3f706b7d1b84da96c835fdabcd3d6922e794769f04df26a908e7fc3e51ef0f467823a81cdce0a6ec3699a64d10667327117c89c4271e48df86ca33018d0b5c56025210387b83721a30ae850424810b07903640ec06a034819c0b605a01a00c8062025011808801c00d0050024010007002000c004001⟩⟩
theorem candidate00348_checked : Checked candidate00348 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8783208284416 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00349 : Description := ⟨80, ⟨13, 0x140293a44521930977503a3dcd0e0a6dfb699aecd40693ae5d47c9f34e0a2b0f947ad3b31cd0e366e93681a80cd465131e137092245f22190a88283e21e48e5c6fc3651988bfc5cc2d1159894840e1ee0dd868c2aa13e06d82640b605a02b81580aa03f01f00bc046022010807c03c01d008003801a00b00500240100040018008002000⟩⟩
theorem candidate00349_checked : Checked candidate00349 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8783229157376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00350 : Description := ⟨78, ⟨13, 0x500a12f07d78ebb49d40e89735b829b7eda66a0349d3829a74239ff0f947b33ca9cd0dd26d03351944c7053f26e12448be4441fd8f2476037e1b28bfc5cc2ce15a8a744d6252110081c3dc1a30ab84fc1b607602e816c0b405702b015407c025011808803e01e00e806c034010007003401800a004802000a0040018008002000⟩⟩
theorem candidate00350_checked : Checked candidate00350 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8783501721600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00351 : Description := ⟨82, ⟨13, 0x4ffe12908a7c6bc99db6ea973d384db90daf6c03591a72d204df268d1548473fe1f28f2e7343749b40d3a68531c14fc9b849122f90b079237e1b28cc86342ca1588a8050e26e12a88f044620a0f8876036e1a60c285b02b614209084201de0d604682300d406901900c406002f012808c04401f00f007403801b00d004001c00d0050024010007⟩⟩
theorem candidate00351_checked : Checked candidate00351 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8784013427200 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00352 : Description := ⟨78, ⟨13, 0x50161290797903b55d46e6d70536fdb4cd7569f349537c9a34251ffcf9a79739a1ba4da069f334193cc7053f26e12448be42c1e48df86ca33218d0a7450826b12908e44402070f706e831016f0ac04fc1b406a03481a00ce05702b015406403101800bc03e01e00e806c0340100070034014009004001c00c005002000c004000⟩⟩
theorem candidate00352_checked : Checked candidate00352 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8784013688832 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00353 : Description := ⟨79, ⟨13, 0xa01425e0f2f8078ebb49d40e6d70536fdb4cd40693a7053468aa4239ff0f9479739a1ba4da066a32898e0a7e4dc248917c8583c91bf0d945fe2e614e8a104d625211c888040e1ee0ea868c2b013f06d81a00ce05d02d81680ae05602a80c005e025011808803e01e00e806c0340100070034014009004001800a0040018008002000⟩⟩
theorem candidate00353_checked : Checked candidate00353 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8784030203904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00354 : Description := ⟨88, ⟨13, 0x15e9a0449d21290807503a49cf2e587133835bb6dc26d4b5ddabcd3d6922e5d37c9a33e51eb0f267823b49d40e6e71e3829bb0da66ba3509a20cce64e31e117c88642a20a0f887923971bf0d9466631a1660acc53a26b129088040e1ee0de068c2b413d092042c1e40d903501a40b605a01f80f806403101800bc046022007003401600a004802000e005002000c004001⟩⟩
theorem candidate00354_checked : Checked candidate00354 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8791798251520 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00355 : Description := ⟨83, ⟨13, 0xa0449c61290797503961c4ce0d6edb709b52d776af34f5a48b9b4df268cf947823a81cdce0a6ec3699a84d1066732718e08be44521610507c43c91cb8df86ca33318d0a7450826b12908e44402070f707543781a309e84902160f206c81a80d2068033816c0b403201880c005e023011006c03400e006802c014009004001c00c005002000c004001⟩⟩
theorem candidate00355_checked : Checked candidate00355 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 8792335056896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00356 : Description := ⟨61, ⟨13, 0x215b06a7e8bc19c18d58687a75d3108f44182050e6c71a3411878bb058d28693048f04131e38df85a2281135094446c1ee0d1062824a10d04602200d606902d01540a805202800cc06202d015008803a01c00c805c02c00f00680280100070018008002000⟩⟩
theorem candidate00356_checked : Checked candidate00356 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9065407250432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00357 : Description := ⟨59, ⟨13, 0x89ebf19d76dc16ac33e19b4cae4c422b10927e53d91d3cdd669b34117c4b1055928593788ec4111f20df066028111b081834418a0b8849421a0f405b029c0d605f02a014809804701e80d006602d015009c038013009003c0140070018008002000⟩⟩
theorem candidate00357_checked : Checked candidate00357 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9504332808192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00358 : Description := ⟨68, ⟨13, 0x141d99042ae0d4fd175db6f1ab0d41694b3e18949d54c423d10be7e538d1b98d0466b3299878bda5d82d19634a1a4db26191d88263001740b4450226a11b08183dc1a20b8849421a06f035816c0aa05402900dc06602d015008c03a01c00c805c02600f00700280100070018008002000⟩⟩
theorem candidate00358_checked : Checked candidate00358 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9545369845760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00359 : Description := ⟨62, ⟨13, 0x5e86c553ff9aec4c61b8f3d77436fdab6d3c6412fa56a09be4ae1f28e686e93681a14c585db2a293f49ba4a42098f8c6fc31a17f0a704d82070d1861c21408d04601ec0d205a02b81540a8032018808c04401f00f007403801900680280100070020008002000⟩⟩
theorem candidate00359_checked : Checked candidate00359 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9600069804288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00360 : Description := ⟨67, ⟨13, 0x91340c9c14dbf6d3356da84b50576295940c95c47c21890247343749b40d0a66c30f17b4bb058d2a113dc94e4131f08f246fc36518d0c0453826a129081c3dc1a30c502300d205a02b81580aa054029010c06202200f807803a01c00c805c01a00a004802000e0040018008002000⟩⟩
theorem candidate00360_checked : Checked candidate00360 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9602217345024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00361 : Description := ⟨66, ⟨13, 0x54c24bd1c58193ae5b4cd5a6a12df15d0a084ae23e0fc676338c1b40d0866c30f17b4bb058d28691e08903f81f08eb46ca3191808a704d425210387b831412604601a40b805a02b01540a805201e00e4062024011007803a01c00c805c01e00d004802000e0040018008002000⟩⟩
theorem candidate00361_checked : Checked candidate00361 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9614699593728 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00362 : Description := ⟨63, ⟨13, 0x8193a81b7ed5b6a0af99734a5550425711f07ca3b41c60dd26853359878bda5d82c6936c8be4482098ff475a37e18d0c0053826a129081c3dc1a308682300d205b02d015c0aa05402900e4062023011007c03a01c00c805c01c00d005002000e0040018008002000⟩⟩
theorem candidate00362_checked : Checked candidate00362 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9616779968512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00363 : Description := ⟨64, ⟨13, 0x148f9ffcd764c712386fbcf5d70e436df3629a78c825c4293937c95c3f11f28dd06d0316168ca8a4fd26e91dc8964031f18df468c2fe14e09b0346187093042816a08d04601b40d206002d01540a803201880a004602200f007403801900980340100070020008002000⟩⟩
theorem candidate00363_checked : Checked candidate00363 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9805825581312 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00364 : Description := ⟨63, ⟨13, 0x92f42aa0d4eb671b3699a84b7c4ea2620fc071b3681adccd861e2f6968ca1a4481fc0f846fa36518c8c045a228113508183dc1a20c5055412e08c03c81a40b405602a81500a404101e00c405a022010807803a01c00c805c02600f00680240100070018008002000⟩⟩
theorem candidate00364_checked : Checked candidate00364 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9820851732480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00365 : Description := ⟨64, ⟨13, 0x149685641a9d40e416de3505734a554eb26210be7ca3b21c6cdcc6b73359878bda5a326d91dc8be4482098ff46343001688a044d42060f7055424a10d04601bc0d205b02d01540a805201b80c405a023011008403a01c00c805c02600e00680280100070018008002000⟩⟩
theorem candidate00365_checked : Checked candidate00365 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9822932107264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00366 : Description := ⟨61, ⟨13, 0x2f3b49a9ff4daa4c71c486fbae5c86da06c53569710a594dea570fc67c934219b0c585732a294348f044b2018f8c6c434618c8a704d82070f5849821409104601b40d205c02d01540a8036018809c04802200f007403801900780340100070020008002000⟩⟩
theorem candidate00366_checked : Checked candidate00366 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 9838037836032 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00367 : Description := ⟨69, ⟨13, 0x220109680cbd4de18ea272cb555a52d1155ca879380943462a1e10547cc3bf1ba4ca661f2f81750a1e4f4260117482a3cb1d78d9062e3001740b3853225411c08803da1bc0d006242e213f091823810805502a0130088033017009003e01d00e006c03001500900380100070028008002000⟩⟩
theorem candidate00367_checked : Checked candidate00367 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10129488494592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00368 : Description := ⟨68, ⟨13, 0x13e795e470a129019782b82da7ed115f32bb137c9434179cd4cd263930f9820bdc5d42c493d09844a922f8fe87903af1b28b384a0238110081c3781a30c484fc24c10c04601a80d206602d01540a803201880b804401d00e006c03201800b005401c00d004802000e0050020008002000⟩⟩
theorem candidate00368_checked : Checked candidate00368 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10167136550912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00369 : Description := ⟨59, ⟨13, 0xbfad4c291f44f8e2c4921c8dbe6d334a58fec3a59eabbd54ea4e50727c921887b3ff1ba0da06532d0944092637d1b28ba04a41ee0d185c424c0b504681a80c005b02b01540a804d01900a004601e00e807002600e004802000e0040018008002000⟩⟩
theorem candidate00369_checked : Checked candidate00369 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10485504246016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00370 : Description := ⟨71, ⟨13, 0x80cbfa5ea6ebe7513965b88da86aab4fd9f0bb555da88928690e43c1f84f9877e3739b48cd261f2ea1694a1e4f423d117482a3fa1c00d8c62e2ce14c88e04402040f686f03401890b884fc24610c07a023810806a02a013006603201700a004801f00e006c03001500900380120070028008002000⟩⟩
theorem candidate00370_checked : Checked candidate00370 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10610491277312 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00371 : Description := ⟨62, ⟨13, 0x52da296d5a6a134a5924b8259bab9d538a6952b282d1e6876431205cf0269b34219b0ca658828593dc9584161980c646022e8129081c31417109302440dc05f02e01580aa054026012408e03601a009c04801e00e807002400f004802000e0040018008002000⟩⟩
theorem candidate00371_checked : Checked candidate00371 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10655423889408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00372 : Description := ⟨72, ⟨13, 0x1630a59d00658b14884b3a79b7eda56adb505a52c785efacdd538a6b505a7011e687b42ea05cf9077c3749b3cd36685335994cb1051027912b08ba4111bf0d9066031a1800ba04a42070d185c421a05f02d815c0aa054026012408c03d01a009c04601f00e807002400e005002000e0040018008002000⟩⟩
theorem candidate00372_checked : Checked candidate00372 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10657504264192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00373 : Description := ⟨71, ⟨13, 0x9a94b12395145846bf59ea2e99705367dab6d23618afad5e2a6f4dc23f50f67c43749b28d0a66631c9664a7e50c27c92ac8ce4131ff8ec46da33218d0bec5ca29c14408e83ec1bb0d186102dc10707882bc13609104682300d405b02b81580a8031011007c03a01c00d806402000a0038010002000⟩⟩
theorem candidate00373_checked : Checked candidate00373 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10673811623968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00374 : Description := ⟨75, ⟨13, 0xa99d0064211c88a24259e08e9e72bb695ab4d41694accd5cca6e52aa7011e682e3e41e04ed07183679a10cd66533119760b1050d26191748864121fe8eb472e3641998c646002e814e094840e17109f049821a05f02e016c0aa05402600fc072027012008c03a01c00c804801e00e005802000e0040018008002000⟩⟩
theorem candidate00374_checked : Checked candidate00374 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10678576414720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00375 : Description := ⟨73, ⟨13, 0x27fb20d8e3c512132fd3752b95db40d5a69e34a5704b37573a9b93788f34171f20f0268432998e4ba858728693d88c24452090ff075e3971b10ccc6322fe1740a7050a23810387ac30e17109f049821409104681700aa05402600d8064027012008c03c01d00e006c032015007802c0100070020008002000⟩⟩
theorem candidate00375_checked : Checked candidate00375 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10679046119424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00376 : Description := ⟨71, ⟨13, 0xa99501212501c7ea3d39d44da36ad34fda52ae74de269127e8f243c2184f9876738d1b34d08669329988cbb0588286930c8ba3191740b3050c236110081c3da1bc0c485c427e12608601b80d406602e01540a804c01b00c806002e015009003a01c00c804801e00e004802000e0050020008002000⟩⟩
theorem candidate00376_checked : Checked candidate00376 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10679303077888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00377 : Description := ⟨69, ⟨13, 0x28091bd8494065e9cea26d1b569a7ed29573a6f12868783e61b34d0866932998e4c3e5d428693d098645d1fd0ebc6322e816708e04402070f686f031217109f849821808403701a80cc05c02a815009803601900b804801d00e006c03201800a804801e00e004802000e0050020008002000⟩⟩
theorem candidate00377_checked : Checked candidate00377 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10679311400960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00378 : Description := ⟨68, ⟨13, 0x13fb960c271fa6e9a72936adab6d3c6942f857049ba4799df0e686ce3429948c725d42c393d895245c2228ff06ce33318d0bf85ce29c14288e040e1eb0d1861c27c10a07a026c11a07502d015c0a804c02000f4064027011808803e01e00e006c032015006802c0140070020008002000⟩⟩
theorem candidate00378_checked : Checked candidate00378 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10682166681600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00379 : Description := ⟨69, ⟨13, 0x2c5f5359fc4b0638f08e83d3f69e74eec7543951c80df26d7356da78d264c8a404f8c77e39a1b30d0a6502ed964c8b84131bf0d886342fe1648a3047c1f00de068c30e17009f84281e60af04681a40d006602b815008003601900c405c02300f807803801900680280100070028010002000⟩⟩
theorem candidate00379_checked : Checked candidate00379 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10682389504256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00380 : Description := ⟨71, ⟨13, 0xb15500a57f0977503829b7eda66a0349d8f0c2d5f12e0966eaec51f27cd3828f843da1750247ca3be1cd0dd26d035019a8ca258d28813c894e45f2088f246fc36519a8bfc5cc25210387b83460db02d81680ae05602a812408c04301e808c04401f00f007401c00d00500240100040018008002000⟩⟩
theorem candidate00380_checked : Checked candidate00380 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10690739929088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00381 : Description := ⟨73, ⟨13, 0x24b120d8e14511f9ceb972bb699ab4d425c12cdd5d8a6e47c1f8cf026d034219b0c7261f2ea1624a1a4a923c11148243fa1f10ebc72e3651998c6460229c14189484702070f7062827c12604601a40b805a02b01540a8031012008803c01d00e006c03201800a803c01a00b004802000e0040018008002000⟩⟩
theorem candidate00381_checked : Checked candidate00381 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10714479591424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00382 : Description := ⟨75, ⟨13, 0x9ffcaf213afce750397dc20dc56d63585a74d215f32e0966eaec4df23e0f9477c39a1ba4da068531c987cba858927a12a48be40f1f28f307343811b40cd863a2fc1718a7050625211c081c3dc1a30a004882120f006b823411805b02d00f4064031011808803e01e00e807003601900c005401c00d002000c004001⟩⟩
theorem candidate00382_checked : Checked candidate00382 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10716492858368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00383 : Description := ⟨69, ⟨13, 0x291f3fd8e245c62470997a8bcf5d4ae436df3681b14d3c694b1fd54ea4e4de23110f67c8374194cb4653a28613f48c244b2018df46c43461990bf85d029c0f586ec3461870b884982140b5048823410206d03001540a803601900a004e02300f007403801900980400100070020008002000⟩⟩
theorem candidate00383_checked : Checked candidate00383 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10863461277952 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00384 : Description := ⟨64, ⟨13, 0x14968573a3dc82dc16a0b4a1730a554ec23d50be7ad3b21bacd6e66b329188cb4655923b910c7fa37c1998c686002e71688a0440c15509f049421a0f404d81e00ea05f02d81680a804001f80f405a027011808804201c00c804c02400e006802c0140070018008002000⟩⟩
theorem candidate00384_checked : Checked candidate00384 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10887849115648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00385 : Description := ⟨73, ⟨13, 0x293340792dc241d70e9d747b95dc88da869fb4a16fca534dd26991ee8613f11f1cf5a7813b11b48d6e669329188cb4655923b910c8243f81f10d8c6662e71688a7050c1ed0d186242aa13e09304301e807803501800b405402000fc078032014008804201c00c804c02400e006802c0120070020008002000⟩⟩
theorem candidate00385_checked : Checked candidate00385 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10887915175936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00386 : Description := ⟨78, ⟨13, 0x525a80d1da848be75d74e9c747b95dc82dc06d3b505a4cb04575a9553769a6463a17cfc87c63d69e04ec86ea3689adccd6650311968cab247722190487fa3971be8d906663001688a7050225210287b03461700aa84f824c10d07981e00d205b02a010007e031016808c04201c00c804c02400e006802c010007002000c002000⟩⟩
theorem candidate00386_checked : Checked candidate00386 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10887948206080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00387 : Description := ⟨70, ⟨13, 0x52527f11c4897423a0f4f3a75d3aa1d0ae356e036b9b1ad3c693264518e7e43e31ed8ec06ea3661940b4647722e112c80637d1b10bf859228c10287c03781a30c385c02a413f09304281e60af04b82340d206803301640a804001b00c806202e011807803801900980340100070028010002000⟩⟩
theorem candidate00387_checked : Checked candidate00387 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10888145281280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00388 : Description := ⟨70, ⟨13, 0x523e7ff35f8c1448a1cb09a7a03a99c72dbe6d33651a76d2263faff954ea4e4df21ecfc47ca3741b40c4c5a32a594009be494231112c7ea37d1b28d506682fd1720a704a41ee0de86182da12606c02d411a08c03a01800ac05501900c4050023011007803a01c00c804c012008002000c004000⟩⟩
theorem candidate00388_checked : Checked candidate00388 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10896747268352 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00389 : Description := ⟨69, ⟨13, 0x29352d48bec4bdea2eb86df3699a84bfe54da94941287b4311f88ec66e83681ad0cd86232d194f4a184f724891dc8903f81be8d946923321808a704a41ee0dd868c31412604601a40c005a02b01540a804901e00d4062028011007803a01c00c804c02000d004802000e0040018008002000⟩⟩
theorem candidate00389_checked : Checked candidate00389 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10898894815232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00390 : Description := ⟨71, ⟨13, 0xa50d0224b71da84a3ae1d40e476d4b4f5a48b7e582294d37c9a642f9f88f9476138f1b4cd74667327188cb4647722f910c8243f81f10e5c6fa3651998b4453828112907b834615a08583c81b206a03481800b605a01f80f006403101680a004602200c804c01c00d0058024010007002000c004001⟩⟩
theorem candidate00390_checked : Checked candidate00390 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10922240442368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00391 : Description := ⟨75, ⟨13, 0x93844ae1590647f33a81d12e5671f36f1a82b9a52aa75931c9103e51eccf0076837319acc7261f2d193d08ee45f22210b48263f91d80d306343001670a6c50626b11008183dc1bc0ab84fc24a10d04601bc0d205b02d01540a8037018808c04401d00e006c032018009803801a00c005002000e0050018008002000⟩⟩
theorem candidate00391_checked : Checked candidate00391 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10922447863808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00392 : Description := ⟨63, ⟨13, 0xbced26a7fd3758dfc60a1caf5975fb8e5b28d5f6912a9d4b29bd43b1f8cf926843361898a9650924a11ec8963f51aa0cd06362e414e094840e1bd0cf85b424c0d804882300e806e02f81580aa04701b00c404e024011007803a01c00c8048012008002000c004000⟩⟩
theorem candidate00392_checked : Checked candidate00392 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10928959523072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00393 : Description := ⟨62, ⟨13, 0x4245b84d5e6922e615d6a554dda6991ea85f3cd9c78dd86ba3441938c464431fe8e5c6fc3641998c686002d114e0a044a42070d185682480f206c826c0f0075034817c0b605a02000fc07a031016809c04602200c804801c00d0058028010007002000c004001⟩⟩
theorem candidate00393_checked : Checked candidate00393 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10956533071872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00394 : Description := ⟨71, ⟨13, 0xa9bd2867ed2708e244ba11d07a7e83ce9d34e7172537d1b84db16c83579a9ad244c89dc4e6e6ec3659a20cce64e22e112c8264031bf0d886342fe1648a304402070f586f03461870ae849021e0f206c82bc13606903401980b404001b00c806202e013808c04401900680280100070028010004001⟩⟩
theorem candidate00394_checked : Checked candidate00394 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10956730147072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00395 : Description := ⟨76, ⟨13, 0x136a92c45de28912c79c3ae5caeda66ad3509928b82550a9b94ac8623f19e04da068433618e4c3e53e29394349e64aa23c11148243fa1f10e5c6ca34b1998c6460229c141894840e1ee0ea062827c12604601a40b805a02b01540a8031012008803c01d00e006c032018008803c01a00b004802000e0040018008002000⟩⟩
theorem candidate00395_checked : Checked candidate00395 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10972177629184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00396 : Description := ⟨69, ⟨13, 0x20c8f4e75cba25c72da66ad350931c8783f19eccec66d034219b0c7261f28691e08883b01b28d306323011670a0c4d6252110081c3dc1bc0c5055c27e12604601d00d206602e01680ac05502a00f006202e012008803c01d00e006c0320180078034018009004001c00a0040018008002000⟩⟩
theorem candidate00396_checked : Checked candidate00396 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 10989084868608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00397 : Description := ⟨61, ⟨13, 0x271b0f77f6bbc1b82d3f67b329d8f6b4b510a42d1528484099e00e9c6eb35b19a4bd85a12ba155c9844ac1be0c6853e26d11b087440c1d20c485c424a10c07a02a80e406a02a014009e04d01d00c806002a014809803801600980380140090038008002000⟩⟩
theorem candidate00397_checked : Checked candidate00397 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 11044276764672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00398 : Description := ⟨62, ⟨13, 0x4a2a43cee572eb8adb82d4467c31ed76893f48822a50907b03bd9d24dd666e2f6155c9844a723b917c8223df1be0bfc53e26d11b08183a418909e04942180f406d82fc13c07202d014008603d01d80e806002a0130088040016009803801a00a0048008002000⟩⟩
theorem candidate00398_checked : Checked candidate00398 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 11180390318080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00399 : Description := ⟨61, ⟨13, 0x2b331887bd3849b8ed2b654aff9798b4b4d225550ee7e43bf1d38e606e532a9888aac53c26f12a88bc3c61bd8b9859626d12a08243721700ac048c2180f306d82e414806e02f014009404901d00dc06c030017009804a01f009004401a0090040018002000⟩⟩
theorem candidate00399_checked : Checked candidate00399 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 11414699294720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate00399_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch003

module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch016
open Papers.RationalityTen GraphCandidateCoverage

def candidate01600 : Description := ⟨71, ⟨13, 0x8e4451612cfd47a8ba89bd6dbf6adb4a55cca6f52aa7011e487b4309f30f306e935b9a14ca65ed2c415c4a1845d2098ff475a37e1b20cc86343001740a7050c23610387b43761a30c485c42aa09403e815c0aa054026011407202a010807c03a01c00c805c02401000700280100070020008002000⟩⟩
theorem candidate01600_checked : Checked candidate01600 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27167082741760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01601 : Description := ⟨80, ⟨13, 0x1539a25ca8a44d1cb8a2c44e12afd47a8b911becda86adb4a1798b50572a9bd47aa0a4dfa3c90f68143cc1d88e326d235b9a14ca45ed2c415c4a184da24891788263f81f08f247643631990c686022e714e0a1846c2070f686ec34615508603d00b405702a013007802a011008403e01c00c805c02401000680280120070020008002000⟩⟩
theorem candidate01601_checked : Checked candidate01601 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27168122929152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01602 : Description := ⟨76, ⟨13, 0x13208e446a228911284b3f51d44e576f5b569a52c4a5c1ab995a4a6e52aa8f13808f24309f30f026b7342194cbda5882b894349b64c322e90487fa3e01d68e5c6c833318c8c005d029c14308d840e1ed0c485c42aa13e09302500b805502a013007202a012008403a01c00c805c02400f007002c0100070020008002000⟩⟩
theorem candidate01602_checked : Checked candidate01602 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27171243491328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01603 : Description := ⟨74, ⟨13, 0x4c823910967ea3ed1e9cf1e75137adab4d296252b994aa9c04c7a3c91bc878430a120f986b7342194cbda5882b894349b64c322e8ff475a36418c8c005d028613488d84402070f686f03121710aa84fc24c09403301700aa05402600e405c02a012008403a01c00c805c02400f007002000e0050020008002000⟩⟩
theorem candidate01603_checked : Checked candidate01603 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27171507732480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01604 : Description := ⟨73, ⟨13, 0x26411bc895c259f68f4e78f3a89bdcd5a694b1295cca554e023790f08483e61c60d0865331097b4ae250d27a136c98645d1fc8d906983191800ba04d2238110081c3da1bc0c485c42ae13f09302100e206602e01540a804c01c80b804801d00e006403001700a804801e00e006002000e0050020008002000⟩⟩
theorem candidate01604_checked : Checked candidate01604 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27171516055552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01605 : Description := ⟨67, ⟨13, 0xa25c509f8ce9f720b895becd586942e0d4d8a0a40a1f24ec874f38c9adcd046522f69620ae250d23c11787fa3e01d90ccc5ce28113508d834418a0aa84f824a10d07a029c0ea06b02f81680a804c01e80cc05a02a013808804201c00c805c02400f006802c0140070018008002000⟩⟩
theorem candidate01605_checked : Checked candidate01605 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27172217618432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01606 : Description := ⟨75, ⟨13, 0xa9cd12e39714484abf51d72e5772237d9b50d5a6942e015caa6e50526fd1e48143f19e04ec47193691adcd086522f69620ae250d23c11788243f81d90d8c6663191808b9c53828611b081c3da15509f04982180f403981700b405402600f007602a012008804201c00c805c02400f006802c0120070020008002000⟩⟩
theorem candidate01606_checked : Checked candidate01606 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27172283678720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01607 : Description := ⟨80, ⟨13, 0x1539a25c89a3970957ea3ed1ea0e567223891becda86ac34a16a0ae550526fd31e8f246f21e90287803b11d38e326d235b9a08ca45ed2c415c4a1a47822f104c7f03e11e48ec86c63011738a6c50c26911b08803da1bc0d1055427e12508603d00d605a02a0130078033015008804201c00c805c02400f00680280120070028008002000⟩⟩
theorem candidate01607_checked : Checked candidate01607 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27172415799296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01608 : Description := ⟨72, ⟨13, 0x1523a27500e3730de8343f69e9ceec71ab89dbdadae6c6b569a4cae44dea5612028783e59d80e987233661a10cd86502c995cca1a4782018f8c75436218c8a304ce23e0f806f02e015209f84982140f305d825c0e206903301700b205401b00c405c02c012007803801900780340100070028010002000⟩⟩
theorem candidate01608_checked : Checked candidate01608 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27172513784064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01609 : Description := ⟨69, ⟨13, 0x2c5944b8893f51d3ae526fb356da50be15c1a955478a0a47921850287c73cc1df0e326b73429948bda5882b8936c7fa3e01d90ccc6343001738a7050c23610387b43461890aa84f81e807803a81680ae054026010007a02a011008403e01c00c805c02400e006802c0140070020008002000⟩⟩
theorem candidate01609_checked : Checked candidate01609 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27174364053504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01610 : Description := ⟨73, ⟨13, 0x2f4762fa9c525a89d406960c37a0d0fda79d3c85dd8ea87373951bdad8d6adb4995e49bb4ac240508c7c63bf1dace466d134299acca05932b993748b84131d50df863428c13388f83e01bc0d1861c2e015209f83cc0e206903301640ae05402000c405c02c011807c03801900680280100070028010002000⟩⟩
theorem candidate01610_checked : Checked candidate01610 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27174594158848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01611 : Description := ⟨70, ⟨13, 0x54a688b2268e2c3aa160fd179dbc7ddcae366f5b699b24d5d693ad415dea144ed23ed0ca8494079d80e2a6d035e1a1cca25ed26d12448f04131f08f246fc36518c0b984d41ee0dd868831412506d827812e09403f81680ac055023808803c01d00c805c02000f00680280120080018008002000⟩⟩
theorem candidate01611_checked : Checked candidate01611 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27180992102656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01612 : Description := ⟨72, ⟨13, 0x17aba51d11657f2268e2c4d61d50977a8bcf9dcae446f5b6fdb24d44693afa56a0aef52fa85138287b434203cedc7153749af0cdc6512f6943092245f2098f8479237e1b28bfc5cc29c10386ec346189086036c13c09403e81680ae055022808803e01d00c805c02000e00680280120080020008002000⟩⟩
theorem candidate01612_checked : Checked candidate01612 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27183138537728 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01613 : Description := ⟨69, ⟨13, 0x2c4752da0142c1e5ee4071537c1abad47693b1297d2b4c512a7693828fb42d203cf9474a3681a1ccd465128693f49ba4a423c0f7872e37e18c0c0c5cc28c13608cc39e1a20c384f824a10a06d828413c07b03a81880bc05a02a80f4076023011007803a019007803401600a0040008002000⟩⟩
theorem candidate01613_checked : Checked candidate01613 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27187702931712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01614 : Description := ⟨73, ⟨13, 0x2c47447964c3a6166fca7973b8dd4ce256f83645ac4d4669131297d2a6c51e275d1f685a4079f28e9e68233597b4b2050026312d48f64621f00e5c6fc3161810b904fc26a11987b83ba1a40c305b427c125086836014209e04601d40ca06202a80f4066031011808803a01c00c805c01600a004000c004000⟩⟩
theorem candidate01614_checked : Checked candidate01614 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27187753257216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01615 : Description := ⟨77, ⟨13, 0x2a754a4a20c89a38b12f86cc0b9fa2f3b772b91dc1adfc6e136a5b30d5e6a2b4916a0aef52ca80d2b08fb432a03cee27373931bb0da66c234419bcc9c5ed2098f8479237e1b28c68602252110081c3dc1bc0d1862824810b079036416409e03481980c805a01880b805802200c805c01a00a004802000e005002000c004001⟩⟩
theorem candidate01615_checked : Checked candidate01615 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27193854066944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01616 : Description := ⟨73, ⟨13, 0x244d1c5897c36605ce0d6e136a5abcd456922d415d0a524ac23e10c481239b9bb0da66883379938bda58d27b929c8263f81f08f2475a37e1b28d24634301129088040e1ee0de068c31412408583c81b20b203481980c805a02180f007203501880b805802200c805c01a00a004802000e005002000c004001⟩⟩
theorem candidate01616_checked : Checked candidate01616 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27193862455296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01617 : Description := ⟨79, ⟨13, 0xaca48ce064fce79c3ba1cbee2d7083715b58d616a43485698aec52b28192b88f84312048ef874a39a1ba4da06853361884bda589279903c7ba3cc1cd0e046d033618e8c105c629c14189a84a423810387b83a81a30c50500244109078035c11807b02d010c07a03b018808803e01e00e807003201800b805402200d002000c004001⟩⟩
theorem candidate01617_checked : Checked candidate01617 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27194134889472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01618 : Description := ⟨72, ⟨13, 0x1627a4b512665b14d859bf29e4eea671d3589a8cd2262329a93ae8fb4221f28ed671534119acbda590284935c98c49423d91888264001d50df86683161810b904fc26a11987b837a1a40c305b42a4125086836012808c03881940c405902a811c08a033018808c04401d00e006402e00a004000c004000⟩⟩
theorem candidate01618_checked : Checked candidate01618 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27196074756352 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01619 : Description := ⟨73, ⟨13, 0x2a754568e2c512064fd175cb91dbf8da96a2b491700ae853728212b88f440a1f8cec27163699ae8cde64e2f69634a1a4782090fe075a3971b28ccc63230114e0a044d425211b081c3dc18a0ad042c1e40d903981a40b805a01e00ec07203101680a804802200c805c01e00d0058024010007002000c004001⟩⟩
theorem candidate01619_checked : Checked candidate01619 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27206608945152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01620 : Description := ⟨77, ⟨13, 0x2a534498df437a0d703f7edbd6ddeeec2719b8bdbd0daf6cb359da96d20577a5611f68783f19d80e987153681a10cd85ed2c814348f03f51f08ea86ca3191808a6051e26612a891044620a0f886fc33c18d0b6058c28412908403bc1ac09704a02300e807103480c405c02c012008803c01d00e006402e00f0068024010007⟩⟩
theorem candidate01620_checked : Checked candidate01620 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27206872990464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01621 : Description := ⟨72, ⟨13, 0x1627a2b444a064fd175037f1b84d5e6922f99706a5551e28212b88f442fa050f9479b38b1bb0d7468832717b4b1a4db22f8ff47c03ad1cb8df866631a1800a7050226a12908d840e1ee0d185682480f206c81d40d205b02d00f407203101680a804602200c805c01c00d0058028010007002000c004001⟩⟩
theorem candidate01621_checked : Checked candidate01621 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27208689319936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01622 : Description := ⟨65, ⟨13, 0x298f1287f63f35d7ce386e236a1aaacaa5a82aed4b290c3f09db8dce6d23589680a1e4fa23d10547ea3e11c00d8c68c3171808a7851221f10207b439e1a00b8854824610c07a024011c08303a01b40bc05902a0134096033014009003e01c00b80500240090038008002000⟩⟩
theorem candidate01622_checked : Checked candidate01622 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27225031196928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01623 : Description := ⟨64, ⟨13, 0x13807d83cedd76e416e0b61dab0caa54323d51b485e3f29d90dd66822f69564a1a4f723b104c7fa37c1a48a044d421f103074834418a0b8855424a10d07a024010a083035817c0a804d02580d406602d013809804201c00c805c028013009003c0140070018008002000⟩⟩
theorem candidate01623_checked : Checked candidate01623 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27225099403264 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01624 : Description := ⟨67, ⟨13, 0xa48c75a264fb57983905b78d876a0b4a5600a5046f9d90e366e6335994cbda570279136c8263fd1cb0d246343001740a044d421f10307b83a41710aa849421a0a104802140de05b02a815009a04601b80d405a026011808403a01c00c805c02801300700280100070018008002000⟩⟩
theorem candidate01624_checked : Checked candidate01624 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27261573070848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01625 : Description := ⟨68, ⟨13, 0x152ca48d0063b715c7e83ee9e5eea56f8b561a52c4a582a9713808da42d1f20ed66cf3589a08cd66532d115b8a1a4fd26e91848263961bf0d185d028c136087c3d61cf0d1061c2e2152092828412006d03581780b205502a012c066027011807403801900a003c0140080038008002000⟩⟩
theorem candidate01625_checked : Checked candidate01625 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27291637784832 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01626 : Description := ⟨69, ⟨13, 0x244d12f84abf9dc88da86c3b56da50be55a8294937e91147ba054f307623691a14ca45ed2d113dc92045e2098fe07c23c91b18d246343011738a7050c21f10387b43a41a30aa84301e809004181680ae05402580f006a026011008403e01c00c805c02801200680280120070020008002000⟩⟩
theorem candidate01626_checked : Checked candidate01626 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27296971948032 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01627 : Description := ⟨68, ⟨13, 0x152ca48d0066ad1457e83cbde48ea56f8b6f1a52cae537a97138085a4221f20ed66e63679ac4cd66532d195cca184fd26c11848263461990c685d028c13608183d61cf0dd861c2e2152092828412006f03681780b205502a011406e027011807403801900980400140080038008002000⟩⟩
theorem candidate01627_checked : Checked candidate01627 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27356062294272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01628 : Description := ⟨70, ⟨13, 0x589a7090ae79dba7dc82e256e0b61da50cae5f2ae0d3b08f542f2054f927643a79bacca45ed2d195c4ab24f723b91787fa3e01be0d2466631a1738a044d42060e906282aa13e09284341e809003a817c0b405401e80d405a027013008804201c00c805c026012006802c0140070018008002000⟩⟩
theorem candidate01628_checked : Checked candidate01628 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27365491146752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01629 : Description := ⟨69, ⟨13, 0x270912f84abae1caee446d4361da50cae5f2ae014a49bf47ba054fc47813b11b48ca45ed2d195c4ab24f723b91788243f81b18d246663011738a7050c1ed0e9068c2aa13e09304301e809003981800b405401e00ec06a028013008804201c00c805c026012006802c0120070020008002000⟩⟩
theorem candidate01629_checked : Checked candidate01629 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27365557207040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01630 : Description := ⟨70, ⟨13, 0x5e769274038e2437e0d0eba71ab89db80dae69332b94b29bd4ac231d0ca7e43e59d80e986ea3661ac4cd86502d195cc8ee4031f18df46c4346146099c40a1f00e786f03461700a904fc24c10a079825c12006d03481980bc05902a00d806202e016007803801900980340100070028010002000⟩⟩
theorem candidate01630_checked : Checked candidate01630 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27365787312384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01631 : Description := ⟨67, ⟨13, 0xa49d12a5bf0e585bbbc5d86df16d33619a44bfc52ca8f53a88654249f80ec06d035899b0bda5a328492508e63f51f08df46ca35419a0c6c5c827e13508183dc1dd0de86902da15206c025c12008c03a01940b205602a811c082031011007803a01c00c805c026009004000c004000⟩⟩
theorem candidate01631_checked : Checked candidate01631 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27387267909888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01632 : Description := ⟨72, ⟨13, 0x1490a26d00a6ad2d489c4389e5ef24775b8d5be2dbc6c5b51da4ebfe5a8297d38285a4221f28ec06e63681af0cd46512d194309fa4d824891dc8264031f18d446062e614609b040c1cf0dd861c2a4125085036c14209703781780b405902a811406e023011007803a019009804001a00a0040008002000⟩⟩
theorem candidate01632_checked : Checked candidate01632 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27389297959168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01633 : Description := ⟨71, ⟨13, 0xa48d12a6b3137872bcb9e4eef175338e9be2dbc6c33519a44bfe537a9713ac85a4221f28ed66e635899acbda5a3280135c92846220990006a83341810b904fc26a10307b83ba1bd0c305b42a4125086836014209004601bc0ca05902a811406e031011808803a01c00c805c02600a004000c004000⟩⟩
theorem candidate01633_checked : Checked candidate01633 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27389348284672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01634 : Description := ⟨66, ⟨13, 0x52728cf12780bbf79e64ee972cb8f5c24dc46c634fd442868417a068efc7303739a14cd25f02d01640ab64ef257905478c38014c8a244a8233102073c3781890b884fc24610c07a02a00fc06a03101840bc05402680e806402e01480a003e01c00a00380120070028008002000⟩⟩
theorem candidate01634_checked : Checked candidate01634 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27536949002496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01635 : Description := ⟨65, ⟨13, 0x29390f77f0bcf9de0e566e0b4fd990a51510a50521685c4099e00ece6eb35b19a4bdc58d2ab93c89844ac2098df063429b14308d840c1d20de06242e213f09284301e808503901a80c2054026811807403201500a404c01c00c805802801300700280120070028008002000⟩⟩
theorem candidate01635_checked : Checked candidate01635 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27536951148544 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01636 : Description := ⟨65, ⟨13, 0x28cf1277ef3bb5cb2e126e234fd990a51510a0bd02e77e3981b9cd0a6692f81758b405892ad92a082a3fa1e30e0069629912a08e04081d40de06242e213f09184301e80a803f01a80c2054026811807403201700a405001f00e006002a01400880380120070028008002000⟩⟩
theorem candidate01636_checked : Checked candidate01636 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27536957390848 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01637 : Description := ⟨67, ⟨13, 0x89643f5ea6eed72cb849b50d55656b1914aca20486a3150f08173bf1cc0da45f02eb15c8a1e4f326292a082a3fa1e30d8c6963171808a644a82380f687503781a00b884fc24610c07a023810806102a013007403301700a404801f00e006002a01400900440120070028008002000⟩⟩
theorem candidate01637_checked : Checked candidate01637 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27569169645568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01638 : Description := ⟨73, ⟨13, 0x2a8d4718e1440dea6f0c776b965c24dd76b035118c2b05576287521a878415205cefc7303809ba4d0666e2f81758b1250f26012a082a3fa1e30ebc72c36518e0bfc53225411c07503781a00c485c427e123086036c0fc06102a811808803a01700a404801f00e806002a01400880380120080028008002000⟩⟩
theorem candidate01638_checked : Checked candidate01638 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27601365123072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01639 : Description := ⟨70, ⟨13, 0x52468911328723f9dfa2f30781bbc1caee416f5b755b0ed41694a97141c91147da16905a81a3c09dace2a6ff35899acca65ee2d113088243331800ba053821f10387b834617109f049821a0a104a02400e006302d81540a8038015808c03a01c00c805802800e005802000e0040018008002000⟩⟩
theorem candidate01639_checked : Checked candidate01639 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27605034139904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01640 : Description := ⟨71, ⟨13, 0xa4ed13e2650e47f3bc0dcaedd56a0b4a566aa50503a4451f085d416a05cf0276838c1bfcd6866b32997b8b4458d27913089584121fe8eb46923331800ba053821f10387b834617109f049821a070031816c0aa05402300e4070035015808c03a01c00c805802800e005802000e0040018008002000⟩⟩
theorem candidate01640_checked : Checked candidate01640 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27605042528256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01641 : Description := ⟨73, ⟨13, 0x293944c8e1449e1c304c7f53cc9e0aee972d38f5c16df06e93631a7ed295a7a4350d082f40d1df4e6a69e334994cb4c590277930895e4161e40e506ca2e814d0a244a023310e881c39e1a30c485c4278126086024c0fc06a03101780aa05401c00c805c029010007403801600700240100070020008002000⟩⟩
theorem candidate01641_checked : Checked candidate01641 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27605500723456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01642 : Description := ⟨77, ⟨13, 0x292d31f8edc5161f30c87e8bb51c82e0c6f5b505a52c495b52c154dea55511a7c91e885f3ff1d90e6c6b7335994cbdc5a22c694309b84c2247904c7fa3c71d68e586fc33218d0c005d028112888d843e1ee0dd85c42aa12508682500b605502a00e405a02a011808403a01c00c805802801000700280100070018008002000⟩⟩
theorem candidate01642_checked : Checked candidate01642 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27613760389120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01643 : Description := ⟨60, ⟨13, 0x11417e33e5de76ef0720b831becdc16c3b5c54d68f0460a19503476b39b1c80dd66b134d97b8b4650c1e38df063425110306ec31417109f049421a0f40538240104075036017c0a804a01e80d004e01c00c8058026012008002c0140070018008002000⟩⟩
theorem candidate01643_checked : Checked candidate01643 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27632852861184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01644 : Description := ⟨63, ⟨13, 0x89e3f19c82df66b8b3156d4b1f460a0c0fca76439b1c64dd66b734d9a08be05a52c41558a144c523d10407fa3cb1d90e0062e28111b06ec3141710aa84f821a0f405b029c0d805f02a013009404701e80d006602d015009c04201c00900400160070018008002000⟩⟩
theorem candidate01644_checked : Checked candidate01644 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27645737779200 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01645 : Description := ⟨69, ⟨13, 0x2a7339b8ddc52e1f4fc87abbaedc70def6d43635adcb4f57aa9a544891047f21d4fca76e3901b48b0a50b26091d882c3f51e40ed46c633018c8c0453e28911988183da1b90d105c42a413c08603d011e08404101d00c405902a012808e0340128080038016009804801e0090038008002000⟩⟩
theorem candidate01645_checked : Checked candidate01645 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27645801693440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01646 : Description := ⟨70, ⟨13, 0x54e639714b87d3f51eaeebb72237d9b50d6e662ad3d5caa6951224411e48753f29ec4ec47193691adcb1050b26091d882c3f81e40ec86c633018c8c0453e28611b08183da1b90d105c42aa13c08603d011e08202a013009404701e00d00540250108080038016009804801e0090038008002000⟩⟩
theorem candidate01646_checked : Checked candidate01646 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27645801758720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01647 : Description := ⟨63, ⟨13, 0xa5546edf44ebe6f9b6a1adccc55a7ab954d2a244872300fc277d39a9c74da46842ab13148f43ae1b18d3066030112a08e04081ed0dc86802e215709e04301e80a204782100e8054026012808e03c01a00b8050025012008003801800a80480180090038008002000⟩⟩
theorem candidate01647_checked : Checked candidate01647 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27645808001024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01648 : Description := ⟨66, ⟨13, 0x46edfd2fa27a43af9be6da86b9b3155caa244872300fc273538e9b48d3a6842f81694aac50a26291e875c3631a60cc860229912a08e04402040f686802e215709f84301e80a204201d00ba054026012808e03c01700a004a02400e006002a01200800300120070028008002000⟩⟩
theorem candidate01648_checked : Checked candidate01648 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27646076403712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01649 : Description := ⟨64, ⟨13, 0x11bd7a438f5be4d73662ab9d56aa244eca5d925676739a9c70dd469d34217c0b4a55628513148f43fa1d78cc86022e81678a6450425411b88243aa1a00ac04fc2180f305102100dc05d02a013009404701b00b804a02400e006002a01200800240100070030014002000⟩⟩
theorem candidate01649_checked : Checked candidate01649 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27646571855872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01650 : Description := ⟨70, ⟨13, 0x54ce89f33a8de452e1bafc97abbce1e0ceed71f37b9b4ad8a6b734a55e4a69507256d0ea8303811b3cca65852ac142c9f44c125790588003aa1b20d186603191740a7c4a21b90d106282e213c086823c108071036817c0aa05402380d004e0250100074038016009003c0100070018008002000⟩⟩
theorem candidate01650_checked : Checked candidate01650 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27697382195456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01651 : Description := ⟨76, ⟨13, 0x17aaa27cad637912686ec259f36f54782bbb5d44e5a6f73629adcd29624afbd5e4a5c507270118a8774179f30efa7023299614ab0510277930895e45d20b10007543641a30cc06002e814d094040e1ed0dc868c31217109e049811e08403f01c40da05502a00d005c025010007403801600900380100070020008002000⟩⟩
theorem candidate01651_checked : Checked candidate01651 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27699528630528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01652 : Description := ⟨67, ⟨13, 0x8de452e2570967e43d5de6eea26c6b5b9a52c4757929a53808fe43a9f30e2a7023299614ab050b22e90588003aa1b20cc06323001740a7c5122330f686e43441890b8854827809404782100f807103101640aa05402381100680250100074038016009003c01c0080038008002000⟩⟩
theorem candidate01652_checked : Checked candidate01652 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27712407240960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01653 : Description := ⟨69, ⟨13, 0x237af487763965c7ae126f93581a56bb3573aadd3b497640b1df8ece73038e1a0ccaa5f0285131495249122f10547f43c61d78c705cc2cf14c8a084a82370ea86802e015809f848c2180f306d828810806e02e813008e03a01b00b804a02400f806002a01200800340120080030014002000⟩⟩
theorem candidate01653_checked : Checked candidate01653 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27714100150272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01654 : Description := ⟨69, ⟨13, 0x28692b88e1425de64e5d71eb7c1af2d44693b1257d2b4d51f27cd3828684079ff0ef670234e19b8ca259028813bc9844a422f90446fc36519a8bfc5cc29f14488cc39e1b90c484f024a10c06d82780fc07b03901880bc05a02a80f4074025011008003a01600700340140090040008002000⟩⟩
theorem candidate01654_checked : Checked candidate01654 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27733160657152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01655 : Description := ⟨66, ⟨13, 0x4e1a250fde7d13d4dd7cda86c532ad8c8a5251223010f07e139a9b48d686842f81680b145722ab143c9e64c523d0d8c60229912a08103da1d40de06802e215709f84301e80a803a01b40c2054026812807803501700a405002400e006002801200880300120070028008002000⟩⟩
theorem candidate01655_checked : Checked candidate01655 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27774925422592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01656 : Description := ⟨67, ⟨13, 0x8e944c9fd8f9f7983729b30d2c5b52941446973486230905a79b38f1b90d6468832b17c0b4055b27910407fa3cb1bd8d246663001740a7850224f10f88103dc1d20b885682500f206c82f014207002d813408c03d01c00dc06a02d01580a004c02300a0038016008003800c004001⟩⟩
theorem candidate01656_checked : Checked candidate01656 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 27811058499584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01657 : Description := ⟨73, ⟨13, 0x2f5764baa752825711be892c36a12ef3376d38e5b8ed8f6a034ad7f2be95802bbd4bea144e0a4290ee8473fc1f90efc7343819b94cd46552c813bc94848e22f8fd475437b1b28d445fe2e6111082437217009183cc1b607e03d81d00e205b02b0134084037017009404601f00f003801a009004000c002000⟩⟩
theorem candidate01657_checked : Checked candidate01657 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28076495388928 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01658 : Description := ⟨66, ⟨13, 0x4ae23850d184bbb9dc76df26e3b501a56bf95f4a8f93d69c143da16903a7e43be1cd0dca6a03351954b204ef25212388be3941bd8d9466a2ff17309f847c2090e785c02460f306d82f014207e03d81940bc05b02b013408403d01c00dc04601f00f003801a009004000c002000⟩⟩
theorem candidate01658_checked : Checked candidate01658 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28076759630080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01659 : Description := ⟨75, ⟨13, 0xaa5d27689f4338994391fdaed76de3505a52c3258e2c014dea50503a7c92168f842ea11d02e7fa3c01da0e307013731ad0d3a66b3299684b1a51027912b09263fd1d68d246343001740a7c43a2060f706e42e212508681bc0b605502a013408c03901b80d4052025011807403801300700280100070018008002000⟩⟩
theorem candidate01659_checked : Checked candidate01659 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28077621084160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01660 : Description := ⟨78, ⟨13, 0x591aa6149aa224c2e5c112886c4335fdef5179c3bc9db2ebd71cb7e1b86d8a6a1348d7f2aef52ca80d3da90c43d9fe4fc46e836819b0b3e50c27d12c891a4791fa8ee073037f1a30cc86022e514e09484422030dd868c31416e09303c416408c03a01b40ac0540268108062028011007803a01c00c8040012007002000c002000⟩⟩
theorem candidate01660_checked : Checked candidate01660 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28078763938048 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01661 : Description := ⟨74, ⟨13, 0x527689f2ef8f0c49a1bb0af7f6bf39e66eed75db8f9bdcdd26c53505a52aff537297141c9d9485a1e8fca69e335994cb42590277930c95e47620b10007543941be8d186323001740a7c43a2060f706882e213c086824c0fc071036816c0aa05402680e0052023010007403801300780380100070018008002000⟩⟩
theorem candidate01661_checked : Checked candidate01661 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28081781768448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01662 : Description := ⟨74, ⟨13, 0x5e4ec3b523a48516281b1db875427dea2ef375437e5b5cd926a3b4ad7bcbcb582ab914bea144dca4050f685a40e9f18ec07343919b30d7866a32a9688a1845c2098e586fc3621818b985381f00dd868c30e17008503cc1b60c505d828412e07a02b8108080036011807c03c01900a004001a00a0040010002000⟩⟩
theorem candidate01662_checked : Checked candidate01662 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28110850957568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01663 : Description := ⟨72, ⟨13, 0x1630a9b523e5911ce8ae448dfa6f5079ebbb5d4ae56721b7cdb56d8a6ac34f17deaf552728891ba87a3e41e00d9c6822d1164ca1a4fd25791848264031da8d9c68c2fe14d87ac3781a20c385c427e12508503d016a08d03681ac0c205401980c8052027011807803801900a003c0140070028008002000⟩⟩
theorem candidate01663_checked : Checked candidate01663 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28116242145536 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01664 : Description := ⟨71, ⟨13, 0xb10524a591142898bf15e5eee9752b901bb4dab6c63561a78bef56a29b14448f042d2068f907043671a08b4459328693f495e4611ca8d9c6662fe14608cc43e1eb0e7868830e17109f04942140f4053828411a07503581880bc05401e80cc064027011807803801900a003c01600a0038008002000⟩⟩
theorem candidate01664_checked : Checked candidate01664 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28116506386688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01665 : Description := ⟨72, ⟨13, 0x1633a9cd23a58b1cb8923f8dfa8f3e7783a89ca8e446fb36a1b0ed5b69fafbd5eaa4e486a3f90d081a3e61df8edc7203691ac4d0a6692d115c88ba4131e48d8c6342070f686f03461890b884fc2180f405a82400d4066030815c0a803201700a403e01c00c805002400e005002400e0050020008002000⟩⟩
theorem candidate01665_checked : Checked candidate01665 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28120527732992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01666 : Description := ⟨74, ⟨13, 0x58ce9392b5893bfa9f90f32774ba89c9ee3d6eeb6a1b18d5b69fafbd5a890d47f21a10347cc3801b48d3c6853349698b0a4ef25791748223c91cc8d8c63429a14488cc43a2070f6873c3461890b884f02180f404c02100fc06a03101780ae05401e80c805c029010007c03801200700280120070020008002000⟩⟩
theorem candidate01666_checked : Checked candidate01666 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28120796135680 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01667 : Description := ⟨75, ⟨13, 0xb184b22262fe77e9bcf5ddaea57293769b56d5b69e2f7d5a8a51488a3cd0ba8173e41df0e687043671a14bac5a22c393c49504611fe0e546ce34b1998c685fc29c14288e043e2070f587503461870b884f82140f404681d40ae054026011807a032013808c03e01e00e006402a014008802c0140070020008002000⟩⟩
theorem candidate01667_checked : Checked candidate01667 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28120807645184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01668 : Description := ⟨73, ⟨13, 0x2c6749c962bf8dfa8f3e7783a89ca8da86adb4fd7bea514a0a4351e485c4099f30efc7673691ad8d0a6692d11620ae44f225611748263c91b18c6850c23610387b43a41bc0d186242e213f08603d00d4066030815c0a804c02300c805c02a014809803e01c00c805002400e005002400e0050020008002000⟩⟩
theorem candidate01668_checked : Checked candidate01668 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28121064603648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01669 : Description := ⟨68, ⟨13, 0x12b5893bf8dddaea272a36a1ab6d3f5efa94521a8173e61df8da46853349758b4457225411748263fa1e48d8c69631a11c081c3da1d40de068c31217109f84301e808403f01a80cc06102b815009804601900b805201f00e006403001500a004802200e005002400e0050020008002000⟩⟩
theorem candidate01669_checked : Checked candidate01669 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28121072926720 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01670 : Description := ⟨78, ⟨13, 0x54a69274488e2c4be1c90c87f3bf45e98f3b7783b51c6cdeb6d3361dab4d42694abbd4b2a0e4f924451f6876432a068ffc76038a9b40d62684336194cb4448f1cb0d946643191808ba053825210f881c3dc1bb0c505c424c09704a02400fe05c02b01540a8047012007803a01c00c805002000f004802000e0040018008002000⟩⟩
theorem candidate01670_checked : Checked candidate01670 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28144253862144 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01671 : Description := ⟨79, ⟨13, 0xa98526a89f1c5897c392190fe77a63b51b4cd5a6a134a5864ae8529281d3e491147c21d90c48173ff1d8ce306d035a1a10cd86532d116349ee4ac2478fe075a3961b28d246643191808ba053825210f881c3dc1bb0c505c424c07f02e01580aa05402380f0072035012007803a01c00c805002000f004802000e0040018008002000⟩⟩
theorem candidate01671_checked : Checked candidate01671 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28144262250496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01672 : Description := ⟨71, ⟨13, 0xa5951323bd0e17e53ba5cbadf06e93631ab0d41694ac054d88fb43d216903477b34f1a08cd66532d316409de4c3257904472837e1800ba053e27e11988743dc1cf0d105c4278125086828412607e03581940c405e02d81540a803d01c00cc052023010007403800f00700280100070018008002000⟩⟩
theorem candidate01672_checked : Checked candidate01672 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28150895509760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01673 : Description := ⟨76, ⟨13, 0x1144896439a194f38779395dbbed5a6a1348d7feaec537295940c9ef488a3e10c48123f19e04dfe6d034219b0bb252728693cc94c4922090fe87c43b11c98d2c6663191808b9453828312908e84421d40c505b827c12607882300b805602a010c070031012008803c01d00e0064030011007802c012007002000c002000⟩⟩
theorem candidate01673_checked : Checked candidate01673 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28152046817280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01674 : Description := ⟨79, ⟨13, 0xa94d24e8911c58a244be1c8fe77e8bcedde0e5771b37adbaada66c3b569a84d29577a9b94b2a0e488a3ed0ca81a3c09d80e2a6ff3681ac4d0866c3299688a1a4121f10d946663191808ba053825210f881c3dc18a0b884f824c09704a02400e005c02b01540a8038012007803a01c00c805001e00b004802000e0040018008002000⟩⟩
theorem candidate01674_checked : Checked candidate01674 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28152575361280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01675 : Description := ⟨77, ⟨13, 0x2a6149aa27c71625f0e47f1bd39baeda66ad3509a52ae8529281d21a8f843c218902e76338c1c04da06b434219b0ca65a22c694349ee4ac1fc0eb472c3651a48c646022e8135894840e1ee0de06282e213f09301980c205c02b01540a803c01c80d405c029012007803a01c00c805001e009004001c00a0040018008002000⟩⟩
theorem candidate01675_checked : Checked candidate01675 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28152847990784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01676 : Description := ⟨80, ⟨13, 0x152da4bd132288fe77e8bcedde0e576eab699ab4d42694abb14dca56505a4451e889242f204cf0276538d1bfcda06b634219b0ca65a22c694349ee4ac2090f886ca33318c8c045d029c140894846c21f10387b83a418a0b884f824c07002e01580aa05401c00b4054026012007803a01c00c805001e00b004802000e0040018008002000⟩⟩
theorem candidate01676_checked : Checked candidate01676 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28153112231936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01677 : Description := ⟨81, ⟨13, 0x23851448964385fcefce79c3bb5caedd56d33569a84d2957629b94aca0b488a3e10c48173c09bfcda0684336194cbac5a22c4949ca1a4f325410487f43e21d78d9469633318c8c045d029c141894847021f10387b83a818a0b884f824c07002e01580aa05401c009003c01d00e006403001500a004401e00b004802000e0040018008002000⟩⟩
theorem candidate01677_checked : Checked candidate01677 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28153120555008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01678 : Description := ⟨79, ⟨13, 0x8e144b21c2fe37e73d39e70eed6ebb699ab4d42694abb14aca0b486a3e10f086240b9c04da0684336194cbac5a22c4949ca1a4f32540fe875e3961b28d2c6323011740a0c4d625211c081c3dc1d40de06282e213f09301980c205c02b01540a802e014809003c01d00e006403001500a004401e009004001c00a0040018008002000⟩⟩
theorem candidate01678_checked : Checked candidate01678 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28153384796160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01679 : Description := ⟨73, ⟨13, 0x289d2d58e2bd39da6e366fcb765ab4d426932ffd5d0a084a221e102c7fd38b9c0cd6e6843361940b4458d28692408f03f81d68e586ca3191808a044d625211d887837818a0b8055427e126079825c0d206602e01580a803c01c80c405c02d012008403c01c00c805001e00d004802000e005002000c002000⟩⟩
theorem candidate01679_checked : Checked candidate01679 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28168946253824 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01680 : Description := ⟨73, ⟨13, 0x256afe97a9bbb5d7cea27273711b50d606a230657bebb555da89521c87840b9f84f986e73691a0ccdc5a528792a08f445d2080fe87c43801b18c705fe29911c08804081ed0ea06f03401890b8848c2180f406d826010807e02c013008c03d01700a004802000f806002a01200880380160090028008002000⟩⟩
theorem candidate01680_checked : Checked candidate01680 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28185245794304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01681 : Description := ⟨73, ⟨13, 0x29234488ed44ca1c8fd17a8bcc1de0e57720b7adb7cd876b8b505a52b0452e28391f687b42d2068f0276b38a9ba0d6269b335994cb4650c26e104872e37d1800ba05382520f706ec34617109f049821a0a104a02400d806002d81540a8034014008c03a01c00c804c02000e005802000e0040018008002000⟩⟩
theorem candidate01681_checked : Checked candidate01681 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28214919495936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01682 : Description := ⟨75, ⟨13, 0xa4bd14638512c86e4005ea8f34773bae9cb4e3b6f93701b18d6e6a134997fcb044f821dd0ca81d3f21df4e9a6ea3361940b2051027d12908ee4161be8d9466030114d09f84a423e102873c3721a30c505c0278126079823c0f606903281780ac05401a00c405c02501000780380130068024010007002000c002000⟩⟩
theorem candidate01682_checked : Checked candidate01682 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28216459297024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01683 : Description := ⟨74, ⟨13, 0x476a256fce7a8b95dc7cdee6df35c5a82d2958229551f087b3c09da0e306e834d99acca65bd2d19624a184f426e11188243f91cb8df46983001740a7050625211c07b83761a30b8855c27c12608681c40d806002d81540a803901a00a004601d00e0064030015009804001c00c005802000e0040018008002000⟩⟩
theorem candidate01683_checked : Checked candidate01683 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28232107687936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01684 : Description := ⟨73, ⟨13, 0x28972d47e8bd45d70e5771b37d9ae2d426942ff941492847a21ed0287e23c09c64d6e69b3361948b4658d28612448ee4121fc0f887643011738a7050225211b07b83761a30c5055427c12607a025c0d806002d01580a803c01a00b4054028011008403c01c00c804c02000d005802400e0040018008002000⟩⟩
theorem candidate01684_checked : Checked candidate01684 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28233139552256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01685 : Description := ⟨74, ⟨13, 0x4b521c0fce7a8bae1caee396f9b5c5a84d285ff28291f087b3f11e04ec671d34d99b0ca45bd2d19624a184a924891dc88c4121f10eb86983011738a7050625211c07b83761a30c5055c27c12607a01d00d806002d01580a803c01a00a004401e00e0064030015009804001a00c005802400e0040018008002000⟩⟩
theorem candidate01685_checked : Checked candidate01685 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28233147875328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01686 : Description := ⟨67, ⟨13, 0xb10549e58b1c889f3f19e60ef074f3905bd6da56c935d9ababef57929a11e085a40d1f20ed67153679af0d4068726e130c8ba3971bf0d906623180dd86882e213e09284341b60a705082500fe07502f816c0aa04701e809c04601d00c804802000f007002c0140080018008002000⟩⟩
theorem candidate01686_checked : Checked candidate01686 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244868923648 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01687 : Description := ⟨73, ⟨13, 0x2c61533a5e4ad637915f8a73f25eaef33776ba79cbae3e6f73695b1ed796aeafbd5e4a6843aa11cf9077b3811b3cd386872c2942c9de4c325791748224001d50df86c835119a8c6053e1b90d105c4278125086836c10807e038817c0b605502380f404e025011808003a01200780380140080018008002000⟩⟩
theorem candidate01687_checked : Checked candidate01687 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244873085184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01688 : Description := ⟨74, ⟨13, 0x58c2a674bc962c72229cf5774f3975b4ad796aeaf7d5ccaa2544a9a11e687542ea11d02e7c83bd9da0e307023679ae4d386872c4142c9e44c325611748223fd1d68df86c834e19a8c6053e1b90d105c4278125086836c0be05b02a813008e04601e80e404e025011808003a01200780380140080018008002000⟩⟩
theorem candidate01688_checked : Checked candidate01688 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244873150464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01689 : Description := ⟨74, ⟨13, 0x58cea494a3962c6ea26b1147ea3d31e7cef0751395dc88deb6d1b649aecd445f7ab914bea3e47f21d90d081a3e61e04edc7153669af0d4066e26e130c8ba4121f10e5c6622ff14e081c3da1bb0c485c427c126086036c17609403f81b80b805502380d804801d00c804802000f007002c0120080020008002000⟩⟩
theorem candidate01689_checked : Checked candidate01689 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244934983936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01690 : Description := ⟨67, ⟨13, 0x95ac495e92eed7513969bdcda36c7b5e5a88bef572297d47c7cc3be9c08d9a69c3371614a164ef26192bc8ba4161fa8ea86a233517f8a6840e1ed0dc86242e213c09304301b60bb05102100fc07403881b80b805502380d805c025012008003a01200780380120080020008002000⟩⟩
theorem candidate01690_checked : Checked candidate01690 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244939145472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01691 : Description := ⟨68, ⟨13, 0x12c58dd44d5e92ea272d368daf2d445efaa8949ea3e40b9f30efa7183811b34d7269c3371620a164f226192b08ba4161fc0eb469c33517f8a6840e1ed0dc86242e213c09304301b60bb05101b80b8055026011c08c03c01c80d805c025012008003a01200780380120080020008002000⟩⟩
theorem candidate01691_checked : Checked candidate01691 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244939210752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01692 : Description := ⟨72, ⟨13, 0x1630a92d2825911b98bc44e1fa6f4c79ebbb5d4ae57721b7b9b40d8f6bb351d7deae452fa8f90ec82e3e41e04d4066a2c993f495e461209100c7543971b10d4466230314e081c3d61bb0c385c427c126085036c17609103f81c40b805502380d804e024011807803a019008003c0160080020008002000⟩⟩
theorem candidate01692_checked : Checked candidate01692 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28244942266624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01693 : Description := ⟨79, ⟨13, 0xb19d4ca9792b58dec53a1f6fc87abbcc9dd2ea272eb8f5be0da36bcb575a88bef53428f944a8fe43aa1a10347cc3bd9c08d9a69c34399b8b0a50b277930c95e45d2088f246fc33518c0bfc53e28911987b439e1b90d106242e213c09284301b608403f01b80c405e02a811c07a036012808003a01200780380140090040008002000⟩⟩
theorem candidate01693_checked : Checked candidate01693 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28245335507200 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01694 : Description := ⟨80, ⟨13, 0x1633a9952f258b14e87dbf51eaef3e7783a89cbada36bcb575a88bdf573a9a147ca2547922ad0ea85c4099f30ef676738d1c08d9a69c34399b8b1050b279130c95845d2088f246fc33518c0bfc53e28611b07b43a41b90d106242e213c09284301b606e02a813008e04601e80d8054026012808003a01200780380140090040008002000⟩⟩
theorem candidate01694_checked : Checked candidate01694 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28245335572480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01695 : Description := ⟨69, ⟨13, 0x2f274a3a2c4ad2375135875423de9af3e779b951c88df96c93511a56bde572297d4289b943ba1a103a77e3b71c8cd7866e32a94309b84912098f246fc2ff173068c31217009f84301e60db06282ec0f006e03301740ae04001b00b804a01f00c804802000e00680280120080028010002000⟩⟩
theorem candidate01695_checked : Checked candidate01695 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28248286757120 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01696 : Description := ⟨74, ⟨13, 0x5e4e94140d959c6e62710da84fbd35e7aea872a390db5cd8f6a3b4ad7bcae452fa8513728774239f18efc73436619a8caa59328613f494849122e104c8063aa1bf0d886a230317307c03461870b804fc2140f306d831417607b03881980ba05702000d805c025011807c03c01900800340140080028010002000⟩⟩
theorem candidate01696_checked : Checked candidate01696 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28248294039808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01697 : Description := ⟨69, ⟨13, 0x2f274a0a06c3aa13ef4d7543951b5cd47695a93d4089b943ba17508e7c63bf1d8ce686cc35c99a8caa50c25392448b84131d68df86c434e1818b983e01a30c385c027e10a079836c18a0bb03301740ae04c023010c08003c01c80d805c025011807c03c01900800340140080028010002000⟩⟩
theorem candidate01697_checked : Checked candidate01697 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28248294105088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01698 : Description := ⟨79, ⟨13, 0xbca52c28a5407958c6ee2450ec850bbd5db0eaa72a37cdb50d946bc3525a5abde57aa9bd49ca114dd21dcff87c73bf1b48d3a6853349948b0a50026f92d492845a2098fd47923b51b18d506682fd174888040e1ed0dc062c2da13f08603d01b00c505a82100e806602b810006402e012808803e01c00c80480140090028010004000⟩⟩
theorem candidate01698_checked : Checked candidate01698 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28248311335168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate01699 : Description := ⟨68, ⟨13, 0x12b4847bd51e7cef3727b5e5a88d2b573a8f93e69b9455a1dd0b88113b39c70d3866e32a9620a204f2253904479237e19a8bfc5cc29a14308ec3a41b90d186242e013c08603cc1b60c504c01e00dc057026011808604001e80d805c026012808003e01200700340140090040010002000⟩⟩
theorem candidate01699_checked : Checked candidate01699 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 28248555225088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate01699_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch016

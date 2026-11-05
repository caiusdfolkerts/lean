module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch001
open Papers.RationalityTen GraphCandidateCoverage

def candidate00100 : Description := ⟨65, ⟨13, 0x283b0ab78e3aedb78d586a0b4a58c6b194eaa6252868f84231f94dcc682335994cc7861e3051760b7458d26d930c8ec300174088040c1ee0de06882e213f09284340de06b032016c0aa054029013806e033016008c03a01c00b804c01e00e005002000e0050018008002000⟩⟩
theorem candidate00100_checked : Checked candidate00100 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5147327528960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00101 : Description := ⟨63, ⟨13, 0xa8bc6b1d72da66ad3509860b7d567aa854ac9ef4baa37d11e8623f19d28dfe6d034219b0c1457429213dc8f03df1ca0d94632301129081c3dc18a09302300d205c02d01580aa0540290120076038018809004401e00e807001e00d004802000e0040018008002000⟩⟩
theorem candidate00101_checked : Checked candidate00101 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5337180635136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00102 : Description := ⟨67, ⟨13, 0x8d4c1aa09cfb575cb699ab4d42569a6212e294246fa244fc67653681a10cd863c30f1828ae049023c0f8472c36518c8c045a22b314089a84a421f10387b831412604601a40b805a02b01540a805201880bc05a024011007803a01c00b805001e00d004802000e0040018008002000⟩⟩
theorem candidate00102_checked : Checked candidate00102 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5354620518400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00103 : Description := ⟨65, ⟨13, 0x235304b7dabae5b4cd5a6a12b4d2ea8df3f19b40d0866c31c1818baa57029312408f03fa1f08e586ca3191808ad450626a129087c40e1ee0c5049811808a03481700b405602a81500a4031012008803c01d00e006c03401800b805001e00d004802000e0040018008002000⟩⟩
theorem candidate00103_checked : Checked candidate00103 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5354628841472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00104 : Description := ⟨64, ⟨13, 0x12a37daba81b7ed5b6a0af3566ca554baa37cf947953b41ba4d0a66b31e1878c1457026d92408be4482150ff472c37e18d0c004d425210f881c3dc1a308682300d205b02d015c0aa05402900f8062023011007c03a01c00b805001c00d005002000e0040018008002000⟩⟩
theorem candidate00104_checked : Checked candidate00104 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5356172410880 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00105 : Description := ⟨63, ⟨13, 0x91fc2520e101b79bb9b5c7adbf6adb4fd79aad34df26a932e8483fd9d38e026e934299a4c5260d2ba117c79237e1b28c685ae2b014489b443a2070d1862421808c03501a40ce05a02b81540a803201880a404401f00e807001c00d00500240100070020008002000⟩⟩
theorem candidate00105_checked : Checked candidate00105 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5356630606080 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00106 : Description := ⟨65, ⟨13, 0x281f25e853bacdb94da96b33515a48b7c5b2ac6d50a9a74c4a5d4e6e6e43699a00cde64e30f11d48903f81f08dec6ca31718088804081ee0de068031412808583c81b20b004e01a40c805a029010407c03c01b80cc06202c01400900440170068024010007002800c004001⟩⟩
theorem candidate00106_checked : Checked candidate00106 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5422673248256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00107 : Description := ⟨65, ⟨13, 0x2b9341292647fa2d10a482fbad9c8cdc96d63595a90d215c42db0fc074c3731b40d0466c31f986cc1a4382030f306f236818a8c105c622010307b83781a20c5049c2120f006b82c011808a03c81900b404101b80cc06202c011007803a01c00b804c01e00d002800c004001⟩⟩
theorem candidate00107_checked : Checked candidate00107 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5422675133696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00108 : Description := ⟨65, ⟨13, 0x2b9748092ec2520e0ffd79bbae1d16e3d715b6f9a7ea3a4df26a932e8483f11d24e046e834f19a4c5260d23b917c7be37d1b28b5c560289136868c31213c093043011806a034819c0c005a02a815007603201880a004402000e807002600e00680240100070020008002000⟩⟩
theorem candidate00108_checked : Checked candidate00108 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5425215865088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00109 : Description := ⟨64, ⟨13, 0x13ff9304455d70e2a6df34f16faa3a4df25d4fc47ca3a51ba0da063830e16f09ec4dd23b91147f83de1cb8df46662fe15a8a144d81a30c384f824c10a04682300d206002d01540a805201d80c8062028011808803c01d00e006c034013006802c0100070020008002000⟩⟩
theorem candidate00109_checked : Checked candidate00109 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5425227374592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00110 : Description := ⟨67, ⟨13, 0x84a42020daf1e75c3891b7cd3f4df268d30e927430a120fc47673a71ba0cd263c30f18289b647722f8f846fa3651660acc53a28613488803781a30c484fc24c10c04601a80d206002d01540a805201900c406002f014008803a01c00b804c01c00d004802000e0050020008002000⟩⟩
theorem candidate00110_checked : Checked candidate00110 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5425484333056 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00111 : Description := ⟨65, ⟨13, 0x212907d78f3ae1c48dbe69fa6f934e8483f11d38dd066931c1818b784f426d91dc8be3fa1f08df46ca2ce15a8a744d22200de068c31213f093043011808a03501a40c005a02a81500a403201880a004401d00e006c03401800b804c01c00d004802000e0050020008002000⟩⟩
theorem candidate00111_checked : Checked candidate00111 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5425492656128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00112 : Description := ⟨62, ⟨13, 0x544e15ae9f7143695ab0be55cdab49542a834eba6251b88ad4311f24e967023679a78d0460a29213dc8f045e1f20df86c82680d1062827812508682300d606902f81680aa0540290120066031016009c04402000e807002400f00680280100070018008002000⟩⟩
theorem candidate00112_checked : Checked candidate00112 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5440190644224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00113 : Description := ⟨64, ⟨13, 0x10917da3c79d3adbf6adabad4aa9bb4d3a3790907c73d99e54dd268531e1878c1457126d91208543fd1bf0d9063430014e89a44402070f686f034618909f82300f006902d015c0aa054029010007c031011007c03a01c00b804801c00d005002000e0050020008002000⟩⟩
theorem candidate00113_checked : Checked candidate00113 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5459248480256 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00114 : Description := ⟨63, ⟨13, 0xaee42460e0fcd79bba75d16e6d6dfb56d5a4a3c4dda6a932e8de4241f1cefe7023749a78d0a6293068f906fc36418d0c005ae2b014489b440e1ed0d1862427808c03c01a40ce05a02b81540a8040018808804001f00e807002400e00680280100070020008002000⟩⟩
theorem candidate00114_checked : Checked candidate00114 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5459508494592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00115 : Description := ⟨63, ⟨13, 0x9fe49c5d34dbf6adae6d5a4a3c4dda5d4e9e6e93679a14cd663830e1630ae64f626e917088a42c20a0e5c6fc33318d0ad450a26c10387ac34618709f026c11806902d015c0aa0540290100062027011808803e01d00e006c03400d00580280100070020008002000⟩⟩
theorem candidate00115_checked : Checked candidate00115 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5459520004096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00116 : Description := ⟨63, ⟨13, 0xa35c3d1e02e0c6e93561a82d2962f2e6d664b1e50f263927c8f84159cd8d3c682335994cc0a5bf2c68f1c72837e1800ba04a221d0f706882e213c092843412607c035816c0aa054028813c08803801980a404602000e807002c00f00700280100070018008002000⟩⟩
theorem candidate00116_checked : Checked candidate00116 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5628095463424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00117 : Description := ⟨80, ⟨13, 0x13cf9b5cb5a3210fa86442bdf38f0676a3aedb4cd42694b3e592ac0055d28913e49d946320c0ffc7e536819b0ca663830f9754b785a42ab94fca4c50e260923c8ec3fa1e40e586fa3651990c646022e8141894443e2060f706ec34418a0b882240ac05502a014403c01d00e006c03401800b005002601000780240100070018008002000⟩⟩
theorem candidate00117_checked : Checked candidate00117 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5828151083008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00118 : Description := ⟨64, ⟨13, 0x1436865be61e06dbe6a0b4a59f2c7c59a2c7553ca554f725c118482d3ff1e68ed06ff3741a6ccd6653302955c9844932178ff472837d1980c005d01ee0d185c424c10d03181800b605502a014407e03801a00ac05002300e807002c013007002000e0040018008002000⟩⟩
theorem candidate00118_checked : Checked candidate00118 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5829558370304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00119 : Description := ⟨70, ⟨13, 0x51926a50c88283e7dda8e0f6dcb505a52cf963e288d3e497046120b4ffc73234299acca661f3021754b7c55b29f93d09b848f2170f2c72c37b1990c005d02b7141893c43e2040f706ec2e212308682480b605502a014406e02b014008c03e01d00e006c03001400800380100070018008002000⟩⟩
theorem candidate00119_checked : Checked candidate00119 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5830229377024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00120 : Description := ⟨71, ⟨13, 0x9e7cd4a1f30c87ce3b51c18dbc6a0b4a59f2c7c511a7c918c7fe39b1b98cd665331c187cbaa5bc2d2155ca7e4f426e130891e42c1e38e5866431a1800ba050625110f88183dc1bb0b8849421a089037816c0aa05402880dc04601d00e006c03401800b005002601000700280100070018008002000⟩⟩
theorem candidate00120_checked : Checked candidate00120 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5830231457792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00121 : Description := ⟨64, ⟨13, 0x10af7ce3c05d76dd26a0b4a59f2c5e59a2c7550ea554eca63918c82b3f29eb8ed069e335994cc0a55723b10bc7fa3941be8c646002e8128887440c1ee0d105c427810d04981f00b605502a014408803f01c00a404602000e807002c01300780380100070018008002000⟩⟩
theorem candidate00121_checked : Checked candidate00121 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5833851240448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00122 : Description := ⟨69, ⟨13, 0x28d741d99f44021650646ebb505a52cf962f28793aa98e46320acfca7363809b98d0466b329987cc085d52df156ca504f426011e885c3cb1cb0dec62e3001740b3850626b0f706f02e213f08681840b605502a014408803701980a404601d00e006c030014007002000e0050018008002000⟩⟩
theorem candidate00122_checked : Checked candidate00122 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5834522247168 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00123 : Description := ⟨66, ⟨13, 0x46421eb0af75db75da7ed2967cb179574a1f4eca5012528934309f94ece701334994cc786233029690aae4761e40e586fa36518c8ba05982b814308183781a20c485c427e10c03e01a80c205502a014408803201800a403a01c00b005002600f00700240100070028008002000⟩⟩
theorem candidate00123_checked : Checked candidate00123 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5834582065152 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00124 : Description := ⟨68, ⟨13, 0x146aa0d4cf9e18ebe6ebb4fda52cf962f2ae943e9d94d3a43d0547e139a9c04dd0684334994cc3e6042ea96f8ab652827a13008f43fa1cb0d945d02ce15b89504081bc0d006242e213f08601a80c205502a014408803201480a004801d00e006c03001400700240100070028008002000⟩⟩
theorem candidate00124_checked : Checked candidate00124 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5834588307456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00125 : Description := ⟨69, ⟨13, 0x276d33e8804259e18ea26ebb555a52ce062f2ae543c9c04d3a3150547cc3809ba4ca661f3021754b1457229413d098045d2170f2c72c36418b8c005d02ce15b89503da1bc0d006242e213f09182380c205502a0144088033014809003e01d00e006c03001400900380100070028008002000⟩⟩
theorem candidate00125_checked : Checked candidate00125 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5868880936960 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00126 : Description := ⟨67, ⟨13, 0xa194a26490f0674fb831bbad586943381766b975b12a153e298e46ea0c0ff67c93d71da0e6c70034f1a08ca46052ac13048f045e2150ff478e399173894443a1a20c504f024a10d07a01ac0be05a02a014407e03e01980a404e022010007002c01200780340140070018008002000⟩⟩
theorem candidate00126_checked : Checked candidate00126 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5869184057344 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00127 : Description := ⟨70, ⟨13, 0x48ea187046767b815b84da96af3515a48b644f6a5c0ff272f3761b4cd1066f32718e0c3e5d529f90b07f43961bf0d9466431a1808ad450621f10387b83761a30c504902160f206c82240f4072034818c0b405102100e806202b011006c03401800b005002000d0050024010007002000c004001⟩⟩
theorem candidate00127_checked : Checked candidate00127 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5899955601408 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00128 : Description := ⟨68, ⟨13, 0x10f3858425dda2dd76aeb511a4ec5e5b228753b49c14a0224d0c27fb3cc9d9ce026873371944c7862330292408f045f1cb0df86ca31817f8b985982b814306f034418909f84942180db03e01c80c205a02a814408803a01800a404401d00b005001e00e00680280120080028008002000⟩⟩
theorem candidate00128_checked : Checked candidate00128 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5902110359552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00129 : Description := ⟨75, ⟨13, 0xa38d06e67d244881c25de18ed1709375dac0d44693b1796c8a1d4ed270534e82a3fd9f8ce607013749a0ccdc65130f9810baa52827a130092045f2170fe878c3961b28c705fe2e61670adc4a81bc0d0062427e123086036c0c205a02a814408803a014809004401f00e806c03001400700340120080028008002000⟩⟩
theorem candidate00129_checked : Checked candidate00129 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5902116601856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00130 : Description := ⟨67, ⟨13, 0xa1ec9161f4f0275cb78db52d456922df96c6b34543a8913de9a74c725c10587fb3f19d40dfa6d335099bcc9c60526091e085e3f81e40e506ca319180887440e1ee0c505042160f206c81a40c605c02d014407e03c01c00c4056029012008802c00f0068024010007002000c004001⟩⟩
theorem candidate00130_checked : Checked candidate00130 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5903575384064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00131 : Description := ⟨72, ⟨13, 0x146587d3c4ddbcec270b3791b5ed676a5b4814489a74c725c10587fb3f19ccce026d034219b0c7061f2ea949898249023c0fe87903961b28c646022a0137093443620a0f886fc33c18d0b605082521080778358118089034814406202b014809004401e00e807003601a00c005802800f0068024010007⟩⟩
theorem candidate00131_checked : Checked candidate00131 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5904380461568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00132 : Description := ⟨64, ⟨13, 0x12488573e5dd3ee0c6e0b5b9a50cc25cbad8953c9d84c72304ff87c93d71da0e6c6eb32918148ee45e2150ff478e37c1980c685ce25110306e431413c09284341e808f041017c0b4054028812807e03e01a009c04a022010007002c01300900340140070018008002000⟩⟩
theorem candidate00132_checked : Checked candidate00132 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5933608566784 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00133 : Description := ⟨65, ⟨13, 0x2b674199d1492e2e90507ca3a7dceae3e707b711ae2d285cf2dc93b07e23e49cc8dce69b3429948c4c6102ab12448bc44021a9000796380173893c4081bb0c504f824610d07a02940ee06c02f81680a804a01a00ac050027011007c03801200800340160070018008002000⟩⟩
theorem candidate00133_checked : Checked candidate00133 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5933610582272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00134 : Description := ⟨65, ⟨12, 0xf95ebaea1dc0da7d6ed26cc2b1daeba9e9f09a798e9708bf7e47cb7ae79a7686ea6d165060547745e42f3fd37d3643302051ec1b91a318a17013c12610d0f308f08206906305405104a03f03403102b02502001c01601301200d008007004003001000⟩⟩
theorem candidate00134_checked : Checked candidate00134 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5933707657216 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00135 : Description := ⟨65, ⟨13, 0x2bf742094842d5d3ed74694330975cb975b12a153a698e460a0c0fc07c93d71da0e6c6eb34f1a08ca46232ab13148ea45e2218ff47963801998c5c5ce26b11006f031410d07a017c0b405802a014409404101f80f80660270110080038012006802c00e0050018008002000⟩⟩
theorem candidate00135_checked : Checked candidate00135 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5937903517696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00136 : Description := ⟨66, ⟨13, 0x4a424b70957d13acdb50d74694330975cb7e5b1aa1d4489bf4d3a300f5c79a39a9b48d3c684329188caac4c523a91788863f81f10d8c66630117389504402040f686f034010c07a02700b405802a014409404101f80f00500240110080038012006802c0120070028008002000⟩⟩
theorem candidate00136_checked : Checked candidate00136 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 5937969577984 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00137 : Description := ⟨76, ⟨13, 0x13cf9a948fe19104b76a3835b74da96af34f5a58cf963e2da53e49753ff1cdcdc86d3344199ccac63830f9818baa5bc2d214fc9e84dc24790b07f43c91cb0d9466431a1740ad450625210f87b83761a30b884902160f206c81bc0d406002d80dc064028011806c03401800a004c02000e0050024010007002000c004001⟩⟩
theorem candidate00137_checked : Checked candidate00137 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6379918196736 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00138 : Description := ⟨79, ⟨13, 0xa00ceda6a52a4864425a096ed474f36fdb4ad5b6a0b4a59c0c7c5e727c93809753ff1f20dd26cf34299acca663830f9818baa58a2b914fc9e84dc24791748583961bf0d9066431a1800ba056a283129087c40e1bb0d185c421a05f02d815c0aa054013808c03e01d00e006c03401800a004802000e005002000e0040018008002000⟩⟩
theorem candidate00138_checked : Checked candidate00138 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6414344912896 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00139 : Description := ⟨74, ⟨13, 0x500276d23f84ac12dd9ee9f7053691ab6d4269433816d29bf4ba9fe4f927343671a14cd865231c187cc0c5d52c515c8a7e45e2160fe87923631990c686022e715a8a0c4a421f10386ec34618a07a01e80be05a02b81580a8042013808803e01e00e006c03401800a004802000d005002400e0040018008002000⟩⟩
theorem candidate00139_checked : Checked candidate00139 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6415385100288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00140 : Description := ⟨72, ⟨13, 0x14049db4ce612507d751375db46d5a69fb4a59c0c634de269cf987013669a10cd265331c187cc0c5d52c515c8a4c4f426191747f439618c8ba059c2b514e881c3da1bc0c485c427e12608601b80d406102e01540a803601900a404801d00e006c03401800a004801e00e004802000e0050020008002000⟩⟩
theorem candidate00140_checked : Checked candidate00140 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6418703843328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00141 : Description := ⟨70, ⟨13, 0x48fe18704b767b829b7eda66adb5096d29ed4ba9fe4e686e93681a14cd863830f9818baa53f2160fe87923961bf0d9466431a1808ad450625210f881c3dc1bb0d1862811807a03481680ae05602a8150084031011007c03c01d00e006c03401800a004001a00a004802000e0040018008002000⟩⟩
theorem candidate00141_checked : Checked candidate00141 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6449711284224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00142 : Description := ⟨68, ⟨13, 0x1258862c12dd72dd56d33569a84b824f7a5d4fc66ff3681a10cd863830f9818baa52624811e088a3fa1f10d946663191808ad450625210f881c3dc18a09f049811807003481700b405602a8150070031012008803c01d00e006c03401800a003c01a00b004802000e0040018008002000⟩⟩
theorem candidate00142_checked : Checked candidate00142 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6453872033792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00143 : Description := ⟨71, ⟨13, 0x83ec192096ed175cb75db4cd5a6a1269d31c9753fd9f8ce026d034219b0c7061f3031754a4c49023c0fe872c36518c8c0459c2b514e8a0c4d625210387b837818a09f849811806903081700b405602a8150062029012008803c01d00e006c03401800a003c01a009004001c00a0040018008002000⟩⟩
theorem candidate00143_checked : Checked candidate00143 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6454136274944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00144 : Description := ⟨75, ⟨13, 0x9ffc34a13b04b7503841bc4dc56d63585a74d215cdae096d29ef4df25d4f9473437f9ba4da068531c187cc0c5d527a12408be4171f28f307243811b40cd863a2fc1718ad450625210f881c3dc1a30a004882120f006b823411805b02d00e0064031011808803e01e00e807003601a00c005001c00d002000c004001⟩⟩
theorem candidate00144_checked : Checked candidate00144 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6455885300736 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00145 : Description := ⟨66, ⟨13, 0x577e4b6eb374eb711b50d606a2331d8c6bb25cbadf96caabb512a69cf8e7ae3ca9dfcdce6d234199b8c464752218fe07c43801b18c705fe22010207b43781a00c4848c2180f406d82700f005a02c010408003f01f00f0050024011008003e01200700340160090028008002000⟩⟩
theorem candidate00145_checked : Checked candidate00145 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6485460467712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00146 : Description := ⟨75, ⟨13, 0x9fcc22e0fae9d72db779b8adb06bd3585a98d215cdae096d29a73e39dfce046e93669a78d0a66931c187cc0c58a27a105c7ca3cc1cd0e046c033618e8bf05c62ce15a8a744402070f686f034618909d848821c0f006b82bc11807802d010006c032018808804001f00e807003601a00c004801c00d0028010004001⟩⟩
theorem candidate00146_checked : Checked candidate00146 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6558961370112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00147 : Description := ⟨71, ⟨13, 0x9b5c96218d04b75cb699ae2d5a6a132557049f04ba9f8cda069b34219b0c7061f30314fca4c50e24891e088a3fa1f10e5c6ca3191808ad450625210387b837618a09f049811806c03481700b405602a8150068031012008803c01d00e006c034018008003c01a00b004802000e0040018008002000⟩⟩
theorem candidate00147_checked : Checked candidate00147 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6582721052672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00148 : Description := ⟨76, ⟨13, 0x123f83ec192096ed270536fdb4cd736adb5096d29a74c725d4ff87343749b40d3a68533618e0c3e60629f92448583fa1e48df86ca33218d0c0459c2b514e8a0c4d6252110081c3dc1a30c504fc11806902e81680ae05602a8150062025011007c03c01d00e006c0340180080034014009004001c00a0040018008002000⟩⟩
theorem candidate00148_checked : Checked candidate00148 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6587146043392 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00149 : Description := ⟨86, ⟨13, 0x49c64b123f83ec192096e55711b829bb0dbf6d335d1ab6d425cdae096d29a74c725d4efe74d39a1c08dd26d034f1a14cd863830f981888a42c20a0fe87c43c91cb8df86ca33318d0c0459c2b514e8a0c4d6252110081c3dc1bc0d1862811806902d01600ae05602a8150062022010007c03c01d00e006c034018006802c014009004001c00a0040018008002000⟩⟩
theorem candidate00149_checked : Checked candidate00149 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6595467542528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00150 : Description := ⟨62, ⟨13, 0x520e1ef006792bb5db82d3f68933d595ea38510a4911548433fd1e64e9c6eb34e99a4b745742ab93649844931be0c6857026d11b087440c1b90c485c424a10c07a02a80e406a02a013c09c04501d00c806002a014809403801600980380140090038008002000⟩⟩
theorem candidate00150_checked : Checked candidate00150 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6654820188160 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00151 : Description := ⟨66, ⟨13, 0x55fa8d71f787a3ee1e02e0c6ac3505a52d12598ac6950aa1e49f236d08c82b3d99cd8e3070134119acca65bf2ba10a878e3ad1bf0c005d026812888743dc1a20b8849421a07c035816c0aa054027811007c03901980b005202300e807002c00f00700280100070018008002000⟩⟩
theorem candidate00151_checked : Checked candidate00151 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6727338655744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00152 : Description := ⟨65, ⟨13, 0x2acb4848fd4465f30f036df3505a52d12599ac6153ca37492a30908882d3cd1d3ce306e834d99acca65ba2ab936498442f1f20eb46fa3301800ba03dc1a30b8849821a063030016c0aa054027011407e03901a00ac05002300e807002c013007002000e0040018008002000⟩⟩
theorem candidate00152_checked : Checked candidate00152 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6791631044608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00153 : Description := ⟨66, ⟨13, 0x53de8c51ef88c43f1ff6f24784380dab6d3c694ac8d57aa38497a32508872e3719b40ca65d42db14fc9b04311f18f4475e3781990bf85d02ba13609684702010dd861c2e2120085025412408d04301bc0c005702a815008a032011807803a01c00d80540200080038008002000⟩⟩
theorem candidate00153_checked : Checked candidate00153 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6792234934336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00154 : Description := ⟨67, ⟨13, 0xa3247e600af9f78d383db72d41694b449632a23492a30908882d3991a14cd66533101824ba85b92ad94fc85c3cb1d78dec6643001740adc4d424f11c08103dc1bb0b8848c21a09203e816c0aa054027011406e02b014008c03e01d00e006c02e01500800380100070018008002000⟩⟩
theorem candidate00154_checked : Checked candidate00154 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6792302051328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00155 : Description := ⟨68, ⟨13, 0x13e88f7c3e5f38f1a70636f1a82d296892c654468c64221cd8dcc66b32998e0c406072f79750aae53f26110b078e3af1990c686002e813509444702060f706ec2e212508682180fa06f02d81540a804e02280dc04601d00e006c03401700b005402601000700280100070018008002000⟩⟩
theorem candidate00155_checked : Checked candidate00155 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6792304132096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00156 : Description := ⟨68, ⟨13, 0x157ba3ec7ea15ef9c780baedc50d41694b449666b18543a8f13b294346321190567e53d71d2ce3070234f19acca65ba2ab91d885e3e41d68df463230017409a04a22060f706882e213c08681f00b605502a013808803f01c80b004602000e807002c01300780380100070018008002000⟩⟩
theorem candidate00156_checked : Checked candidate00156 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6795923914752 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00157 : Description := ⟨70, ⟨13, 0x46421eb0af80e4019e3cebb71234fda52d1255d287d3b293f492224d0907e53a71c68cd265331e17bcbb05ba2ab936c8ec3e11e40df46ca3191740b3057026911b088040c1bc0d106242e213f08601f00d405502a013808803201800a803a01c00b805802600f00700240100070028008002000⟩⟩
theorem candidate00157_checked : Checked candidate00157 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6796654739456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00158 : Description := ⟨68, ⟨13, 0x13e8983c44e000f1f704b699a84d12618a8f52548493999b40cd8638310181cbde5d42dd94fc9b44a92488f847903af1b28cc86022b513508e040e1ee0dd868c31412604601a40c605a02b01540a8031015808803c01d00e006c03401700b005402000d004802000e0040018008002000⟩⟩
theorem candidate00158_checked : Checked candidate00158 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6862162362368 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00159 : Description := ⟨67, ⟨13, 0x9ffc83622b00078438a9c1cd3c6892cdd4749be49520b4f9474a3999b40c705f22ea16ec9ba4c425491147bc3ca1d78e5c6662fe15a89b049c238103868c30e13e093042811a08c03481680aa05401d80c806202b011808803c01d00e006c034015006802c0100070020008002000⟩⟩
theorem candidate00159_checked : Checked candidate00159 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6868336386048 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00160 : Description := ⟨72, ⟨13, 0x109484040ce03900378f3c15c48e0b69fb44937c9a34aea4fd24c848417a050e9c73538d19a4c785ef2ec16fc9b64c222f8f847903651660acc53a26912808d84402070de068c31213f093043011806a03481680aa05401900c406002f015008803a01c00b805801c00d004802000e0050020008002000⟩⟩
theorem candidate00160_checked : Checked candidate00160 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6868593344512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00161 : Description := ⟨75, ⟨13, 0x9f442520fb03380cc001e3cf05712382da7ed124df269d2ba943495212105e74e39a99a4c7062030397bcba85bb26d930895245f1f08f2075e3651670ad453a26912808e04402070de068c31213f093043011806a03481680aa05401900c404401d00e006c03401700b005401c00d004802000e0050020008002000⟩⟩
theorem candidate00161_checked : Checked candidate00161 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6868601667584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00162 : Description := ⟨78, ⟨13, 0x4fa279f3859a8cce22bd0f97dabe71c18dbc6a0b4a5a24cf9657b1ed8c4a88511a37d18c73637319acca6638310181cbde5d52de1690ae055729f14949ea4db26110b078e3961a58c686002e8135094443e2060f707502e212508681bc0b605502a00dc04601d00e006c03401700b005002601100700280100070018008002000⟩⟩
theorem candidate00162_checked : Checked candidate00162 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 6921153150976 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00163 : Description := ⟨67, ⟨13, 0xa72c58615cf9774fb8a1c18dc1694344982eb975a8aa755089d846e230515a7c93d71d2ce6c6eb35a1a78ca452923b91788543e41e38df069231a17389a04a22060c504f024a10d07a02080be05a02a012807e03e01a80b004e022010007002c01300900340140070018008002000⟩⟩
theorem candidate00163_checked : Checked candidate00163 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7024530259968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00164 : Description := ⟨66, ⟨13, 0x53225210957d13acdd1eda8694344975cb7f5b42a1d4489bf493a3011227ad3cb1cd4da46b73421948ae255626291d48bc4431b18ccc6022e716889504081ed0d0055427c10c07a02700e605a02a012808203f01d80bc050024011008403801700900340160090038008002000⟩⟩
theorem candidate00164_checked : Checked candidate00164 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7037477011456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00165 : Description := ⟨68, ⟨13, 0x1772a0fca42126f6c760b891a4cd125d72ad54489d44dea68d2ba8913ef9d38e6a6ea3421940c406092df15c4aac52826291d48bc3e11808ac84d225410487543781a00b8056027e10c07981b80d206802a012808203601880c005e02400e006c02e01200680240100070030014002000⟩⟩
theorem candidate00165_checked : Checked candidate00165 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7038245027840 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00166 : Description := ⟨65, ⟨13, 0x2c1b4e88c7c585e44e9f7063695a24bcc55caa6d508a0946e22a108a7fc3e49ecce6c6cf35a1a74ab052926f11788543c71bf0d9069231a134094437218a092843411806902f81680aa05402480f806a031016009c04a02200e807002c01200680280100070018008002000⟩⟩
theorem candidate00166_checked : Checked candidate00166 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7084894683136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00167 : Description := ⟨67, ⟨13, 0x8d4444a122f9b782ba75d1ee736892b494789bb462a0bcf8e7ad3cb1c6cd6e63c2f795c4ab04db261110c85e3e01cb8d906663001688acc4a02070f6868c31215509f049811807803481680aa05402000fc06202f011008403a01c00b805802400e006802c0100070020008002000⟩⟩
theorem candidate00167_checked : Checked candidate00167 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7108377509888 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00168 : Description := ⟨65, ⟨13, 0x2a193fd8d0c249e08e9e6ad34a5664aca550a8fd4169c3495239111e8173e79d50dfe6ca3421998ca65bf2bc94909584641f48e506be31917d8ba040e1e80c205c424c10705d024411a06e035017c0b805b02b01540a804f02400e004801d00e003c0100070020008002000⟩⟩
theorem candidate00168_checked : Checked candidate00168 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7225892503584 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00169 : Description := ⟨67, ⟨13, 0xbf7d972a193fe978c686126eb974fb569a84cea61e2cfd592aa150827d13848e7447a070f9c74a3849b24d0866c32695f0a484b12318f7c73c35e18c8c045c42520f386282d612607702e812208c03701a40be05c02d01580aa05402400ec04801e00e003c012007002000c002000⟩⟩
theorem candidate00169_checked : Checked candidate00169 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7226966245392 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00170 : Description := ⟨68, ⟨13, 0x17efb2e545e5e31ac75cb699ab4d42615b051664acf550a8193de92a46fa23d0247e33a51bfcda068433616fcae852425391e07be3941b28c6460225210387b831412604601a40b805a02b01540a804f024010c076038018809004401e00e807001e00d004802000e0040018008002000⟩⟩
theorem candidate00170_checked : Checked candidate00170 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7261325983744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00171 : Description := ⟨73, ⟨13, 0x27fb1f488c4266000f24752b6fdb40d5b69e34a59beb1e51c26f12548443e41cd0dd268532998e0ba85bb2b994fc9b04612160f8c75e37e1b10cc86342fe1740ad44d823810387ac3761a30c385c4214091046815c0aa05402280d8064027011807c03c01d00e006c03401500800280100070020008002000⟩⟩
theorem candidate00171_checked : Checked candidate00171 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7376350486528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00172 : Description := ⟨73, ⟨13, 0x27fb20d8d5c456133000752b8a9b40d5a69e34a59beb3756828e937892a4171f20e9468432998e0ba85bb2b994989ba4612228f7875e3971b10ccc6322fe1740ad44d823810387ac30e17109f049821409104681700aa05401d80d8064027012008c03c01d00e006c034015007802c0100070020008002000⟩⟩
theorem candidate00172_checked : Checked candidate00172 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7380511236096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00173 : Description := ⟨76, ⟨13, 0x140484942020390037da3c79d44e246d1b569a7ed2966fa6f134693f49323791228483e61d38e346cd34219a4ca663c2ec16fcae24db26191747c23191740b3056629d13488d84402070f686f031217109f849821806e03501700aa05401b00c806002f015009003a01c00b804801e00e004802000e0050020008002000⟩⟩
theorem candidate00173_checked : Checked candidate00173 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7380768194560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00174 : Description := ⟨79, ⟨13, 0xa024ed612507d80cc001f68f1e7513891b46d5a69fb4a59be9bc4d3a50d2548de4241f30e9c6cd34219a4ca66383101750b7658b2b894989b64c322e8f8475e3191740b3856a29d13488e04402070f686f031217109f849821806e03501700aa05401b00c804801d00e006c03401700a804801e00e004802000e0050020008002000⟩⟩
theorem candidate00174_checked : Checked candidate00174 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7380776517632 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00175 : Description := ⟨71, ⟨13, 0x9fdc9c622b09c8003a69c54dab6adb4f1a50cdf5cda8e937492a3a51cd0d9c68532918e0ba85bb2b9937495245c22290b08283de1b38ccc6342fe1738ad44d823810387ac34618709f04281e809b04681680ae05402000ec064027011808803e01e00e006c034015006802c0140070020008002000⟩⟩
theorem candidate00175_checked : Checked candidate00175 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7383631798272 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00176 : Description := ⟨73, ⟨13, 0x260f1f4889c001e3ee0a6dfb699ab6d42618ac7947a92a4249cd0dd26d034299b0c706202ea16eca7e4da25492448583e11e48ebc6fc3651990c686022b513509484702070f706ec34618a04601a40b405702b01540a8031011007c03c01d00e006c03401700a804001a00a004802000e0040018008002000⟩⟩
theorem candidate00176_checked : Checked candidate00176 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7411783958528 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00177 : Description := ⟨68, ⟨13, 0x12ee906c001d72e206d33569a84c1859ba4a8fc674a3681a10cd86383101750b7652625491e088a3af1cb8d946663191808ad44d425211c081c3dc18a09f049811807303481700b405602a8150076031012008803c01d00e006c03401700a803c01a00b004802000e0040018008002000⟩⟩
theorem candidate00177_checked : Checked candidate00177 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7415944708096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00178 : Description := ⟨71, ⟨13, 0x97741f603300075cb889b4cd5a6a1306134e9434951f8ce986d034219b0c706202ea16eca4c4a923c0f8475e36518c8c0459c2b514e894847022010387b837818a09f849811806903201700b405602a815006202c012008803c01d00e006c03401700a803c01a009004001c00a0040018008002000⟩⟩
theorem candidate00178_checked : Checked candidate00178 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7416208949248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00179 : Description := ⟨66, ⟨13, 0x53a28fd164857bc89d76d42694b245702b1d54daa0947a9d946e22a108a7e53d99d30d6869d336194cab252426f11d885e37d1a48c646022e813408183721a20c505c412206e02f81580aa054024812006c035016009c04a01e00e807002601200780240100070018008002000⟩⟩
theorem candidate00179_checked : Checked candidate00179 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7562776903680 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00180 : Description := ⟨67, ⟨13, 0xa7450062c309678bba79b78da56a0b4a58f2b1b54daa113808dc4541f20f666e63679ad0d3a66b3299564a524d922e90a86c834918d0c005d026810306e42e212508682800de05f02d81540a804902280f806e035016009c04a02300e807002601200700280100070018008002000⟩⟩
theorem candidate00180_checked : Checked candidate00180 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7564857278464 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00181 : Description := ⟨77, ⟨13, 0x2c1b4e8a3f50023231618574255e44e9f6e0b691a84d2860baf31702abb54daa1147a9d84dfa3711508453fe1f24f6674c3759b38d6869d3361948ab252926f11dc8bc42a1e48df06c634918d0c045ce26810306e431412507a017c0b405602a012407c035016009c04a02200f007002601200680280120070018008002000⟩⟩
theorem candidate00181_checked : Checked candidate00181 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7565897465856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00182 : Description := ⟨65, ⟨13, 0x24ab0027b63acdd3ae83733b711b50d606a22ec973cabb5129f1cf727923739b48d0666e2b8936c8ea44021a8e006c631c17f8b5057c2040f6868031215209f048c2180f406d827013207803b81cc0b40590208100076028012008803e017009003801a00b0048008002000⟩⟩
theorem candidate00182_checked : Checked candidate00182 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7584967835904 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00183 : Description := ⟨63, ⟨12, 0xeb3e9de8fdc4da8d60d44bb2b97b7fabba259278917c77ad6e76d268366e5714db47544338036331c2ff2d12041ed1a018915513e12310c0f40db09c09907807305a04104003f03e03b02f02802402202101f01701200e00d00b009002001000⟩⟩
theorem candidate00183_checked : Checked candidate00183 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7584967901184 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00184 : Description := ⟨64, ⟨13, 0x12888543a71cece286d3b575a56bb25cbac6d5a49d24c5a24d08c7c63ca1d2cda268732a956498642a1f20d906302e615c09a03d81a20b8055427812508683cc1b609a03c81e00de05b020810007e03e01b80c00580230108080026012007803801a00a004000c002000⟩⟩
theorem candidate00184_checked : Checked candidate00184 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7584998850560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00185 : Description := ⟨72, ⟨13, 0x15f9a1346a2170ec174e3a3dc4adc76d3b581a56bb25cbac6d5a49d24c6a31d12282e3ef9f18f5a74f3729b44d066552b8936c8ea4431f00e5c6f636418e0b985a226a10487b03401700aa84f824610d079836c13207802d810408003f01f00dc05e024011808403e017009003801a00b004000c002000⟩⟩
theorem candidate00185_checked : Checked candidate00185 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7585000931328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00186 : Description := ⟨75, ⟨13, 0xbb9d09a17108f7b63c79d82e72712371dac0d44695aec9570a254e926e53468914241f7cf2e74e3729a0ccdc65531016f8ae252826d91d485c3e11bd8c705fe2e615909a44121d50de06803121700ac04fc24610c079836c0f006e034010408003701b00c005e02400f806c02e01200700340120080030014002000⟩⟩
theorem candidate00186_checked : Checked candidate00186 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7585735917568 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00187 : Description := ⟨66, ⟨13, 0x51f615d0667ffba01cd4e286e0b635a82d285cf28f13b08dc4231eacf4074b3759a78cd66522ac91dc89c4271f20df06343001738b5c576268103054827812508683d013609a03c01d80be05b02d01640a8040016009c046022010007002601200700340140070018008002000⟩⟩
theorem candidate00187_checked : Checked candidate00187 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589310005504 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00188 : Description := ⟨69, ⟨13, 0x24e91128573a3dcece256e0b505a50b9751e276131a9293d69e50e9e6eb35b99acca463c2b895649b647722190a88283e01be0ccc6343001738b4457026a103055427c12508683d013607802f816c0b405402000fc07c027011808804201c00b804c02400e006802c0140070018008002000⟩⟩
theorem candidate00188_checked : Checked candidate00188 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589314232320 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00189 : Description := ⟨70, ⟨13, 0x520280f25a8483ff5d70e9d74039b1c56da86c6b4fda50a3a4dd26a91bc8483f11f1cf5679d3a49b48d3c66932915648ee44e2190f7c6c62e716b8ac04da1ed0d186242a413c09304301e809a03c01a80ce06002d01640a804001d80c8050022010007002601200700340120070020008002000⟩⟩
theorem candidate00189_checked : Checked candidate00189 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589376065792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00190 : Description := ⟨68, ⟨13, 0x14078884241d70e9d747b9cdb50d3f6942dfd4749ba4939f88f8e7ad3cb1b48d6e66932918f0ae255926d91dc88642f1b18ccc5ce2d115987b43461890aa84f824c10c07a01e00e606a03001680a804001f80ec06402f014008804201c00b804c02400e006802c0120070020008002000⟩⟩
theorem candidate00190_checked : Checked candidate00190 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589380292608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00191 : Description := ⟨68, ⟨13, 0x13fb88ac271d70e9a73838a9b56d3c6942dfd4749ba4621f88f3474a3671948c705bc2b993748ee45c2158f786ce34c1998bf85ce2b513607ac3461870ab84f824c10a07a026c11a07703001680a804001f80ec064028013808c04401e00e006c03401300680300160070020008002000⟩⟩
theorem candidate00191_checked : Checked candidate00191 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589387575296 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00192 : Description := ⟨78, ⟨13, 0x4fee4e31158574271ffee9a74439bdc54dc16d5b4f1a50b9b55da8e93b09ba4c6a4a4f647993a51bacd9c65231c16f0ae64dd23b917088a42c20a0f786f83671998c685fc2e71668ad04d823910307ac3aa1870ac04f824a10a07a026c11a05a02a0100076032013808c04401e00e006c034013006802c0140070030008002000⟩⟩
theorem candidate00192_checked : Checked candidate00192 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7589783937024 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00193 : Description := ⟨71, ⟨13, 0x9fc423a0f2f2175d3aa1c4edc06d734f1a4c9a34c5a31d08c7e43e31d30dd46cc32818e0b7857326e91dc8b83e31be8d885fc29d13388143e01d50de068c30e1700ac04fc24c10a07982bc11a069034019c0a804001b00c806203001780b004601e00e006c034013006802000e0060028010002000⟩⟩
theorem candidate00193_checked : Checked candidate00193 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7590147268608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00194 : Description := ⟨65, ⟨13, 0x20f2f1e75d3891b80d3f693268d0907e43a71ba8cd265031c1880b785712ac936c8ee3e11be8a744d22050ea86f03461890b8056027e12608603cc15e07803701a80d2068033815008003601900c406002f00e006c034017009804801c00d004802000e0060028010002000⟩⟩
theorem candidate00194_checked : Checked candidate00194 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7590148308992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00195 : Description := ⟨66, ⟨13, 0x500a12ef1775036f1b4cd40693b1e582eb8158da95d4189c14541ff0f947b33a61b98da06b93351944a524d923b917c8543c91b28d385fe2e613408183dc1b9092836c14006f02d81680ac055024811407c037016009404602200f007402600e00680280120080018008002000⟩⟩
theorem candidate00195_checked : Checked candidate00195 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7598092943360 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00196 : Description := ⟨69, ⟨13, 0x2ac347d8f8c2b20ccfff7503a01cd4e286f8b6f1b1ad415cf28f13ac8463e51eacf4074b3811b98d3c66b23b917c89c4271f20c686002d715d89a040c1ee0a904f024a10d04d02300ec06f034816c0b405902a815006e031016008c04402000e807002600e00680280100070018008002000⟩⟩
theorem candidate00196_checked : Checked candidate00196 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7623636189440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00197 : Description := ⟨71, ⟨13, 0xae6d22281125a8f9c2520ccffd75c3a81d2ae3f71737d1b52d9069eb4914749be4d52118fc47ca3de1d20e0a6d3350999cc9c47722f91388643df1be8d945ae2b013409483dc1a30ae85042160f206c81a80d2067030016c0b403b01900c4058028011808802600e0068024010007002000c004001⟩⟩
theorem candidate00197_checked : Checked candidate00197 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7623701332224 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00198 : Description := ⟨67, ⟨13, 0xa044442128eb875036a5a7ad245bfac754749be4c6a49cfc47ca3b49c78da66ba3339938c784db23b917c88642f1cb8df46ca3331688acc4d42520f7068c2b410b07903640e606a03481800b605a01f80ec06403101780a004602200b804c01c00d0058024010007002000c004001⟩⟩
theorem candidate00198_checked : Checked candidate00198 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7623705559040 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate00199 : Description := ⟨70, ⟨13, 0x4ffe4c511d84ebae1d40e2d6d634e9a42b7f58ea8e937c7e23e51e68e946e836818e0c405bc26d91dc8be4411ff0f7476639a1b40d3c66c2fc1718ad44d42520f7068c2b214008483c01ae08d04601800b605a01f80ec064031014008c04401e00e807003601a00b804c01c00d002000c004001⟩⟩
theorem candidate00199_checked : Checked candidate00199 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 7623713752064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate00199_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch001

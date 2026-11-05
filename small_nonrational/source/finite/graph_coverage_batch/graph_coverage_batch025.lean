module
prelude
public import IncreasingEmbedding

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch025
open Papers.RationalityTen GraphCandidateCoverage

def candidate02500 : Description := ⟨75, ⟨13, 0xa78d17a5df296906c61e20cfa87c1bbf5caae036ddb6b9ab2d475f3aef566eab2516a33d15a8283a69cb8de26cc34519a8ba856129f132c95047d23091147a23af1cb8de06c431f1818b384b420c0f8075037819d0c384802140f306d82e413e09503781700b005701b008c04001e00d805402200b0040014002000⟩⟩
theorem candidate02500_checked : Checked candidate02500 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16640339615808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02501 : Description := ⟨83, ⟨13, 0xb2d5806a0f47195eca4e33310380abe89efef0c774baf9d44e867093711b50d606a22eb5566a1d4a3230116082a40d1f84f9877f3981b9cda4683337176caac54526012bc8f445d1f10f1870036318e0bfc59225411988804081ed0e786f03401890b8848c2180f406d81a00c405e02c012808803a014009004001f00900380160090028008002000⟩⟩
theorem candidate02501_checked : Checked candidate02501 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16640365314304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02502 : Description := ⟨86, ⟨13, 0x5806a0f47195eca4e33310380cbe89f06f0c776baf9d44e126e236a1ac0d4460caf9d75aab350ea50d1808ad415205cfc27cc3bf9cc0dce6d234199b8ba858b2ab14f89ea4c025411e88ba4451f10f1870036318e0bfc59c25411c08804081ed0ea06f03401890b8848c2180f406d816009404401d00a004802000f806c02a01200880380160090028008002000⟩⟩
theorem candidate02502_checked : Checked candidate02502 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16640373702656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02503 : Description := ⟨70, ⟨13, 0x53ba42118088a3e6df12f007783a89d1ee0b6f5b68db24d766a22ce9554a3e462a2cd05481a3e61ee4e6a7153669af0d4066e2ac14389b845d1f10f2072e33117f894040e1ed0dd86242e213e09304301b609403e01b80b805502200d804801d00b004802000f007002c0120080020008002000⟩⟩
theorem candidate02503_checked : Checked candidate02503 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700062892288 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02504 : Description := ⟨70, ⟨13, 0x55ee9d72bd8e0460e25af9b7c43c01ddaea2747382dbdcda36c7b5e5a88b3a55528f918a8794151f30e6a7023669a70cdc5582a412bc8ba44e1e40ea86a233517f894040e1ed0dc86242e213c09304301b607c03881b80b805502200d804a024010007402c01200780380120080020008002000⟩⟩
theorem candidate02504_checked : Checked candidate02504 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700067053824 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02505 : Description := ⟨72, ⟨13, 0x14fda38c40de18ea2709368dac0d445f3aba956ea8952ba8752868c545421e50548173e61ecce607183749b34d726833371760a7a4dc26012b08ba4481e30eb469c31c17f89504401ed0d006242e213f09184301b606e02e815409204401d00e406c025012007c03a01200800380120080028008002000⟩⟩
theorem candidate02505_checked : Checked candidate02505 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700201320448 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02506 : Description := ⟨69, ⟨13, 0x28dd1928afc41a032f7e785bbb5d4ae89708b7b9b40d8f6aeb51d56ea1d423a0acf9073134399a8bb655a29d143897e4af230912c78a3aa1bf0d886a2318181894c4401eb0d1061c2e213f09284281b609104081c40ba05502200e806c027012808c03c01d008003c0140080028008002000⟩⟩
theorem candidate02506_checked : Checked candidate02506 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700202295552 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02507 : Description := ⟨77, ⟨13, 0x29fb47188a440df12f0c7783a89c24da36bb3581a88be759baadd4e0a3e50ea31514e892415204cf987b23981c68dd26cd3501a0ccdc5d829e93709804ac22e8f8878c3971988c705fe2d112a08d83da1d20dd868031217109f048c2180db037015409204401d00d8054026012007c03a01200800380160090040008002000⟩⟩
theorem candidate02507_checked : Checked candidate02507 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700465561600 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02508 : Description := ⟨79, ⟨13, 0xa7ed2c68e32bd881be21e18eed7513849b46d796b035117ceb3755ba9c147ca1d4a1a315150879415205cf9877f3981c08dd26cd34e1a0ccdc58b29e13d49804a822e911c78c3af19a8c705fe2d012a08e03da1d40dc868031217109e048c2180db037015409204401d00d804a024010007c03a015009004401c0090040008002000⟩⟩
theorem candidate02508_checked : Checked candidate02508 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700469723136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02509 : Description := ⟨78, ⟨13, 0x58a29cf46ba26500641b18f8bfc52620afcc7c73cf1e1ce8870637c1b4ad916bdb589a8cab9536a8793808b3415a068f907363679a6cd0466b329976cab054b288937c97c4141e38e5c6fc3641978c586042d412888cc3ba1bd0d2061827c12508683600c405f02a8110068033013808c03a01c00b004801600a004000c004000⟩⟩
theorem candidate02509_checked : Checked candidate02509 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16700516862208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02510 : Description := ⟨82, ⟨13, 0x5ddac5746ea06ca3241b19288342c213ef7f785bb9dd50e86708b7c9b5cd5d6a3b4ad762ab750ea7693728b0415a074f8c74d3989b30d0e66a32a976cab454525f92908f045c20a0f1472e37e1b10c606062e6164894c47c1f00e786f03441870b804942140f306d81ec0d005e02c011008003a01b008c04001e007803401600a0040014002000⟩⟩
theorem candidate02510_checked : Checked candidate02510 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16707979059456 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02511 : Description := ⟨77, ⟨13, 0x28bb3fb961ca521e10a180cbc39deae98711b81db48d6269db4b576caa150da7192868ad41aa048f8873b36a9a78d046663291750aba52a26892948f646a222905078436a1a68c586122e916709584702200f407583481920b6849420e0f406c02cc13608d039017c0b005602180cc04402000e006c02a00b0050014004000⟩⟩
theorem candidate02511_checked : Checked candidate02511 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16708003694624 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02512 : Description := ⟨79, ⟨13, 0xa2ecfee52914988bc3c2142fcc7873a61d10e076d235edac4d3b696b0c576ca6d50da71915883540a1f10f6473b36a9a6cd046663291750aba51126892508f646a222905078436a1978c586122e916689583d01bd0d206482da15809f049420e0f406c02cc13608d03901880be05601a00cc05402200e006c02a00b0050018004000⟩⟩
theorem candidate02512_checked : Checked candidate02512 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16716589434912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02513 : Description := ⟨78, ⟨13, 0x56169d918f8bcc3e612cfcc7ccbe15e06e9e74ab9c5bd8dc26c835fdabcd2c59d2ae54469c04a3230d08e82d3e41ef0f047263829bb0d3268832b156098445d2270f1c75437e1b20cc06343001740b5c4662070dc868c2e215d0a084901e40d9038818c0c405f02d80d0056027012808c02c0120070028010007002000c004001⟩⟩
theorem candidate02513_checked : Checked candidate02513 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16721448698112 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02514 : Description := ⟨83, ⟨13, 0xa9a54168df40e8c945da1f909980abe79f00f08752b9c5c30dec6e136c5b20d5e6a6b4b156ea214de25191868474169f20e5e7263761b2cd1066732b176cab44c4230912c78a3aa1bf0d8866431a17f0ba059229d12708cc4402070f5868c30e1710ae849021e0f206c81c40d006202e80e806c032015809c04a02300800280100070028010004001⟩⟩
theorem candidate02514_checked : Checked candidate02514 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16721650000128 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02515 : Description := ⟨86, ⟨13, 0x53f68cf4048e4c66a2090a380cbe6de0aea270bb7edb8adb06b0b531a5eaea55baa814429bc4a1a31505e7cc3d99cc0e306e93669a74d0a6693299750b1655829f937098445d2180ff87883ab1c08d8069e31d17e0bac59c29d12808e04402070f6868c3121710ac848821c0f006b817407403901b00c804a01f00e807003601600a804802000e0028010004001⟩⟩
theorem candidate02515_checked : Checked candidate02515 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16721659298816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02516 : Description := ⟨79, ⟨13, 0xa33d01e2090197cdbc15d3ae9172db85daf4d616a62bb5442a0a4dd250d18a82f3e39eb8efe73038e9b48d3c6853349948ba858b2ac1308952441218105c7fc3e51e20d3c66c31d17e0b3853a25011c088040e1ed0de068c31215909d848821c0d703c016808003f01d00c804402000f807003601600a804801c00d0028010004001⟩⟩
theorem candidate02516_checked : Checked candidate02516 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16728940610560 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02517 : Description := ⟨85, ⟨13, 0x281b306906464a1c509f7c1bc21da6ea8744b80dbb2dae6c7b51da56c3059b2add4aea0c4dca38115a82d3fe9f18f667033661ae4cd46552ea9568a7c4c425512408b84442168f147603961bf0d886943031730b3853a24e10f07c03a81bc0d1861c2e015709f84281e60db04a815c08003a01b00ac04601f00f006c02801100680300140080028010002000⟩⟩
theorem candidate02517_checked : Checked candidate02517 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16849450835968 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02518 : Description := ⟨74, ⟨13, 0x57ba9eb4eea654a0e3151808a33e45df6ec8757b865b6cdb26b52ef5580a9a45f229d0c08283f41f20f5a73938d9b8cd9e6b53501a28aa653d26e12f48fa45d2218f3872e3781b20d3866231f12e88483d21ae0c285d0262110077837814a09f04902080f806f02480fc04e026011808403a0120080038016008⟩⟩
theorem candidate02518_checked : Checked candidate02518 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16906153165376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02519 : Description := ⟨71, ⟨13, 0x943464230712d871425df38f8f79cbbb9d46e8071e37c5b4cbb055d2aa947c9f34e0a31916c84a3ff9f34f5674d3811b40aae54822f913879037d1b28d4466a2ff1730b5c4a22060f7076837c1880b7854827809a03e01e40b205602a811008202000f007402c013007803801a009004000c004000⟩⟩
theorem candidate02519_checked : Checked candidate02519 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16939504402688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02520 : Description := ⟨72, ⟨13, 0x15ffa7d4602192f0f74dba3dc1eda55d8aae5534a8953828313e69da461a2550c682940c1f98f8a7ad3cc1cc8e366e936794f49b84c0248910c7963971b20d3866231c1730b4449e1d70d286202de15509f048c21a07802f815409204402000fc056027010807c03a012008003801a00b004000c004000⟩⟩
theorem candidate02520_checked : Checked candidate02520 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16973799178240 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02521 : Description := ⟨76, ⟨13, 0x15ff946460219309f7cf3c49d78eab747b839b40bb154d295d47ca0c4f9a6e5186895431a0a50307e63e29eb4ecc73338d9568a7a50e25f92448f045c2218f2872e3621a70cc46062e6168893840e1eb0eb868431816f0aa84f824c10a048815409204402000fc06c02b013808403c01d008003c01a00b0040010004000⟩⟩
theorem candidate02521_checked : Checked candidate02521 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16973866278912 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02522 : Description := ⟨79, ⟨13, 0xbb5d3a28d13fe944c66a2cb10787442da140f7e7833b49d3ee146cf365dacad48690aadd558a8c507a77516a8023d99cc4d7c6a23461930ab0538296945096049723f10c07fc3c41d98e046c035a1940bd859c26b12888803b21b50d385a82b212708483c01c609104602040be05d02d00e806c02700f00740360160090014006002⟩⟩
theorem candidate02522_checked : Checked candidate02522 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16976137159688 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02523 : Description := ⟨80, ⟨13, 0x1505a37cfda31b1828984396118f997c5bc8ddb0e98702b709b42d5069baaf1536a26504a6e11908a84191ff0f887423761b6cd106773271574a764ad24a11a888842d1e10ec06fc35f1a40cd06122e41670a7449622010387a03ac1b80c905b4248112079037415e09b03901b80c605f02480d4062025011006c01800a0040014008002⟩⟩
theorem candidate02523_checked : Checked candidate02523 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16978282678304 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02524 : Description := ⟨84, ⟨13, 0x14fda74519e7f319a899c4121d108b7cdbdf9e0aed274eb85db8adb06cbb585a98d2155baab14b4a0f4db231516a8023ea1ecce606e93669af8d446733261560a704fb27112c092e4572180ff87883b31c08d806b430f17b0b3853a250110081c3da1d90da86382d415909104381e00e3057823010207802e816807403600f80740360160090014008002⟩⟩
theorem candidate02524_checked : Checked candidate02524 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16978283594760 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02525 : Description := ⟨76, ⟨13, 0x176ea77d14e52918f8b144161cb0b384f3cf1e1cef174c3a09be8ddb6cdb4dd762ab955228793ae9bb45820acf787053611a84c9c55825f11ec8b444020a0f1c72e37e1b20d5062c3021720b244d625111007743481860b6857427a0f206e826c0ee06802f8110080033018809c04602200b004801600a0040014006002⟩⟩
theorem candidate02525_checked : Checked candidate02525 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 16982370027776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02526 : Description := ⟨72, ⟨13, 0x1505a37cfda335104845be65e06abc51326e11908323e21eb0f367823a11c78e0a6ec36d9ae8d4268833b9938aba4c722c91048604171eb8ecc7343811b80d3c66c31d1860b8c56c29d12588e44402070f407543781a30c202bc136078034018c0be05b02d00fc062030011006c01a0060028010004001⟩⟩
theorem candidate02526_checked : Checked candidate02526 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17003775656992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02527 : Description := ⟨70, ⟨13, 0x466a20908b7cdbc15d3aab7510a31505e7c73d61e6cf0471e3829bb0d746a13441938ab04c222090c082e3fe1f28f1076639a1c08d8069e33618e8bf05c62b614e894047222010387b43aa1bc0d1862415e078034016808003f01d00d80640310180088036016009003801a0060028010004001⟩⟩
theorem candidate02527_checked : Checked candidate02527 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17003776705536 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02528 : Description := ⟨82, ⟨13, 0x53ea8c93fc8c7c3e6122fa67883a5dcfce7772f3865bf4de16e436c9b2cd7d6b23539a408c34169ea4f3c7853909c20dde6bd3521a2cc9655826110f886641a1db0e7470835219c8c805c02ca15c8a8050e26e12688f044620a0f4876037e1a60c285b02cc14d09a04081d209b04d02300f0077034810006002b013808c04401b00b004801c00d⟩⟩
theorem candidate02528_checked : Checked candidate02528 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17003842634244 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02529 : Description := ⟨71, ⟨13, 0xb3f54ba6212d68c8c5f603ef897783b51d76df66e0b691b0ed586a130e9800abb553a52516681a3ff1f94e406eb3671ac4d0466c2d215c8ab250e24791d879237c1b18cc860221f10306ec34418a0b884941e8090035817c0ac054019809c03c01c00a004c02401000780280120070018008002000⟩⟩
theorem candidate02529_checked : Checked candidate02529 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17045959803136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02530 : Description := ⟨71, ⟨13, 0xb3dd3a26272ef8fac70e32315c80f3e21ddaed775db7cdb82da46c53561a84c3a6002aed54e8dd3fd1f94dd66ce34e9a08cd85de2ac952095e49323b0f2476a37c1b18d1860221d10306e434418a0b884941e806d035817c0ac05401980a404e02500f007002601200780280120070018008002000⟩⟩
theorem candidate02530_checked : Checked candidate02530 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17045963964672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02531 : Description := ⟨71, ⟨13, 0xbb9d9f6c57580a8c50365e52c094746521f70bb8513cd9d16d5d6a030dd764b03568aae144a9d24dca5311c08b040e9ff4f8c74d37f1b30d0e66a32a95709864b223a116c79237a1b08c605fe2ea16b873c34413c092836c0bc05b02b010408003801b80d804602000f003c01c00a004800c002000⟩⟩
theorem candidate02531_checked : Checked candidate02531 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17051576471808 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02532 : Description := ⟨70, ⟨13, 0x4a2e3230f8808be19de0ebb7513a31becdc16d4361dab0d3f5daaaed44493b4582068fca7cc3db1c80dd66d23589a08cd25a42b9156498647622e8f246f836310307b43781a20c485c427e12508603d015409003581a80c205401980c805201c00a004c02400f00700280120070028008002000⟩⟩
theorem candidate02532_checked : Checked candidate02532 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17052399108352 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02533 : Description := ⟨70, ⟨12, 0xebeea2dc4da8d55d3fc19be7bb5b1faedabba86a54a2293e90f8ad8177e17cc7b371d6e76d26b46695d35725424ac47a45d4483b23803633493172041ed1bc1a018917113f12310c0f408e06a06105404f03503303202902802401f01c01401200e009007005002001000⟩⟩
theorem candidate02533_checked : Checked candidate02533 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17052405415936 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02534 : Description := ⟨74, ⟨13, 0x5f46afd44fa0ed0064311f88ae4085f72f83744b7e1bb8dc66d53629ab0d415daacf541c9d54e02374fca7c83809b98d9e682335994cbc25a72ba9570a8a4c32258ee073037a1b30d1860026b10e08203d41bc0d104fc24a10d07881b40d605b02a00dc066029013808c03a01c0078038014007002800c002000⟩⟩
theorem candidate02534_checked : Checked candidate02534 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17052439941376 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02535 : Description := ⟨76, ⟨13, 0x165a8d5407dde0ebe7513769b88da86aab4fd832be75daac195a8abb550a88927a928449204cfc27cc3d91c10dce6d235b19a4ba65722a112b08f445d1f10e547003631998c5c5a223610f88103da1d20d006242e213e09184301e808e035015009e03301900a8050026012007c03801400900380160090038008002000⟩⟩
theorem candidate02535_checked : Checked candidate02535 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17052669657088 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02536 : Description := ⟨72, ⟨13, 0x17efa0acffa6252f290ac6b62ef0e686542d2130fa07793ac9d48ddf6e1b67dab4d42691b0f1838b3f56baa854209f44ef270919481c3ee1f38e126ed3649a10cd864d29f149c88a3e21a58ccc632301129075031413e093027012208c02e01580a802400f0070036011007802c012007002000c002000⟩⟩
theorem candidate02536_checked : Checked candidate02536 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17053851324432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02537 : Description := ⟨74, ⟨13, 0x50768032188fc45da048fd27c137a9b8cdaa6c6b561a82c005e72ed567a9f24eaa7012927fe3f29f20e2a6e63679a08cd66532f0969caea55c287137098644b1dc0e606f43661990c005a824111088203d41bb0d1054824a10d07882500d605b02c815006e033013808c03a01c008003c01c00a003800c002000⟩⟩
theorem candidate02537_checked : Checked candidate02537 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17061025681664 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02538 : Description := ⟨79, ⟨13, 0xabed08e80531297948563bf0fb85dc091e6cee47603a21beaddf6e33575a80d2e61bac0d44a9d24e0a52501e7e03e51bfcdcc6d034399a8ca25e12d395149864b224911d08283e21e48e4c6f431817f8ba85a8241110882039e1a20b704f824a0f106d82780bc05b02b0104070037011808803c01d007803801600a004800c002000⟩⟩
theorem candidate02538_checked : Checked candidate02538 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17085939847424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02539 : Description := ⟨79, ⟨13, 0xbf7d0567ff2f590443a616f09a7853bd5d62ea66eab6f9b4cd5f69db489878c1c59faa854209f44ef20b90387dc3849bb4d0864d2e7170cb5452a27c13189704862228f887683901c10d346362fd178094847a224100075833e1860bc84f824c0ee06c027011a08c04381c00c005602a80c804802300f007003600b0048010006000⟩⟩
theorem candidate02539_checked : Checked candidate02539 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17086063577104 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02540 : Description := ⟨71, ⟨13, 0xbd2d856afd0fb87542c211ef0776ebaf1d36e0a6dfb09d7d4bd15a12bc1512a57512a85d39894b471a1f10948314051f60f667343911c18d924c325892608b03c91db8d7869c31817f8bb44a42270f386f83421880bb03b819009103c01b80be05702b015409201f00f003c01c00a0048010006000⟩⟩
theorem candidate02540_checked : Checked candidate02540 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17111443669008 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02541 : Description := ⟨79, ⟨13, 0xbce59e28d94219fb484e1fd0b38463ecde14ebf74c3835b84da16b4b541a6ec3c5f52d095e0a8652a28894049b74a5a38d15a82e40e2000f8673736f1a00cce65e2f015e098c46d2240f2476e39b1af0c585fa2f014e89ac4a42190f3867c30c179092042c1f20dd05902bc13606e030817c06a033019009004600a0048014008003⟩⟩
theorem candidate02541_checked : Checked candidate02541 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17120016664592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02542 : Description := ⟨75, ⟨13, 0xbebd9d68ab42397947e238d1948afc3b6176f7e7793b01d48e896fc3719b3ed8f6aeb4b9868ab850a2748ff87e03e49b98d0e6512ae14e8a1c4b223a11808963c91dc0de86c235118c0ba84d62080f5068831416e09f84941e20db04882040ba05602080dc06c027012808803c01d008003c014009002800c002000⟩⟩
theorem candidate02542_checked : Checked candidate02542 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17182312370432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02543 : Description := ⟨83, ⟨13, 0xbb9d5e284740a9794b0251d19487dc2ee144f7f7723b01d4ee866fab719b5ad5d6a234b9764ab8512a749372946458203cfc07c73811b98d9a6873371944ab854526192c88e845b20a0f8879237a1b08c605fe2ea16489044101ef0e786f03441890b704942180f106d82780d005e02c010408003701b008804001d007803801600a0048014002000⟩⟩
theorem candidate02543_checked : Checked candidate02543 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17189015916800 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02544 : Description := ⟨83, ⟨13, 0xa094ff25eb2c3948c8361d30a584f4065deaec374c3761b78da56b13519a44c1c5f52ee1542a104e8271515a81c3f51f0cde06d434f1a08cd664d2e19644abe52a27c131897048623691148283b41bb8da469a3161810bc059c26b11e882c3ce1d60d206182f212508683b81b00b004d82300de05f02c0154066023010007003600b0050014006000⟩⟩
theorem candidate02544_checked : Checked candidate02544 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17189073586192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02545 : Description := ⟨87, ⟨13, 0xa0ed0065171f28bb42ae12d01978ebaedd3ce896f736f1b4ad736ac3505a52bb558e2a813aa9c04a1a11cfca7c83d99c60dcc6cf34e9a08cd66532f29718b285622a6145c9ca4cc24391b88aa4361d38dd46e235519f8c4461a2f116d89d048a22910987943661af0c085e82c814809904581d60d203881bc0d605f02e816c0aa05401c80dc066027012808c03a01c⟩⟩
theorem candidate02545_checked : Checked candidate02545 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17198468825089 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02546 : Description := ⟨74, ⟨13, 0x53b693717d87242be038f8c7a93c81e0ee8c6f5b6f9b4cd956bab571a7caa7507276528c8b643e21290627b638a9ba0da06bf34f9a18cd050e26e130c8ec37d1b28cc86322e814e89ac4a42200f706e834218809f84981b409403501800ac05501900a003c01d009804001e00e004802000e005002000c004000⟩⟩
theorem candidate02546_checked : Checked candidate02546 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17215705645312 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02547 : Description := ⟨74, ⟨13, 0x55e29d5482977c5f21c30af7ff3e3ded6f39783ba2dbe0dbe6d33639af8d5c69f28ed3b294645b21f10948313a69c08dd06d034d1a18cd054826192bc8ec37d1b28cc06322e816b89484661ee0ed06f834218809e04981b406a03101800ac05501a00c805002000f007402600f0070024010007002000c004000⟩⟩
theorem candidate02547_checked : Checked candidate02547 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17215974048000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02548 : Description := ⟨78, ⟨13, 0x5982af1454a1150165e517787342d2008f6b79cbc1ddf2ec7743388dbeadc36c73571a7cd314ea26f928c8314101f78f9a74d3811ba0da0686334193ca8a4c325911d07c437f1998c645ca2c914e89ac4a424110187683421880b984981e20da03501a00b005602080c8062028010007803a00f007002c0120070028010006000⟩⟩
theorem candidate02548_checked : Checked candidate02548 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17223490212096 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02549 : Description := ⟨85, ⟨13, 0x28411f587f42ea032f2376c3b0dd4ce896f9b705af0d6269db4b5862b1f55028894149d34a1a11cff87e03e51ecce3a6eb34e9a08ca45d42de94449be4c624a11cc8c44442168fec7923ae1be0cd062c2fd1748b384d623811008183dc1b80d206182da15709f84941e80d80468158082033019009404602200f00700360150098030014009002800c004000⟩⟩
theorem candidate02549_checked : Checked candidate02549 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17231721269248 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02550 : Description := ⟨85, ⟨13, 0x28474028a344521f70bb7c13bbdd80e886fab719aecd5d6a034b9862b3753828f944a9f34e927051588143f01f28f6471a3731b40d406873351944b8053f28713709864ab23a11148283e21e48ec46f433118c0bfc5d42cd14208d44101d50dd86882dc15809f04941e20db02d8158082037015008c04401e00e806c02000f007002c014009003000c002000⟩⟩
theorem candidate02550_checked : Checked candidate02550 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17231968735232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02551 : Description := ⟨82, ⟨13, 0x5386835176857c09a00ef8d7ac3c99e1aec874b3915bd0dcb6d7b659b00d6769cb4c93b294643ca11d05c7e13db1c54dd06d034e9a10ca65db28713709864762258ea86fa3651990c645d02da15009b84aa24411188083e21b70cf06142e81630a104a42100ef06b025011a07103500c8050025012008c03c01d00e004c02000f0070024010007⟩⟩
theorem candidate02551_checked : Checked candidate02551 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17232885187328 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02552 : Description := ⟨82, ⟨13, 0x59ca82f3ff983c2b2129026803be35e4cef776dbb15d52e136feb6d9b5ed806b234e5a409db49722a908e8193f39cd0e3e6e234e9a14c9a5c329f937095c47c1e48ed06ee33218d0b885942b91500a1c4dc25512388543b01b70d306142f815b0a104842100ff06b024811a08c03781a80d2032018009404601f00f00700360100070028012007⟩⟩
theorem candidate02552_checked : Checked candidate02552 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17236509065744 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02553 : Description := ⟨85, ⟨13, 0x2b0b566a2b50928111f8871c2c6008eef75eba09ce2e5871fb899c1adff6e6b641aeed5e69eb4d16749d64df2518fc47ca3de1e08ea07373931c14dc86d33509a20cce64e23c91008283e21e48ee06f433318d0b9459229d13589484822030de068c2dc15d09e84902160f606c81dc0d406802d80dc064031014008c04400e00580280120070028010006001⟩⟩
theorem candidate02553_checked : Checked candidate02553 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17244293828864 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02554 : Description := ⟨80, ⟨13, 0x167f98543ee1d50b084bc071f18f527903c1ddeced575e3a8dd18e0a6f5b6fdb4cc34512a8513b49c14a322d90f884a418a080ffe7e63e69ed8e687153749b40a1c4dc26192448f045f1e48df86ca31817f8b9853a26b129088040e1ee0dd068431016f09f82500ae05602a807c03c01d008003c01c00d0050024010005002000c004000⟩⟩
theorem candidate02554_checked : Checked candidate02554 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17283233939712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02555 : Description := ⟨82, ⟨13, 0x4c2a1f70ea858425dea4f20783bb55d78ea370536fdb4cc2d544a95d44aa044ed270528687c42520c4ffe7e63e69ecce687183749b40bb053d28713709864a724891e08be4481e48eb46fc3651a70c605fe2e614e89ac4a422010387b83741a10c405bc27e05702b015409204301c807c03c01d008003c01c00d0050024010005002000c004000⟩⟩
theorem candidate02555_checked : Checked candidate02555 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17283242328064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02556 : Description := ⟨80, ⟨13, 0x167fabc43ee1610977c7bdade72f077733af1d46e8b70537c1b7eda661a29c147ca254f9a76938294645b21f10948314101ffcfcc7cd3bf9d34e687023749b40a904c325211e08be3c91bf0d9466a31817f8b985ae252119881c3dc1da0df068431016f09e01ec0c405702b015404001f00f007401e00e0068028012008002000c004000⟩⟩
theorem candidate02556_checked : Checked candidate02556 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17283502342400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02557 : Description := ⟨80, ⟨13, 0x1466a0dd00a62920d7853bd5d7eea670536fdb4cc2d59ba9c147ca254f9a76938282e4091f8cf947343749b40d406833351944ba853b29514449f04df263129492847b23111148283e21e48ebc72e37e1b289484702070f7075837a19f0c305b427c05702b0154092043012008c04401f00f00740360150058028012008002000c004000⟩⟩
theorem candidate02557_checked : Checked candidate02557 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17283514632192 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02558 : Description := ⟨78, ⟨13, 0x59fe8d3454a0f50166290fe874c2ce13501570537c1b7eda661a28893ae9be4a322d90f884a418a080ffe7e63e69cd0dd26d034f9a04cd064f2ed952ca224df26312d492847b2310f246fc36519a0c585fa2e41648a744d6252119888040e1ee09f81a00c405702b0154066032018807c03c01d0050024010005002000c004000⟩⟩
theorem candidate02558_checked : Checked candidate02558 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17283753969920 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02559 : Description := ⟨93, ⟨13, 0x2af1466a0dd00a41b0fb858425e04cf907b8bcfde1aee27613aa5d26e5e716384dbfade16e436bdad4d5169c28953b49c14a322c105c80f3f19f28efe74d39a1c08dd26d034199a8ca25db2a2930c94847822f90507c43c91cb8df86ca31817f8b985b42a0137095448822310507c43c01bf0cf06142d813a09084201de0de04f01ec048023011008003e01e00e803c01c00d0058028012008⟩⟩
theorem candidate02559_checked : Checked candidate02559 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17292091982592 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02560 : Description := ⟨89, ⟨13, 0x28d9421a0443fa16709a80cbd55e46f0a76c3afdd4ce0d6e136a5ad2d5069bb0c5540a22504275d37c94343ca11d05c7fc3f19f28e6e6ec3699a00cce64e2ea14449be4c624a11ec8c44442168fec79237e1b28cd062c2fd1720b3853a26b12908e04402070f706e033e1860b684902160f206e81c407203301900c404a024011808803601500600280120080028010006002⟩⟩
theorem candidate02560_checked : Checked candidate02560 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17300405225472 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02561 : Description := ⟨93, ⟨13, 0x2ce5463a0c4ffe60f0f8856c25204cf8d7ac3c99e1aef776dbb09d52e136feb721b5ed806a934e5a40a284eea71127e87f426a0d10047e93e81cd0e346e93681a88cfc6653261750a284e2264925c8fc4651e48ebc6fc36519b8c4c5f42e11650ae4540287137095446822310507c43941b10cc05fc2b614209084201de0e6047023411806b03501a406002a00f807803a01b00a8028012008⟩⟩
theorem candidate02561_checked : Checked candidate02561 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17300933575176 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02562 : Description := ⟨82, ⟨13, 0x55de92b41a90644aa15f0237f73e41ee2f3f786bb21d2ce456fd3791b96daf6c2359da72d324eca43d16082e3f09ed8e026e83681ac4d086532d215149864762258e586fa3651a30c645d02da15009b84aa21b10107c43c01bf0cf06142e81630a104a42100ef06b024011a06d03500c8052028012008c03c01d00e005002600f0070024010007⟩⟩
theorem candidate02562_checked : Checked candidate02562 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17361734206208 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02563 : Description := ⟨76, ⟨13, 0x10fb858425de0eebc751b829b7eda66172cd9512a57512a8313b49c14a122550c683140c1f98f9a7983b31cd0e366e936814f4a1c4dc26191e08be4481e48e586fc3651a70c605fe2e6168894843e2070f7075c3421880b785540f405702b0154092042010807c03c01d00a004001e00e0068028012008002000c004000⟩⟩
theorem candidate02563_checked : Checked candidate02563 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17420677087232 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02564 : Description := ⟨89, ⟨13, 0x2ce34d0a4f51b28a7421a0448322c513087f439616709a80b3db9e78f0a778bafdd4ce7171fb835be8dc26d4b66dad2d5069ba8893ae9be45820b8ff67e33e51cdcdd86d33611a00cce64e26311ec8c444b1e48e586fc3651aa0c585fa2e41648a744d625210387b83ba19f0c305b42ba12408583c81ba06803080cc064031014809004602200a00280120080028010006002⟩⟩
theorem candidate02564_checked : Checked candidate02564 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17429245856000 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02565 : Description := ⟨73, ⟨13, 0x230712d871425df1ef6b79cbc1dddceb4751ba01c78df16df3699554a3e4f9a70516c87c42520c4ffe7de3e69eace9a7023741b40a904c322f91386fa3651a88cd45fe2e616b89483dc1da0df068431016f0a904f024c09a03c81800b205602a810405002000f007402600f0070034012008002000c004000⟩⟩
theorem candidate02565_checked : Checked candidate02565 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17489258119424 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02566 : Description := ⟨77, ⟨13, 0x28474027c5bc8ddb0ec37533a25b78da6544a95d44aa0c4e927051508473fe1f80f947b33731b40d726873351944a7652a28893e09be4c625692508e646222210b47f63c91d80d9459c26b11008183dc1d60dc069030c16d0ab84fc24a06f02b015409204101b809404602200f00740360130060028012008002800c004000⟩⟩
theorem candidate02566_checked : Checked candidate02566 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17489402529792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02567 : Description := ⟨75, ⟨13, 0xa76d26e8a1422a02c60a2610e585bc269d0ae3c6f8b6f9b4caa74ea26f916c87c42520c4ffe7de3e69ed8dd06d035f9a7cd0c668327952ca224df26312508e64622258df46ca35419a0c6c5fa2e41648a744d625211007b82a413f09301a00c005902b015408203201880a003c01d0098024010005002000c004000⟩⟩
theorem candidate02567_checked : Checked candidate02567 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17489509746944 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02568 : Description := ⟨82, ⟨13, 0x527a8a7424a04460a2610e584d3de5e78f23778bb61d4ce7171fb835be8dba6d4b66daa0d37553a75937c8a54239ff0fc47ca39b9b90da66c2344199cc9c54b26f92508c444b1e48d946a833417e8b9059229d13589484401ee0ee86e030c16d0ae84902160f206e82900de06803000dc064031014009404602200980280120080028010006002⟩⟩
theorem candidate02568_checked : Checked candidate02568 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17493670365440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02569 : Description := ⟨82, ⟨13, 0x526289b402896c38a12ef7879fbc99de8edb762baa5d2ce77722b84dbf4db66d7b671aa2d384e0a29508e7fc3f11f28f6c7343681af0cd465129d137092247722f912c7923651a88bfc5cc2da15009b84aa22310107c43c01b70d306142d81630a104842100ef06f029012408103780dc050025011808803e01e00e804c02000e0068028012008⟩⟩
theorem candidate02569_checked : Checked candidate02569 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17493687010048 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02570 : Description := ⟨82, ⟨13, 0x505e7ff0ac84a3de1e7ef2677a3b6dd8aea9709b6d9b5ed996c03591a72d204e2228d0cc84d40da008fa07343681aecd4466532614e09f64e2258125c8ca3c91b28d4066e2fa1708b285722a014389b84aa23c11188083e21e30e506602fe15b0a104842100ef073029012408d04602040de06a03480dc06002800f807803a01b0098028012008⟩⟩
theorem candidate02570_checked : Checked candidate02570 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17494207103496 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02571 : Description := ⟨90, ⟨13, 0x538a82b3ff8bbc2aa128f907b8bcfde1aef47583aa5d26e2c6f0b72db5ed996beb59da72d204f0a71113086641a206cfb67d03d81d34e046e83681aecd1266532614b49f64c925811c08ca4451f10e5c6fa3651a80c785f42e11650ae4540287137095447822310107c43c61b10cc05fc2b613a09484201de0e604e023411807903501a4060028010007803a01b009802c012008⟩⟩
theorem candidate02571_checked : Checked candidate02571 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17498367853064 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02572 : Description := ⟨93, ⟨13, 0x282f3ff8564251d8aea973f39ddcbce45716384dbf4de16db36bdb2cd7d6b234e5a409e34e39f88f947a93cf1e14ed875339d1c84e106e136b1af4d4868b332192c8ee45f21f10cc8344011f40f3c76c39d1bb0dac6a43391900be45c02ca15c8a8050e26e12a88f04462020f8876037e1a60c285b02cc14d09a046c2040e904d024811a08c03b81bc0d406901800a004602200d804c01c00d⟩⟩
theorem candidate02572_checked : Checked candidate02572 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17519171600900 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02573 : Description := ⟨74, ⟨13, 0x50928110b984ebae1d409d64df1f88f947ac3cd9e08ed275039b9c78e0a6e43699ae8d4268833399388ee45f22090c082e3fe1f28f3076639a1bc8da069e33618e8bf05c62b614e8a104d625211c88803dc1d50de068c0d006002d816807e03701900c40600280118088036013007003400c005002000c004001⟩⟩
theorem candidate02573_checked : Checked candidate02573 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17519171732480 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02574 : Description := ⟨70, ⟨12, 0xf0aebfe98e0ddc2da1a9aa89a70a57a3ea25a0c9f39da9b98a789286082e8157e379b76973771e6ec6cb5114df4c649447b45a4434143e23c939737e2d12522071bd19f18616d15a12410b0f209b06e05f04904003f03602702602402302201200b00a009008004003002⟩⟩
theorem candidate02574_checked : Checked candidate02574 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17523487737856 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02575 : Description := ⟨84, ⟨13, 0x11838afc4b61f70e2858425df1ef6b79cbc1dddcebc751ba01cdce3c70537c5b7eda655529c147ca254f9a7693828b643e21290627ff3f31f34f5677f3a69cd0e046e9368152098647822f913879237e1b28d4466a31817f8b985ae25210387b83b41be0d086202de15209e02680b205702b015404001f00f007401e00e0068028012008002000c004000⟩⟩
theorem candidate02575_checked : Checked candidate02575 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17557843378432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02576 : Description := ⟨86, ⟨13, 0x43ee1610977c63d49e40f0776abaf1d46e8c70536fdb4ca8952ba8954189da4e0a29912a87c431a1290628183ff9f98f9a7af3cc1d98e6871b3749b40a7a50e26e130c92247822f912079237e1b28d386302ff1730b3053a26b129088040e1ee0eb86e83421880b7855427e05702b0154092030010807c03c01d008003c01c00d0050024010005002000c004000⟩⟩
theorem candidate02576_checked : Checked candidate02576 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17558111846400 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02577 : Description := ⟨80, ⟨13, 0x1469a0f50161fd0b384d3829b7eda6511275d37c8a644aa1f10c684a418a060ffe7e63e69cd0dd26d035c1a7cd0266832794eca5451127c137c98c4ad24a11ec8c43c91bf0d9469a33418b0bf45c82b614e8a104d625211c888040e1ee0ac04fc0d005702b015409203301900c406001f00f007403600a004802000c005002000c004000⟩⟩
theorem candidate02577_checked : Checked candidate02577 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17558631876608 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02578 : Description := ⟨99, ⟨13, 0xa77d34293d46ca29d08681116289843fa1cb0b384d3db9e78f0a778bafdd4ce82738b961c7ee26706b7d1bb6dc26d4b66dad2d5069baa914449d74df22c105c7e33e51ef0f0475039b9c14dd86d33611a84d0066732713188f646222010507c43c91cb8df86ca35418b0bf45c82c914e89ac4a422010387b83ba19f0c305b42ba13d092042c1e40dd03b81a0066032018809004602200580280120080028010006002⟩⟩
theorem candidate02578_checked : Checked candidate02578 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17566416374016 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02579 : Description := ⟨95, ⟨13, 0xa3650868110fe859c269edcf3c7853bc5d7eea672c3899c1addb6e136a5ad2d5069baa854449d74df22a51248604172054fc67ca3c11d40e6e7053761b4cd426803339938a544f826312b48f646222290507c43c91cb8df86ca34d18b0bf45c82b614e8a104d625211c888040e1ee0e8867c30c16d09e84902160f206e81a006603201880c004c024011808803600b00500240100060028010006002⟩⟩
theorem candidate02579_checked : Checked candidate02579 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17566953244672 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02580 : Description := ⟨98, ⟨13, 0x519a83740287dc2c212ef907b8bcfde1aef47613aa5d26e5e716384dbc2dc86d7b5a9aa2d38512a7693828a9449218105c8153f19f28f6077f3a69cd0e046e93681a0ccd465129f149c9ea4c325511e08be44520a0f887923971bf0d946302ff1730b285722a014389b84aa23c11188283e21d00df867830a16c0ad84e82421080778378060026012008c04402000f807803a01b008803c01c00d0058028012008⟩⟩
theorem candidate02580_checked : Checked candidate02580 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17566969889280 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02581 : Description := ⟨99, ⟨13, 0xa31d0627ff0f8856c251e1aec2754b9f9ceee5e722b8b1c26dfa6f0b721b5ed966beb549a72d20515a78138e82e3f19f28f5279e3c29db0ea673a3909c20dde6d635e9a90cfa664325930c8f045f21f10cc8344011f40f3c76c39d1c20dac6a43391890be45c02ca15c8a8050e26e12a88f044620a0f8876037e19e0c285b02cc14d09a046c2040e904d023811a08c03b81ac0d4069018009004602200d803c01c00d⟩⟩
theorem candidate02581_checked : Checked candidate02581 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17583596110340 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02582 : Description := ⟨69, ⟨13, 0x286d3298a5c32e0a2fd178334a5a20cfa670b10d4d29ee4b7a3d11be893424a0c0ffc74f38d1bfcd3665330297b0b7e5a62c695d0a164de260924c82c3e41ca0cc06322e815c0a044a22360f7068831417108681540a8051028011c07003401680a803a01c00b003c0100070018008002000⟩⟩
theorem candidate02582_checked : Checked candidate02582 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17716410941440 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02583 : Description := ⟨63, ⟨13, 0xb4bd0be65314b865c0e1f9cfb87abbc89e0ced77143749adcd29629a9d53ea96247c238910284c4182004ea46fc34c194cb76589293130475e3191740a0c4a22380f70688314171086824c11e08902a81500a201d00e006803001600a803c0100070018008002000⟩⟩
theorem candidate02583_checked : Checked candidate02583 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17716415070336 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02584 : Description := ⟨67, ⟨13, 0xa1b4ca62970cb7e73c19a52d1067d3385886a694f723e11be8494181ff8e9e6ff34d994cbd85bb2d31624ae8526285937898249320b0f9075e3941980c645d028312888e03dc1a20c505c421a08902a81500a205002380e006801d00e006803001600a803c0100070018008002000⟩⟩
theorem candidate02584_checked : Checked candidate02584 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17716419264512 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02585 : Description := ⟨61, ⟨13, 0x2d2d565aa2c43607cfe978cb761a52cc06282c614aaa434b2a4950fc84f4179e68f087183741a60ca65f72c6956c9ac3fd1f38eb465a3001740a944e025410206d831217109c823c0fa06c02e81600aa054028813807202800e807001c0080038008002000⟩⟩
theorem candidate02585_checked : Checked candidate02585 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17786744160384 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02586 : Description := ⟨62, ⟨13, 0x4e5a64d1197fd3cdde4adf06b734a59a0c4458228dd2609104219c08ca66022f616dcb2055728813649844161f20df46603001740aec53e28913688cc40c1b90c485c427808f04482180c405502a014008a034012808003a01c00b004c01c0080038008002000⟩⟩
theorem candidate02586_checked : Checked candidate02586 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17787274690816 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02587 : Description := ⟨61, ⟨13, 0x319d63face443e07cfe9769387da50cc05b1ad59480a0a4b2a4950fc7e23cd1e10eaa73538e9a60ca45f72c6956c9c23f81ee0ec865a3011738a944e025410206d827210c07a023c0e606c02e81680b00540288138078028011007001a0090038008002000⟩⟩
theorem candidate02587_checked : Checked candidate02587 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17787784347776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02588 : Description := ⟨59, ⟨13, 0xc13d97299f4448e2c4be1b303e7a9b8918d8c1b5b7abbd51ca59512280d2aa8783f19d38e6a6842f5943c98a3e11b28c0453226912a08803781a009f843016408c03481680aa05402800c405c024011007403801700680240100070028008002000⟩⟩
theorem candidate02588_checked : Checked candidate02588 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17843853803776 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02589 : Description := ⟨60, ⟨13, 0x17d3aced2ca6852f1917c2b6070f0672eb8a1c18d5868b31bd6b8a8d538a8191f08624091d2ce0469e30797d8b1a52e27b932094e41b1f20f386282680f7062827810d04601ac0d205a02a8150086031016008804001d00e00340100070018008002000⟩⟩
theorem candidate02589_checked : Checked candidate02589 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17844056195136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02590 : Description := ⟨64, ⟨13, 0x1434994cbba4591c27b4bd5ddd4e3d715b7c1af2d27621ad293e68753fe1d24e0469c3289808bd85c22c8142c9bc4c123c10587be3c81b28cd45cc2bb14f8a244da2330dc868827810c06d82240c405a02a814008e03b012808804001d00b003c01a0090040008002000⟩⟩
theorem candidate02590_checked : Checked candidate02590 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17852722610432 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02591 : Description := ⟨64, ⟨13, 0x18d1a5ed0ea4650c6814bc6dda4e636edb5bda48b625acac694e4a084b825512548f843f2130f146ec3549a20c9c5f72c693848383fd1f38f2c75a32d152899449e1ee0db0628288128079036415606c03481900ba05a02880f8072031015808801a008003800c004001⟩⟩
theorem candidate02591_checked : Checked candidate02591 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17856402243712 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02592 : Description := ⟨62, ⟨13, 0x56ceac53ec925c37a0a10377e73c7dceae3e707b7b96e4b21537a55d0f68493991ba4d0a6102f596409b449121a90548003cb1d50cc853c26a12787b837618a091843411807103481680aa05402800c405602200f807403801700800340100070018008002000⟩⟩
theorem candidate02592_checked : Checked candidate02592 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17856674676992 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02593 : Description := ⟨60, ⟨13, 0x13e6863410201afdb77bb7f5a409f04b6a55d25a8fb43da124f0274f34d9808b8459028613689224121f00e5c58228f12689104141f10d306342d812908803bc1ac0ac046022411006c0348140068031015808803a01c00c805c02c010006802c010007⟩⟩
theorem candidate02593_checked : Checked candidate02593 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857068925696 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02594 : Description := ⟨64, ⟨13, 0x14319f3431a04ef5e7963b6dcc8e326f0b5ada409704aa24a91f087e4261e10ea46982f496ecb1251327092a48323e71d78cb455027612688283e21c70d306342d814a09484401de0d6055823c11808904401b00d205101880ac04401d00e006803001600a8034010007⟩⟩
theorem candidate02594_checked : Checked candidate02594 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857073119872 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02595 : Description := ⟨71, ⟨13, 0x9f3431a08d02d8003f39ea2f1f72bb895ae2d104f825c12ae92a47c21ed0927813a79a6cc8662a2ff9798b9859a28e93ac96c49a2118fc47783a01950b7c5842a914809dc49224510807dc3901ac0c985a029612f08b03ac1a408c04482200d806903181680aa0540288140068031015808803a01c⟩⟩
theorem candidate02595_checked : Checked candidate02595 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857077313537 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02596 : Description := ⟨65, ⟨13, 0x27df24791747d228b05381d4001ea2e036dfb56da2cb6e5aaabb147a97a4b0a3e109272e36819b0c8062430b17f495249121890607f83e31e88ebc6642ba1508a144d825a11c06ec24010a04a82300d205a02b81540a8031011007803a01c00a804001a0080038008002000⟩⟩
theorem candidate02596_checked : Checked candidate02596 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17857144430656 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02597 : Description := ⟨58, ⟨13, 0x4bba2bb0de81c3f39e0ce3e71437b94dc95643d20c0e9670234f1808bd85c22c813048f043220b10007c83aa18c8a7c4d02510f7068831413c086823011207103481680aa05402800c4058022010007403801600780340100070018008002000⟩⟩
theorem candidate02597_checked : Checked candidate02597 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17860833345792 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02598 : Description := ⟨61, ⟨13, 0x2070f067143441830b9c5c1aa1d4dca084ab23e10f48303b41d2ce3070234f1814bd85bf2c693048f042f20b0ff47c83ad18c8a7c4d02510f7068831413c08682300d205a02a81500a205001c80c4058022010007403801600780340100070018008002000⟩⟩
theorem candidate02598_checked : Checked candidate02598 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17860833411072 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

def candidate02599 : Description := ⟨56, ⟨13, 0x17d09f6492e2c10de7e738f9bdcb72590a75d2ac87a4181e00e6c68230817acb2050f26290d482a4001e58ea862e2200f706f031413f08682300e206903201680aa05402800cc06202c0110074038017006802000e0050018008002000⟩⟩
theorem candidate02599_checked : Checked candidate02599 SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) 17860967547136 := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩

#print axioms candidate02599_checked
end Papers.RationalityTen.GraphCoverageDescriptions.GraphCoverageBatch025

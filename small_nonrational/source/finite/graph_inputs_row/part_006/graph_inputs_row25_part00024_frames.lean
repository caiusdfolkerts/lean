module
prelude
public import GraphInputsRow25Part00024Data
public import RawFrameSupport
public import SharedFrameGroups013Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups019Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups021Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups041Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups046Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups063Checked
public import SharedFrameGroups071Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups107Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups114Checked
public import SharedFrameGroups115Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x355694cdd9131f5f9b8569acd593af349a875019f53d259ca293923a444628b314e114087d2f41daba974ae25c1b7b69acf98db16610bb16dac4572ab14aa905189b91ca1b4087c4f49df3786b0d219130e5dcb79692c651c9e12f246460870ea1c233c630b514626c4207e0d61902a05109c1301f83e07a0dc1b0350560981202304007c0f0150280440700d0160240400600a00c00800 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x39f9b7cd576a83525a6cd2668c3419a0acf75be2c9d5b0aab54da9f54209bb4b624fd25e911477a3691a68cd461a2f11708b0453a2891388924469c1cdaa66431b96c8b0050f27112e895a4a4250125891e48a24211f48ea46f2358e5462c30816e09e84d025611c88b443020e0fe879032e1850b9855829413509584682020f907803a81c40db06a02cc13e07103801b40d406203081780b604401d00e006e03301900ac052028012008c02800e0058024010007002800c004001 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xdf8680b2298f8c525c9aa7144aa174f6a6bd3509a14c725f92e095e4aea53d24691d48b242921090047d23c91d88e046ea07ce1e6933419960bc65d22e01610ac253d281937c8ee46622a10c48464112010fc07a23741b18d4462a2f21670a504e02080fb87943841b40d1064c3021620ab854029214209d84c825612408e846021e10b08183f01ee0f007403901b80d6068027c12608d03e01c00d404401c00c805602a01480a004c024011808003c01d00e005802a014009804401e00e0058024010007 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c76d7b6abb541a92d3668c342d9fecfd67b33b9704b6f5ae2b6155ea97546a9f142ca034f825b128692b490a4411de8e8470a3691a68ca463a3011728a7451226d12488e3be1c1cdaa67132c992cc706282d91600a3850427b138c9a64ba2569290940496247922890847d23b91bc8d23d618c0c2c5e22db14c89e84c224811c086041c2000f086d832e17e0b2855426a12b08e83f81f20f007483881b80d405902780e406d035018c0bc05b01d00e006e03201880ac052028011808802c00e00580280120070028010006001 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c6ed776abb541a92d3668334119facf16772e096deb5c550aa354e4a16501a7c126a92148323bd1d08e146d234d1948c746022e51528a244ca24911c77f3939b70cd865e32598ccc505d22c3945ca124f626f134c9904b3256929c93a496249122890647d23c11bc8d24061898c145e22e015c8a284f426612b892048421d10707ec3c21d60d3865c3061740b2857c27412b08c03f81ee0f007583881b80d405982c013e09c03e01c80d606a03181700b603901c00c806202a014808c04400e006002c0120070030014006001 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb16ad0abfab8ab3a9da48a46a39a18a1498197a9708f68e98cf89588b8807e47d37b879c79378377276374b74673271e6f06de6c36b06aa63f6195e759858c57f56a56253e5094b74ab49d48a48047645544743d42041040c3f83e93db3cf3b33a337a2e22da2ce2c32a027526725524523522e2091fa1e41ca1c21a019117d16f16115a13712b1160fb0f10e60de0cc0c20b20a10a009709607a07006906806105a05903903803203102a02902302200e00c00b009007006005003001 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdd369f323d84cc1a60ab0196d2ab552aa92d484a354bd245521a90547b21c90b884e420a0c103880e4009fc0fce7373921c74d7c66f32e9838c065fe2f995c8aaa51d28013e09e84e926592008ca45d22810d885c42120d0df86dc31e1870c145fa2f015c89dc4ca24d11e88ac4262030fd06002ec16c0a7851427612608c04241d209404801c00d806302f816c0ae05502a00e407003501a00ac054027013008c04201f00e807002c014009004001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5f5b9566ab8563abb53e90cf39933065b4a88ed1562844987304a054037fefddf6be47bef61e9bb0748e81c2b666c0ce596321624b916babe558a8d4fa8b502981272484808ad1221a426794ee1bb3626acd09902fe594ae14d28a4e49491f2303c4760e71b6354680c61802ec588820fe1a43285d0b21542884f09c0e41c0350680ac1502704c08c1081f03a0700b0140240400700b0140200380400600800800 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x4a491b1a627c4988d0fa12c007d4f9df13d9748e11bfb7b6e4d51a6b46682cdd97b29644c61892fb5e2bad6b2ba56aa654a29050e99d2da4646e8c917a2643c808fb1f43d6770eb9cb388650c697b2e85c4b61642ae5009c92e244460889082043806d0d619231c610b71642b4518810fc1a43305d0b415c298510a00e41c0350680ac1502704c08c1081f03a0700b0140240400700b0140200380400600800800 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x5f6b4f586af54e9fb30a5a4a78ed13222c3a81d01dfb3ed7c8f7decbd275ee19bc3716c0ca98fb115c8b5d4da8c5029c92ba5247e8ad1221b424794ee1a73225fcb81602aa5109c92924045c788ec1ce36c6a8d01963005d8ab11220c3f8700d41942e8590a81442804e0861081d0350680ac1502704c0881081f03c0700b0140240400680b0140240380400600800800 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86581a81480f80875d6d26c66bc6af6755df5dd5cd5bd5ab59959058858057856b56255a55754e54653e53152a52247b3e53e33d33c33b136f2e42d82ce2c12b62ad2a529d29528827f27727426b26325b24e24723f2201d01c91c31bd1b81b11a91a219a18d18517e17a17216a16315815014914613f13713012811b11310c1081000f80f10e60de0d70d50d10cd0c90c50c10ad09f09509409308e08d08c07c07207107006b06a06904402b02a02902402302201601501400f00e00d } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x79dcc729c9719b56699865d9461d6d5b16a599625815e5715a5615554d515414e5314a51d4550d3145d1645110431033a0e6394e237cdd36cd935cd4348d033ccd32cc9318c4308ba27c9d2709925894248902388b2248721884208801f47b1e4781d8741c8701b46b1a468198641885f1745b1685916057158551404a108411003b0e8390d42d0b02b098250902006017058110400f0240801c0200400 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x8ea1f8761c866087b5eb7a9e7769bf6f9bc6e1b36c1ae6ada8695a06759a6659664d906318a6217656d5a5615453d454a92849d244851f47119459114390b42907411013f4fb3e4f1358d434cd0334cb320c5308bd2e8b72d8b32c0ad2a4a7294a42889f27099250912388d22887210801f87c1ec7a1e4781dc761c46b18c621845c16c5a1584e1344c11c46114370ac2a0a42408c22058150500f0380d } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record008_frame003_links_0000 record008_frame003_links_0064)
theorem record008_frame003_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 3 :=
  of_group record008 3 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record008_frame003_indices record008_frame003_graph record008_frame003_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (Fin.cases (record008_frame002_supported hcells) (Fin.cases (record008_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6cf6bb69968b68466e60e5d85bb5b455753b5285245075014d84d04cc4b34a74a349a48c4374173dd3c83c53a73a336d35734233933132831730b2fb2f72ea2d82cf2c82bc2ae2a52a029b29121e2081fb1ef1df1b91b11a419818f18317b16c14f13d12d1141090fe0e70df0d40c40b50ae07c07506c06105b05a05605404804204003903602b02602502402102001e01601301201000f00d00b009008005004003001000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x3541a84d30696b3fd9f8cf6677adbd698b1b587aa5d4f8a6a501a78135e9a3495a4411fc8ef47423851b48d3465231d1728b2453a2811368944471964c9863831394109ee4e326912e895a4a4250126091e48824211ec8ee4712348e386162db1640a644f426111c08a44302000f9078436c1970bf055428c13508e843c1fc0f907803a41c40dc06a02e41640a504f01c80da06c03181780ba04a01d00dc06c03401880ac050027012808802c01000580280120070028010006001 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x31b18a4c346182f5d7a0bbd5d3ab5d57caa454c291944aa124e3a6a931897c48923b91b08c5459a28512087e43821b107e82a4021fbcfc27cb3dd9934c8262e30e9548a8a53529393f09bc4d126712d093a48f24611b08c845521e8ef06b232a18c0b8c5842b013e89ac4ac23611208343c01c30d8860c2e61600a104c823c11507f83c81ca0d906382c41580a504f01c80da06c03181780ba04a01d00dc06c03401880ac050027012808802c01000580280120070028010006001 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x9b32f65bcb395329a5049892323a2cc488610a20c408802ffdf6bd878cebdd6ba2740e61cab91704dfdbab716cad7dadb54618bc970acb58cadd5a2aa51ca05332594ae949242454748d91822d44c8750a211410810e3196314610be9772ea54ca313f2744b89491f22c44c788e61b6344648be1722d0530a113825c4708b1061fc348640c61542a0510a013c1c034064094118210400780a81001a0300580800c01400800 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x74f7257147046f06e06d56cd6af6a363e61c5f75e45cf5ba5a85a557555753d52351d5024fd4ee4e84df4c74bc4a449f4834794734664043d03bd39b39538037536132b31d2f22e92e32cd2bc2b429d29428d28226f25c24924223222c1e61ba1b51af1a519d19817116615c15414814313a13012d11110b1020fa0f30e50de0d90c60be0b90b40ab0a609909107706f06d05b05a05705605504003903602502302102001e01501000d00c00b008006005001000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x241c4788b0fe0f3e67c0f69dd3b2744e61c73826eedcdb734c684ce594323634c4d4aa91516a1536a6749e9051a230454891119f83e67aced9d839a70cd499e31460cbd9702d0588b093825e4908d1102104047e8fa1ec3c0748df1aa33c630c11762e0540a313a2604988b1021c43305d0aa150240440821001c8340620ac1502804e0841001d02c0400780e01802c0380600a01001800 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x71a35d1aa0d42698347da22d0667bb3c17b8b6958e2bad554a76535a7f536097f49f24291fe8ef474238519c8c345f22d51628a9450226512a88d3c19bdcda268133618f8c4c5a22be14b0a2e4e926893209664ad2539274930492244120c8f647823791ac73231f16f0b2457226f12608dc45421d0fd87bc3c81d60c605a42a814709d046021810107b83c01d60e306d83501720b3052827c0e206f03601ac0c406002e817007203601a00c8054027012808c02a010006002c0100070030014004001 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0xceb96726e45c638b311611c1d826e95b6b33636b9569acd4e2895029c133e654c39732b64b47c8ed19e314538890d6184227ceef1d438f700dd9b734265cc61853015f4be16fad65a0afd5e2b854ca894ba955069fd1ca0b3ea7b8f41b7340654c59822dc590ae95824c448820fc1ec3806c0d31943005c8aa13e26049091116224348680cc1942e05b0b21601b8350680c81502704a08c0a81001802c0400700c01401001 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7517267157056ef6e26d76cb6b06a464361c5f75e15cb5aa5a357355353d5235034fc4f14ea4e24cb4bb4b54a34a04924804764754674093d03bd3983913733633293192f22e92cc2bd2b729f29729128127b27025b25824624422f22d1e61ba1a91a119817116615c15414f13f13613212d1111080fe0f60f30e50de0da0d30ce0ca0c20b80b20a60a509e09906f06d06a06906005e05b05a03903603403202a02702502301501000c00b008007006005002001 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record014_frame003_links_0000 record014_frame003_links_0064)
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0xb7b69ac8d8ab015deb8566ab754e8acf99c33425a4a393f2123745e8890ce17c27847066033fb7f2fc1f7be77b0f3de6bc170ed4da333064cc61872e25a8af95b2a853aa6541a804f09a93426149e93521a4246a8ccef1af334648c59662b0534a113d24e47c8d1171f23b8740e11b8338648c417c2e05a8ae14c2844d097120234350690cc1942e05a0ae1581c0350680c81502704a08c0a81001802c0400700c01401001 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record014_frame004_links_0000 record014_frame004_links_0064)
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1b52c5261f2d113da9d94d426693109774b4a57929e94849fa44521c908480a3e51dc8ec472a374f946583219748b5854f295937c99e4be22190c48444121f80f807a236319e8b80578270130093c3a81c20d9868c3021710b1055c2a01490a104ec26412b093047422c111084840c1f80f707703a01c80de06b034014a09f04a023c10407c03881b009404401c80d005602a014009c04a024011808404001d00e005802a013009004001e00e006002c010007 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x32ce0cc0f73ab5565a7b4c288d079ef37e694cb9891ea3c4728c715621440863091f23756ded29a1322630bfd7d2f7574acd54aa0520a193f25548e885089f33da7a0d019831a608b89662ba564a994827a4c88f1162264147d8f71d43846b8d41902f85c0ab13a258458891082043b0720d21982384206e0d01582a05009c128240460841001d0380580a8130240400780e01802c04007 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x24244387d07def3d9776ecdd0b9971ee05bc3746e0d2da5344676ccd93b25638c5172a8d50e9b533a4d47e8ad132233f07ccf59e33ac72ce21a733860cbd9692c85849992d244468881082043fc7d8f71e23a8710de1ba350670cd18a3005d0b91622b0548a413825c458881021f43a0710d4198240440720d01582a05009c128240460841001d0380580a8130240400780e01802c04007 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x38d5aead506a134c1a3ed0c68233f19e2cef5edadbd698b1b575aab9542a72535280d3c09af4bfa50926a90647f23bd1d08e146d234d1948c745ca2c91528a044ca25111c78237b9b44cee65e32618ccc4e5a22be1488a124f726f13489904b3256929c93a498249122090647b23c11c48d23bf1ce0c7860a2e01640ae451427a133095c48422910e87ec3e41e10eb069c32e1830ba057c28c13a08c043c1fc0f707803ac1c40dc06a02e41600a504e01c80d806b03181740b803901b00d006202a0138094044010006002c0120070030014006001 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record016_frame001_links_0000 (interval_append _ 64 128 131 record016_frame001_links_0064 record016_frame001_links_0128))
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8ba87f85e84482982181a81580e80879474e7216ed6e36d26c76bb6af6666355f85ed5dd5cc5be5ab59959058858057856b56256055154e54653953652a5224b146c43b3fe3f33e33d23c43b13603332ff2f52e42d92cd2c12b62ad2a529d29528827f27d26e26b26325625324723f21a1fe1df1d71d01ca1c21bd1b81b11a91a219a18d18518217617216a15f15c15014914613f13713012811b1131101041000f80ed0ea0de0d70d50d10cd0c90c50c109509409208f08d08c07207106f06c06a06902b02a02802502302201601501301000e00d } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame001_links_0000 (interval_append _ 64 128 142 record017_frame001_links_0064 record017_frame001_links_0128))
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x7ddf0791d8745ce731cb721c66f9b26999f6719a66596651835e9705bd6c5a567589605795c56958555535494f5394c52548515434f52d4911a4651644d11431003d0ed3a8e839ce4388df374db364d7350d2344ce334cb320c7310c22dcab290a127c9e26c9925894248902388b22488214842087f1f87b1e4781d8741c8701b46b1a86719864184601745b168591605715855108410fc3c0e8390b42c0a8270942406017054120400f024080180300400 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame002_links_0000 (interval_append _ 64 128 142 record017_frame002_links_0064 record017_frame002_links_0128))
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x92a438de2b8922187e1e86e19846057e5f27bded7b1e979dd6735c3709be6edb96cdb06b9ab6a1a56819d67197659936398d62988609725a55f5795a55d5553d424d92f4b12a4a5264912147d1c465164450e4350841d043fcfe3ecf93b8e236cd8358d5348d0334cb320c5308bd2e8b92d0b32c0ab2a8a7294a42889f27099250912408b22887208811f87c1ec7a1e4781dc7618c621805d16c5a1384d12c48118450ac2a0a02508c220581504c100380d } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame003_links_0000 (interval_append _ 64 128 142 record017_frame003_links_0064 record017_frame003_links_0128))
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x74f7256f06ea6e76e06dc6d56cd6af6a363e5f75f45eb5e45cf5c65ba5a85a555754d54553d5235024fd4ee4e84df4c74a449f48d4834794734664043bd3ba3a239b39538c38037536131d3132fa2f22e92cd2bc2b429d29428d26f25c25324924223222c1e61e11ba1b61af1a519d19817116c16615c15414d14814313a13012d1111020fa0e50de0d90c60be0b90b40ab0a609909107706d05c05b05a05705605504003602602502302102001e01101000d00c00b008006005001000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x6275e65b55b05ab5a75a059a5905815785315004fb4f64f24e04d44ce4c44c348b48647f47845e44644343d43743041a4064033fb3f43ed3e93e23a137036d35a35334e34333c33732b2ef2e62c82c22b72a329729027627126925a25124723d23a23022b1ea1e11b41a71a119619218b16415b15614e14c14213813512c12311c1000ef0e90d60d20cd0bb0b90b60b10a70a309308a07506c05b05a05905605505404003602602502302102001e01101000d00c00b008006005001000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0936.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0936.count (({ width := 9, code := 0x23716894461f0e86c32150983c05fafc7d3e5f0f67abcde4ed763a9d2e47037dbadb6d355a2d066b2d94c96430d7ebe5e2ed74b85bad966af572a952a651a813e9b4d25d289147a35188b452190a7f3e9f0f2773b1c0dc6d351a0cc6431988c2602c950a44e269309248239188843208fc7438190c4602d160ac4c240f07436190c0582210068301608030140200 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0936.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0936
    Papers.RationalityTen.SharedFrameCatalogue.group0936_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb14acca8ba87a80a78a6ca5fa4ba2ca1699a94193e93592c90e8f58e88d18cc85a84583782a7f07bb7ae79b79078074970f7056eb6d96c66ba6a36365dc5d95bf5b15a759058357a55d50c4fa4da4cc4b749647c47545244443040b3f13e43d63cc3b63aa34032d2ec2d92cd2b82a92a02602492392222172071f81ee1dd1cb1c21871591471161080fd0d50cb0bf0b40a60a309708f07706d05c05b05a05705605504003602602502302102001e01101000d00c00b008006005001000 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
def record018_frame005_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0604.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0604.count (({ width := 11, code := 0x2064017dcfb1f4be67c0f65e93c7780ebdce39a730e51c3b806f8dbdb734a68cd059db26624c4185b07600bb56e2d95a2b2962ac2578a81442864f69cd38a694ca97929a3b46c89d0fa174107f4fd9eb3ca778e89c737c6dcda9ab34a61cc11662b6560a694928e4ac9192022e44c859022023e0770e719e3045e0a91482784788d114218418810f21cc330600a41442804d09812c2003604c094118210400780881001a0300580800c01400800 } : Fields).get c.val)
theorem record018_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record018) (record018.maps 5) (record018.inverseMaps 5) record018_frame005_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0604.localPairCheck (smallEmbedding record018) (record018.maps 5)
      (record018.inverseMaps 5) record018_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame005_links_0000 record018_frame005_links_0064)
theorem record018_frame005_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 5 :=
  of_group record018 5 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0604
    Papers.RationalityTen.SharedFrameCatalogue.group0604_facts record018_frame005_indices record018_frame005_graph record018_frame005_links
def record018_frame006_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1c3cd5465db2e1962caa6523275928c8363e2e055beadb56aab39576ab2555aa8953c9cb4d5266130c94d48ba4411ee8e5469a2690c885d425a11107a8384181cacd0267c3341984cb66533261918c7a5922bc9544a8653028893e09d84c425b128c90846b23291808ba4562290e186da3251870bf85d22da1660a104da25d12408e446222a112887442a2060d485bc2b212c091045c1de0e506d03481840b904f82540f206f02f01740b805902c015c0800360130094046021010007802201000680300160080030014002000 } : Fields).get c.val)
theorem record018_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 6) (record018.inverseMaps 6) record018_frame006_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record018) (record018.maps 6)
      (record018.inverseMaps 6) record018_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame006_links_0000 record018_frame006_links_0064)
theorem record018_frame006_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 6 :=
  of_group record018 6 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record018_frame006_indices record018_frame006_graph record018_frame006_links
def record018_frame007_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x2854d69632ba54ca393b25a47c828f91060e41982903a003f67defa1f3bba768ebdd3b8f6f4dd9b73696c2d2d9ab30652c9590b1c62ab895f2bc562ab1542a1538a61482664ba941262454708c116218422820fc9ee3d278cef9d83aa69cce97e2e85b4b215f2b65089e1382624b8951242404688990f1e83806c8c41862f8548a51462784c09510c204378680ae1582a8520a21401f03604c094118210400780881001a0300580800c01400800 } : Fields).get c.val)
theorem record018_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record018) (record018.maps 7) (record018.inverseMaps 7) record018_frame007_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record018) (record018.maps 7)
      (record018.inverseMaps 7) record018_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame007_links_0000 record018_frame007_links_0064)
theorem record018_frame007_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 7 :=
  of_group record018 7 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record018_frame007_indices record018_frame007_graph record018_frame007_links
def record018_frame008_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0928.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0928.count (({ width := 8, code := 0xb9b4b0afaeadacabaaa9a8a39f9e9d9c9b9a999897939291908d8b8a898887848281807f7e7d7c77737271706f6e6d6c6b67666463615f5e5d5b5a58565554535251504c4b4847464443423f3e3d3b3a393837363534312f2e2c2b2a282726252322201f1d1c1a19181716151312100f0e0d0c0b09080706050403020100 } : Fields).get c.val)
theorem record018_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0928.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0928.localPairCheck (smallEmbedding record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0928.localPairCheck (smallEmbedding record018) (record018.maps 8) (record018.inverseMaps 8) record018_frame008_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0928.localPairCheck (smallEmbedding record018) (record018.maps 8)
      (record018.inverseMaps 8) record018_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame008_links_0000 record018_frame008_links_0064)
theorem record018_frame008_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 8 :=
  of_group record018 8 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0928
    Papers.RationalityTen.SharedFrameCatalogue.group0928_facts record018_frame008_indices record018_frame008_graph record018_frame008_links
def record018_frame009_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x35367bcab95329651c9d92b2263ec717c6dd5b8b696c6d3da0b3b65eca54aa834e29750d9d53926accf98f2863f4788d11923045b8a7011e63ca780ef1dc3b275eeb1d1b5e6a8cf99a325626bf57c2e25b6b255baa1536a614ba905188f11820c3fa7c8f39dc3b06d0d299e31e610bf17a2f05c0b496326a4407f8df1ae33c598ab14626c4908e1081f8350630a814c2904f09c1341e03404c094118210400780881001a0300580800c01400800 } : Fields).get c.val)
theorem record018_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 9) (record018.inverseMaps 9) record018_frame009_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 9) (record018.inverseMaps 9) record018_frame009_indices (Fin.ofNat record018.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record018_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record018) (record018.maps 9)
      (record018.inverseMaps 9) record018_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record018_frame009_links_0000 record018_frame009_links_0064)
theorem record018_frame009_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 9 :=
  of_group record018 9 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record018_frame009_indices record018_frame009_graph record018_frame009_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (Fin.cases (record018_frame005_supported hcells) (Fin.cases (record018_frame006_supported hcells) (Fin.cases (record018_frame007_supported hcells) (Fin.cases (record018_frame008_supported hcells) (Fin.cases (record018_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6ef6ad6aa6a269b6846175d55d25bb5b45ac54353d51f50b5024fa4db4d54ce4c44bc4b54ae4a94a14554094043f73f13e43db35c35434b34332a30c3062f92f12e92d32cc2bf2a729d29128727f21e2161fc1f41ec1d11c31bb1a519d19518e18117115f15314a13d12910a1040fd0f60f00de0d70d10bf0ba0ae09f08606c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xadaa8ca87a80a78a599a794293e92091390c8568457fd7c37a979b75673b72770d6fd6eb6d96cd6b76375d95d25c95bf5b15995004fa4ef4e44b948e48247546d4604324254153f23e43d63c53ba33732d3052f52e42c02aa2a02752672572492392252071f81eb1d91c218417316515314511910a0fe0d80cd0b40a308c06c05c05b05705605304a04403a03703602802602502402102001f01d01201101000e00c00b009008006005002001000 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0561.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0561.count (({ width := 11, code := 0x718de5bb3746dad919d327648c658c3125bcb6d64abe570ac54c29451ca153fa7a4e89c535a3f4408750ba1241a818e69ca38e700d99a434266ccc994306600bd96f2d4598b11612744dc9492624044c851081f03d4780ed1ce3806b8d21a2328618af1582a4530a312e24c480861062003d86d0be1482884d098124230440740dc1b02804c0941202104007c0e8120220400700c0160240400600a00800800 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0561.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0561
    Papers.RationalityTen.SharedFrameCatalogue.group0561_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a61b78d9f5cc2b5d590ab4550255928c90c47d239115e89844420c903e80d3fc1fa0fae7c63dc9990b465942c015b08444121ec0f1876037b1b20d505fc2eb16c8b105682a31490a1441e20810087e83e61d50e707243841bb0d2067c3301890c085e82e61600a58510278136097849c2160fe07403881aa08203e01bc0be05e02e816c0b205802a8128088037013809804a023010808003a0160098048022010007803801800b005002000c0050018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6c76986935f95b65b35ac5a553a5305135094fd4e84e14d94af4a649c49048a48647f4793f83ac3a93a439f33132b31430c3032f32ec2e72c42bd2b52ac2a82a52a029c22421920c2031fc1da1d51cc1c11b419c19618f17d17917216b15913d13212611e1131070e60dc0c00ba0b007c07606d05d05c05b05905705605304804203702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad9a99a8799c94493e93592c84d84581c8097f47c17a679b75273b7277106ff6eb6d96ca6375de5d95d25c95014fa4da4cc4ba49247e4754384254154013f43e43d63c932d3203133052f52bc2aa2a02962862582492392192071f81e71c21a019118217316515511b0fe0da0ce0b407e07a06d05d05c05b05905705605304a04403702702602502302102001d01601301201101000f00e00c00b00a008006005003002001000 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame003_links_0000 record020_frame003_links_0064)
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0591.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0591.count (({ width := 11, code := 0x10fa1742a7c0f19e2bc177cdd9b93606b2d4da0b3a66cc6589b0d608bf97c2f35e0acd4aa94520a3123a4546a8c516220432861001fa3ec7c0f61e93ca788cb99131261cc11692c8584ae9572824f89d92e254498909111f23cc758e61be3585f8b4142268480740e21a42d85a0b215c2a8540a21182083704e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0591.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame004_links_0000 record020_frame004_links_0064)
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0591
    Papers.RationalityTen.SharedFrameCatalogue.group0591_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x108607c0c76ce59ca38f712d09a0b36662cb18fb1962cbf97d2f55daba5722df5baa7d422824f89e51822e43c8650a2074007f8f41e43c4768eb9d039872cc39812fa5e4b91592a6538a61452604b89591b22843c858f71ce3886e8da1a83385e0b01402684706e0d61882a0530a41402704d0941041e83504e098128230420800e8160260480881001e0380600b0140200300500600800800 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record020_frame005_links_0000 record020_frame005_links_0064)
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b44b98562a89942494949aa48521e8fd471222103e80d3fd1fa0faa7c43dc1ea0cc8591279137882a4011f68f6c7923ae1aa0bac5b22c615a0a8452028413a083c4102010fd07cc3aa1ce0e4867c3301900c485d02da1670b005642a414b0a204d825e11808884282060e9071035014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
def record021_frame002_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8899c93d8d88c584683a82d81f80c7f279b73b7277126ff6e96d76c96b66375d85725634fb4f24e74dd4cf4b84754254154033f43e23d43c83b932d3203133052f52bc2aa2a02492392272191e81da1cd1c21ba1ae1a019117316513512911a1090db0ce0b309b07e07a06b06a06105e05d05705605304a04403503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record021_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 2) (record021.inverseMaps 2) record021_frame002_indices (Fin.ofNat record021.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record021_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record021) (record021.maps 2)
      (record021.inverseMaps 2) record021_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record021_frame002_links_0000 record021_frame002_links_0064)
theorem record021_frame002_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 2 :=
  of_group record021 2 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record021_frame002_indices record021_frame002_graph record021_frame002_links
def record021_frame003_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x69c5e65a055954e4f34ef4e54e14d54c749545944a43b42f4224154114083ad3673203152ba2b42af2a529f28e25c21e2112021f61e61dd1d81cf18b18718117c17715f15b15713813212c12811711211010c10a1051000fb0f00ea0d80d20cd0c70b50b10a809107807406606505c05905805205104e04704303503402b02802702102001d01601301201101000f00e00c00b008007006005004003002000 } : Fields).get c.val)
theorem record021_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 3) (record021.inverseMaps 3) record021_frame003_indices (Fin.ofNat record021.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record021_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record021) (record021.maps 3)
      (record021.inverseMaps 3) record021_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record021_frame003_links_0000 record021_frame003_links_0064)
theorem record021_frame003_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 3 :=
  of_group record021 3 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record021_frame003_indices record021_frame003_graph record021_frame003_links
def record021_frame004_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x185ab1254c288d42097f4b72571296939495a3090be849419a07900a7f03ef9f24e486a43189880b5259a2c695f8ae256428c93109624a124992008da4622298eb473638c1bd8db064e3151830aa052828013708d44462100fe87b83c01d10e186ac3301640a785002600f4073832014a08203e01b40d8063030017c0b205802a812808803501a00ac050027010808003a0160098048022010007803801800b004001c00c005002000c004000 } : Fields).get c.val)
theorem record021_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4) (record021.inverseMaps 4) record021_frame004_indices (Fin.ofNat record021.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record021_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record021) (record021.maps 4)
      (record021.inverseMaps 4) record021_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record021_frame004_links_0000 record021_frame004_links_0064)
theorem record021_frame004_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 4 :=
  of_group record021 4 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record021_frame004_indices record021_frame004_graph record021_frame004_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (Fin.cases (record021_frame002_supported hcells) (Fin.cases (record021_frame003_supported hcells) (Fin.cases (record021_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x69834b5a4cd1f68633dd63ab0f55aa9f53629a34a4a4451de8da469a33518a8be45c22b914e8a044e225111a6c435a1a8cce06372b7957ca9c51b27113209824ba25992b494849f24c123c91048123d91d48e246b1c80dfc6362dc15c8a284f426812d89304721fd0f907903ac1a70cb86142f01690ab046821e10107b83c01d40e206d83501720a503701b40d805f02f017409403a01b80d806a03401980ac0500270130094048012008804001800b004802000e006002800c004001 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa8aa89a82a7aa5aa2d94293d9088db84c8457fb7c379c77276375873e72a71b6fb6e86d66d06b86a45d85cf5c659b56e4fa4ef4e44bb48e4764704634554474314284183ff3f03e13d33c23bb3ab33732d2e92c02a02752672572492392251e61db1cd1c21a019118017316515311910b0fe0f10e60dc0cc0be0b20a309b06c06b06a05d05c05b04a03a03703603503403302b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x66f66e66c66a6626545d85d35b058e5395345114ef4d64c64c14bd4b64b04ab4a149a49449248b4843f93f23ec3d23b035635234c32f30d2fa2f52f12ec2e62df2da2d42cc2c52bf2ba2b62b42af24d2492151f11db1c41b91ae1a419918e16515f15514b13412c11e11510c0fe0d50cf0c50bb0b70b30ab0a409e09508d06b06a06905d05c05b04803903603503403303202b02802702602502401201101000c00b009008007006005003002001 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xbd76a6c0d78ae95bab4d65abb56aa9d4aa9144269cd199b31e614be96d2ce564a39431a23245d8ab13e24c418790d61542683f0620840a808ff1fbbf07caf85ee3d87a8f41e63966c8d75a7349686cf99c32f654b856c2c357cae559aa953ca6d4927b4ec9c934a5e4aa9291f23846c8b9141e13b0704de1b835e690cd99030a5c0b59662c0558a594827c4e09b12e25048c879092003f07a8ec1ce3806c8d519c320610bb16e2c0550a713425c450870d21982d05706a0d01903104c0941182201802c0480800c01401802 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record023_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record023_frame001_links_0000 (interval_append _ 64 128 148 record023_frame001_links_0064 record023_frame001_links_0128))
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xc6612fb7abc5dae972b85bedb6ab4d86af56aa54aa14ea652e9346a2cf277399bcd66731984ba572a9449a49229047a3b1b8c45e2b1489c4a230b81c01f4f87b3d5e6ef76b99c6dd6db65b0d6693419ac662b1182be5e2e16ab3592c15ca852275389b4c255268f46a1d0a8341200f87a3b9d4e872381bcd26732990c45e2e164ae562a148a04e2692c9248208f86e34168a848210c8602c15088401c0d048200c050200c0200 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record023_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record023_frame002_links_0000 (interval_append _ 64 128 148 record023_frame002_links_0064 record023_frame002_links_0128))
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xc6612fb7abc5dae972b85bedb6ab4d86af56aa54aa14ea652e9346a2cf277399bcd66731984ba572a9449a49229047a3b1b8c45e2b1489c4a230b81c01f4f87b3d5e6ef76b99c6dd6db65b0d6693419ac662b1182be5e2e16ab3592c15ca852275389b4c255268f46a1d0a8341200f87a3b9d4e872381bcd26732990c45e2e164ae562a148a04e2692c9248208f86e34168a848210c8602c15088401c0d048200c050200c0200 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record023_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 128 148 :=
  interval_of_check _ 128 20 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 148 record023_frame003_links_0000 (interval_append _ 64 128 148 record023_frame003_links_0064 record023_frame003_links_0128))
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x74e36d9736add5642a314eea5051da84d2ae94949aa48521e8fd471235d1888a844ea2210a4842417a07d01a7fa3f4999cb525942ac150ca3850726f908c82a4011f68f6c7923ae1d18e406e83691aa0c7861c2fb1758b6458c2b510a083c4102010fd07cc3ca1de0e807243681ad0d2867c3301900c506042f416c0b285802b21520a5851026c12f090846022210a08183f01d207c03c818c0c005902c01580aa04402080ac050021010007803a016009804402000f007003401800b004802000c005002000c004000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x62eafe157ca5b526a8494049e24e926d527e93248da4091de8de461a2e114e88c44321d50648204071ff8fd87da3e91b00ca864730717fcbc25d22db1524a7c52a28a94149ee4e226d133096e4b325291c48c845622490f085c4261b08d4067432418a8c185d02d915f8ac44f026d12f894848e23911888884221f20f2875838c1b50d4067030a1790b2055428412f09104581d607c03c818c0c005902c01580aa04402080ac050021010007803a016009804402000f007003401800b004802000c005002000c004000 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xadba9499e94a93e9209138f58e88c684e84683a82d81f80c7f27e37d27ba7aa79b76f76074f73b7277127006395e45d95bf5b15905835645024fb4f24e74dd4cf4b84af4a148b4834754524444354254154033f533832d3203133052f52d92cd2ac2a027526725924923922721a2071f81d91cb1c21ba1ae1a019117316514613512911a1090fc0db07a07706105e05705605405304404102b02802102001e01d01601301101000f00e00d00c00b009008006005004003002000 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
def record025_frame004_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0606.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0606.count (({ width := 11, code := 0xa6347e694b395f2764c48f9131f62bc538930f61a42a84106e0a4047fefe1ecbd178ef01dbba9744d299332462cc4182b005e0b4567aca582ae557aa3540a6d44a8650099d2f25749c9251ea353c677cec1ce38a6f8d71a732a640bc1702d0588af15329c5149f1322584988f9142164147c8f41ca370698c917e2d84e8660c81502904b0941202383f07a0a8140210400780e8160260440800f01c0340600b0120200300500800c01000 } : Fields).get c.val)
theorem record025_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record025_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0606.localPairCheck (smallEmbedding record025) (record025.maps 4)
      (record025.inverseMaps 4) record025_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record025_frame004_links_0000 record025_frame004_links_0064)
theorem record025_frame004_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 4 :=
  of_group record025 4 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0606
    Papers.RationalityTen.SharedFrameCatalogue.group0606_facts record025_frame004_indices record025_frame004_graph record025_frame004_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (Fin.cases (record025_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c76d7b69b34b5a30d11685b40d9f8cf66772c8162aade5652a8d51ea6c4da26a52e495e49ba48d2008ef47423851b48d3465231517c8b545822ad1488964479df0daa6c43489a04ce265f32618e0c505802b794f0a5851c28513dc9c64d326413049744b3256929093e498247922890247b23b91bc8d23911c10d1065e3071798b285722a914c8a284f425b12608b443220a0f707803ac1c60db069c32e1780b4852826c12708583f41ee0f007483881b60d503901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record026_frame001_links_0000 (interval_append _ 64 128 138 record026_frame001_links_0064 record026_frame001_links_0128))
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1998c5b5fd2fb5768ba45ca2e016e0b605a8a9694a0a1450227913a89b649fa4d51e28e045d22a510e878430212506a8234062004fde7d83e99f34f6e7883bb1b04ca664430597f0bd65de2e796f8b6a54929d94089e84e626b93249764b22541258908474233914889843f215109c8284041fd0f947b23611a98c5c6102ea16d8b0056229d14509e04da25212388c444020f0f887903ac1c60da86a03381850bc85902a6140090845420e0f907483781a80c903901bc0c606001d00dc06a03401900c4056028013009404602200b004c01800b00500240100060028010006002 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record026_frame002_links_0000 (interval_append _ 64 128 138 record026_frame002_links_0064 record026_frame002_links_0128))
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb19ad3a9da89a70a63a57a43a36a2aa1494693f9239168f88eb8c984e84782180e7e67d57ad79c79378377276374b73e72a70e7036f66e46bf6ab63c5e05d85bc5ae59c58d58056f5625024fa4da4cc4bc4ac49e48f4804764704634554474314284183ff3f83e13d33ca3b33a333832e3082f82dc2d02af2a029628627526724923921a2051f61d71c91c21ba1ae1a01911731651461331271070fa0f10e60d90cc0be0b507006d06105e03a03703503403203102b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record026_frame003_links_0000 (interval_append _ 64 128 138 record026_frame003_links_0064 record026_frame003_links_0128))
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
def record026_frame004_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6a668a67566e66766466165b65765364b5da5d55c35b75a459858253b53652451e5074fd4e34d64d14cc4c64c14ba4b64b04a84a349f49948d4864443ff3f93e63dc3d33ca3bd3b13a535c35634333c33032731f30e3022fa2f52f12ec2e62df2da2d42cc2c72bf2ba2b82b22ad24e24a22a22020b1fe1e51db1d51cc1c41b91a419918617817015b15114b14613e13412c11510c0f60ea0e10cb0c10bb0b70b20ab0a409f06f06c06105e03903603403303103002b02802602502302201601300c00b00a009008006005004003002 } : Fields).get c.val)
theorem record026_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record026) (record026.maps 4) (record026.inverseMaps 4) record026_frame004_indices (Fin.ofNat record026.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record026_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record026) (record026.maps 4)
      (record026.inverseMaps 4) record026_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record026_frame004_links_0000 (interval_append _ 64 128 138 record026_frame004_links_0064 record026_frame004_links_0128))
theorem record026_frame004_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 4 :=
  of_group record026 4 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record026_frame004_indices record026_frame004_graph record026_frame004_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (Fin.cases (record026_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcd3663b2f9968cab65131dd8d0c5962730fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c28c2458227911a87b4389d08e5872536c1af8d666883359984b9e5b82d89634ae25662b09500a6252327c936c9a44c925792809243e31e38ef871836c1b10d646723251898b8c5842b8130091c4682220f0070c3721b10ca060c2e616a0a7850026012308581640b005702b010808204001480a004e02000f807802000f007002c0140090028010006000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x37edef78dd772dbf6ad9b62d7b5ad5b26c871cc6313c3ef3bc2edbaae7b92cbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe789da739c66e9ae2286e1882e04805fb7ddf5741c9719c16f5bb6e1a968d9d65d936458d5f9775c1495013c4c129499234550f425003ecf936cd4340cc2f4b62ccb028c9d25c93220831f87b1c03a0e4380dc330c831098250901d0701b0400f0380b028090140400c00 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0x9ece66d3095caa491f8f46227128641e0d017ebe9eef579bc5deec74b99c8e26fb79b8d96bb55a4d16732d92c76230d82be5e2e96eb65aacd62af56aa9489f4ea5d249047a04f87a3c1d0e26d3599cc8602d154a651269288c44200f472381208c44200f878361a0c8602a1409848200f07030160a0481c0c05018080200 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xbb1b99b91b65b47b3ba78a6ca65a5ea4ca429d79c89c19b59a399490b8e98d98a98898798598458317f77d47c06bf6b16aa6a069568b66e66165964f64363962b61d61360b5fe5f357755d5505285115044dc4ce4bf49b48247746b45744843b3c03b13a539a38b37e36b35834d34133131f3082f62e62d42c72b72ad2a12932862322232132011cd1b51a819918317416714313312311610305805705604304204104002902802702001f01e01101000f00e00c00b00a009005004003000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x32f9956ca262cb0fd870b555a2ace1658b1f58aaa6d516a7f53a29a14c09b84cda6412b8939496a4391ee8e144f21ed0e275b3a69d08e6e72c3929bd0dc66d83649af8d666a734c9a20cf866b330973cb705b12c695c4acc540298948c9f24db269131895e4a024910107e43e31eb0f1c77c3ad1cd8e306f636c1b10d386723251898c185e82e31698b0857025912388d04441e00e186e43581940c185cc29e140098048c22005802b81580860420208100052028013808003e01e008804001e00e006002c0140090028010006000 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x378dcb6fd8b5ad5b26c871cc6313c3ef3bc2edbaae7b92c1ae2b4a9e9fa6e8da1a7f9ce6e9ae298962287a1b8621383e0b82204805ff7f5fb7e5f77d5d0725c6705bd6eda968d9d65d936458a5f9775c15353949515404f1384d1304b5294991b4550f4250640d003f8fb3e4d8350d0330bd2d8b32b8a327497220831f87b1cc390e0370d0330c831098250901d0701b0441003c0e0300b028090140400c00 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record029_frame003_links_0000 record029_frame003_links_0064)
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x68ab41da02cd3663b2f9968cab6513159878c375aaad15670b2c58fac55592ab055429fd4d0a6052228b14329db4e3a6e135499b4c825fd2dc95c4a5a4e525a92748723dd1c289e43da1c50c6842416a060ec07523a39cf0e6272736d1b00d686883359984c9863731317c0bc05d42e496f4b665a92cd1634afc5712b31588a9e53d29793e49b64d226412a893848e1d68e6c71837b1b60d885c62c215c091c4682220fe87b83c01d10e186e42c814f0a004c022209304902440b005702b008003e01e008804001e00e00580280120060028010006000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record030_frame001_links_0000 (interval_append _ 64 128 132 record030_frame001_links_0064 record030_frame001_links_0128))
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xe1b82e037edef78dd772dbf61d6755c9b21c7318c4f0fc06fabdeedb9ee4b6ed7b4ecbb1ac1af6b8ad2afaaea7a8e9fa6e98a36869fe739ba6b99e58942488b228892218761a83205809fb7ddf57b1e7789da759d273dcb721c570dc16fdbd6edb96b9a86899764d916317b5d16d4e1344c12d4a526400fb3e4d4340cc314c12f4ba2d8b323c8820c7e1d05815c560e4380dc1d0701b0441003c0e02c0a024060140400c00 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record030_frame002_links_0000 (interval_append _ 64 128 132 record030_frame002_links_0064 record030_frame002_links_0128))
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6ff6f06e86cf6b66ad69a6806746085fb5ed5cc5bc5ab59958857650f4de4bd4b64ac49c47845744e43e42e41440d3ca3bd3b438d37d37235934733d2cd29c28a27827326323522220f2051f51e51d419117116d16715f15b13d13913312b12712211c0ed0e70e40d70d10ce0c50bd0b70b40ac08208107f06606406305b05805705405204f04d03403303202902702502302001e01c01301200f00e00a009007003002001000 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x18cf12e1ec057b2f15d4b816e6b4d5daa54ce92516a0d3e276ca99131da38c6b8c713a1d43585f09e0cc13786ee1d937d6dcda1a633e66cb4d54297514a1d3da5b4a09091e232452874e69a233063cc217c2ae544a293b2664a8920ec1ce3846a0d01963045c8b61642a84007f0fa198320630c017c2f05b0b21582a0340660c81482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x6130782bfdf6f97ab9dc6c762b0d7ab95babd4a9f459ccca632f96c9a3f1e8dc5e27108341609017fbf9f0f479399b4d669b49a0c761afd7cba5bacd509c4d2612a9444a1d08803f1ecf06431180bc5d2e168b2582b9549248238f87a3c1d0e47035198c05c251208c42200f07032170a84c240f070281207018080200 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
def record031_frame004_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36b5b04d6f68a33a59accb7651b2717aabb15c5accd61eae956a2b195709eb4bb24f926491d484230d11687f435215508483c3b69d1ce686c334e9a28cdc66032c9674a8652b28b14309f44b624f12248fe46d23191686fc31f1890c005d82db13f09c44be24b11d08bc4521880bc85a4286139098046020c0fc079836c12008f04681b40d606a031017c0bc05b02c81580a803401980c8052027012808c04001e00e004c02400f00700280120070018008002000 } : Fields).get c.val)
theorem record031_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record031_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 4)
      (record031.inverseMaps 4) record031_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record031_frame004_links_0000 record031_frame004_links_0064)
theorem record031_frame004_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 4 :=
  of_group record031 4 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record031_frame004_indices record031_frame004_graph record031_frame004_links
def record031_frame005_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0645.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0645.count (({ width := 11, code := 0x12163dc758cd17a2bc4e8870fe084097f8f99ef3cf784ef1da3826c8d39a5344670c89863085febcd73ae3582ad15729851ea193ba714d68c907a023ec7ccf39d13866e8db1aa344668b394b28c4fc9b932232450871052003ec7b0cf19030c5c8b41602a8520a01362543c0770ea17c2f05d0ac14c2904f09a128240330640c41482704a08c1001e03804c0900f01c0280480700600800800 } : Fields).get c.val)
theorem record031_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record031_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0645.localPairCheck (smallEmbedding record031) (record031.maps 5)
      (record031.inverseMaps 5) record031_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record031_frame005_links_0000 record031_frame005_links_0064)
theorem record031_frame005_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 5 :=
  of_group record031 5 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0645
    Papers.RationalityTen.SharedFrameCatalogue.group0645_facts record031_frame005_indices record031_frame005_graph record031_frame005_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (Fin.cases (record031_frame004_supported hcells) (Fin.cases (record031_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1a64c916142e116fab765b82da56c6b0457bab955aeac855baa9152ea8553ba9a14ae97b48b243120a8fd47b21d10c485241fa0bd0448123ff9fbce6e7303951c90e3a7173609ac8d4469234119c4cc065132098c4c426102ab14049f24f427713a4904475234916c89e44621d10b08403be1d70e7871c37e1b78d7869c33e1970c7861e30417e8bd85e02e21670ae454628d13c89984b224b11e08b043e21110106483041760a8851424c11a08483741a606002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame001_links_0000 (interval_append _ 64 128 138 record032_frame001_links_0064 record032_frame001_links_0128))
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1abecc664b2f917aabc35d8ae7d716b42599ac8561eafd574ab6d5aaace563ab015729bd4a9a50925e919484228111e87c433215509884541ea0d8f207803b69d6ce8e7343731b58d866b134e9a28cf867533799a0cc265a2c494d4a5051a28413e895049b24691ec8da466230916c8ac3ed1ea8f007523951bf0db46be34f19f8cc063e30c17e0bb05b62cc15f0ab853c28f13f09ac4b624b11d08c445422310e068831a17b0a384ec23010a07f036c1a406002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame002_links_0000 (interval_append _ 64 128 138 record032_frame002_links_0064 record032_frame002_links_0128))
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
def record032_frame003_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x1e33ae734e1dc23806fade5bab6a6ced8db035c6b0d51a8b4d694d19a131d5f6bdd79aee5d2b1d61abf574ad558aad550a8d3fa7b4f09d13826c4b095128a4d49291520a3d4748d91922e41a7b8f51e73c6780e11be3766dcda1b135c6a8d399f33464cc61842f65d0b79682c2564a81482885009d9382664b09291d228430841041fe3ec7b8f31dc340660c616a2bc4f09b12a210408520a213826849090098128220420740e01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record032_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record032) (record032.maps 3)
      (record032.inverseMaps 3) record032_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame003_links_0000 (interval_append _ 64 128 138 record032_frame003_links_0064 record032_frame003_links_0128))
theorem record032_frame003_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 3 :=
  of_group record032 3 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record032_frame003_indices record032_frame003_graph record032_frame003_links
def record032_frame004_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xec398e0f6edaf67d9360d7751d3b4ad1f43d033cce735ccb2ecaf09baae6b8addb62b9ad6b1ab2a7a8e9fa6a959c66d9aa6698a5e92a4690e3f8ee378ce2f8b228892207fde1779db75dd46d9b36c1ac6a5a668d9f67193639876097a5c56b5995f56952525424f93a4d5324b5264851944109415013f0f83d0f03acd0330c62d4af2789b254842045013c4c12c4711826094220841d0701505013048110400f0380c02c0a0240400c0200400 } : Fields).get c.val)
theorem record032_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record032) (record032.maps 4)
      (record032.inverseMaps 4) record032_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame004_links_0000 (interval_append _ 64 128 138 record032_frame004_links_0064 record032_frame004_links_0128))
theorem record032_frame004_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 4 :=
  of_group record032 4 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record032_frame004_indices record032_frame004_graph record032_frame004_links
def record032_frame005_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1060.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1060.count (({ width := 10, code := 0x8d626866118420e82e0781a007fdfd7e9f67d5f17c1ee7ade7799d3711c26fdbb6dda7695a26799a65d946418c5e1755d1715b96b5815d57159559535414d53149519434c5224811d469184210640d003f8fb3e0f53cced3a8e7394e0370d9358d3344cc320c4304bf2ecb92d8b32c4ac2a0a42849f26c982549323c822007c1d0701a46718c5c16c45110411003c0ec2408c2007c1b0681505013048110400f0380c02c0a0240400c0200400 } : Fields).get c.val)
theorem record032_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record032) (record032.maps 5)
      (record032.inverseMaps 5) record032_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame005_links_0000 (interval_append _ 64 128 138 record032_frame005_links_0064 record032_frame005_links_0128))
theorem record032_frame005_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 5 :=
  of_group record032 5 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1060
    Papers.RationalityTen.SharedFrameCatalogue.group1060_facts record032_frame005_indices record032_frame005_graph record032_frame005_links
def record032_frame006_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1d20db7695b0297ecbdf5e5aed5740b42596ac5d60aaf256f2b21568aa054629dd4c4959473a3591868ab44c20c104280f3fc9f9cfb67ca3da9e94dac6c23559a5cd0266c30717e4bc65d12df16a8b285802b61560a8652e2128ecc74438f1bb8d905f82ed16d8b145662a714b0a044e223911908ac44821d10b083c4102010fd07cc3d81e30ee075439c1c90e106ec3681ad0d3067432c18f0c406042f41730b604f426a12e08c84481fc0f6077836c1aa06002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record032_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 6) (record032.inverseMaps 6) record032_frame006_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 6) (record032.inverseMaps 6) record032_frame006_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 6) (record032.inverseMaps 6) record032_frame006_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record032) (record032.maps 6)
      (record032.inverseMaps 6) record032_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame006_links_0000 (interval_append _ 64 128 138 record032_frame006_links_0064 record032_frame006_links_0128))
theorem record032_frame006_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 6 :=
  of_group record032 6 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record032_frame006_indices record032_frame006_graph record032_frame006_links
def record032_frame007_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74170d6ea68567e67767166c66764163562c62361d6136075fc5f35ea5e35d756352a52251c51550e4d34ca4c44b84b04a94a049248843542e42742141c4173ee3e33da3d13ca3be3b53a93a039739138730c2d92d22cc2c52be28327927026225825124b23f23720f2061fd1f61ee1e71de1d51cc1c51bd1b61af1ab1a71a319f19819118a18317d17316b16215915014813f13611310b1050f10eb0d90d50cf0bc0b506005f05c05b05705602802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record032_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 7) (record032.inverseMaps 7) record032_frame007_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 7) (record032.inverseMaps 7) record032_frame007_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 7) (record032.inverseMaps 7) record032_frame007_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 7)
      (record032.inverseMaps 7) record032_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame007_links_0000 (interval_append _ 64 128 138 record032_frame007_links_0064 record032_frame007_links_0128))
theorem record032_frame007_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 7 :=
  of_group record032 7 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record032_frame007_indices record032_frame007_graph record032_frame007_links
def record032_frame008_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x3696b0d278ff1c631c5187f0c5f5bdd79aeedd4b9b716e05bab696bed552e9f13ba72cd899f25a45c828e91aa3145b8a914207c08800fddf73e778aef9dbbae74ae79cb391716e15c037b5feb1d5e2b354aa6d31a594a090d1d233458895109fe3f27c8f69e83c6770ea9ce38c700dc1ae34e680cc992316610be1762dc590ae95629e528a314227c4608890b1f23c46e0d21942d45705e0ba1682c8550a80a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record032_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record032) (record032.maps 8) (record032.inverseMaps 8) record032_frame008_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record032) (record032.maps 8) (record032.inverseMaps 8) record032_frame008_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record032) (record032.maps 8) (record032.inverseMaps 8) record032_frame008_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record032) (record032.maps 8)
      (record032.inverseMaps 8) record032_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame008_links_0000 (interval_append _ 64 128 138 record032_frame008_links_0064 record032_frame008_links_0128))
theorem record032_frame008_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 8 :=
  of_group record032 8 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record032_frame008_indices record032_frame008_graph record032_frame008_links
def record032_frame009_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x251259146e33188bc5a2b1187c3a1b0c85c2a11078341608fe7c3ddecf3793b1d6ea73b99cae470b81b2d76b355a8d367b3598cb6532590c662b1186c25e2d96ab458ac154a95429548a35127d3c994b251248f462250c84411fcf8793b9d4e671371b0d46732184be5d2d964ae552993494482110074381b0c05c29140984a2311074381a0c85c2c110803c1c0d0602c14090401c0c04018080200 } : Fields).get c.val)
theorem record032_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record032) (record032.maps 9) (record032.inverseMaps 9) record032_frame009_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record032) (record032.maps 9) (record032.inverseMaps 9) record032_frame009_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record032) (record032.maps 9) (record032.inverseMaps 9) record032_frame009_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record032) (record032.maps 9)
      (record032.inverseMaps 9) record032_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame009_links_0000 (interval_append _ 64 128 138 record032_frame009_links_0064 record032_frame009_links_0128))
theorem record032_frame009_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 9 :=
  of_group record032 9 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record032_frame009_indices record032_frame009_graph record032_frame009_links
def record032_frame010_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1940c385f72d49686b355952c71628ae656aab1d578aae553aa6d516a7f53a29a14c098e496246d2068e846921c50c284b41920750167f63ee1f18ebc7503a29ce8e5e72637a1b8cdb06c935f1accd4e69934419f0cd66612d89594ab454729a14989a44c62599280924486239917c8a04011f80f847a83c51de8eb473638c1bd8db06c435019d8c9c62a30617a0b8c5a62c215c0a9852427f136896448e23411106e43541970b28540242110080036019206002f81700b605702b00a004e024011807c03c01500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record032_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 10) (record032.inverseMaps 10) record032_frame010_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 10) (record032.inverseMaps 10) record032_frame010_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 10) (record032.inverseMaps 10) record032_frame010_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 10)
      (record032.inverseMaps 10) record032_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame010_links_0000 (interval_append _ 64 128 138 record032_frame010_links_0064 record032_frame010_links_0128))
theorem record032_frame010_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 10 :=
  of_group record032 10 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record032_frame010_indices record032_frame010_graph record032_frame010_links
def record032_frame011_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x6b868867262f62661e6186146105f95f35ef5e95e15da5d55ce5cb5c65c35c05585295215135084fe4d14c94bb4b04a84a249b49348f44943942e42441e4193fa3ed3e73df3d43ca3c53c03bb3b73b23af3433183113042fc2f42c92c22b52ab2a62a129c29629326a26025524a23f23722c22521e21520d2091fc1ed1e71de1d51cc1c41c01b91b21a519618e18918217b17417013712a11f0ff0f60e00d50cc0b60ae05e05d05a05905505402802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record032_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record032) (record032.maps 11) (record032.inverseMaps 11) record032_frame011_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record032) (record032.maps 11) (record032.inverseMaps 11) record032_frame011_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record032) (record032.maps 11) (record032.inverseMaps 11) record032_frame011_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record032) (record032.maps 11)
      (record032.inverseMaps 11) record032_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame011_links_0000 (interval_append _ 64 128 138 record032_frame011_links_0064 record032_frame011_links_0128))
theorem record032_frame011_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 11 :=
  of_group record032 11 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record032_frame011_indices record032_frame011_graph record032_frame011_links
def record032_frame012_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad4a95a519d49cb9c49ba9ae9a298097796d96195694b93e93592c9209139068507f77e27d17bd7a675073d7297116fe6ef6dd6c66b366a66365d65664b63d61a61360a5ff5f35e55d95d25c95bf5b15a05044bd4ae4a048e47e4364274174023f33e83da3c53b637936d36035234533a32d3203133052f52e72d72cb2bc2aa2a029628627526725a2472372262182071f81e71d918317216413612a0fe0f20e70c00b405e05d05a05905505402802702402301f01e01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record032_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record032) (record032.maps 12) (record032.inverseMaps 12) record032_frame012_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record032) (record032.maps 12) (record032.inverseMaps 12) record032_frame012_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record032) (record032.maps 12) (record032.inverseMaps 12) record032_frame012_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record032) (record032.maps 12)
      (record032.inverseMaps 12) record032_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame012_links_0000 (interval_append _ 64 128 138 record032_frame012_links_0064 record032_frame012_links_0128))
theorem record032_frame012_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 12 :=
  of_group record032 12 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record032_frame012_indices record032_frame012_graph record032_frame012_links
def record032_frame013_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x33f658c8d86b0ae11c137fefbde3bc3772eadcdb816e2da5b1b5b6a6d2d44a2341a7dcec9bb2964ec939011c6354668c11661542484107209c0c7e4fbdf5be67bcf51e53c6786f01de3b76b2ca990317614bfd672c557cab951a9d534a554826e4c896527a434708c114220436849039fb3e07a8ee9d83a472ce19bc35e68cce19230a5f8bd1762de4c4921191e63a4680c51822904d8560aa1482884d0980a01382404607c0f01502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record032_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record032) (record032.maps 13) (record032.inverseMaps 13) record032_frame013_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record032) (record032.maps 13) (record032.inverseMaps 13) record032_frame013_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record032) (record032.maps 13) (record032.inverseMaps 13) record032_frame013_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record032) (record032.maps 13)
      (record032.inverseMaps 13) record032_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame013_links_0000 (interval_append _ 64 128 138 record032_frame013_links_0064 record032_frame013_links_0128))
theorem record032_frame013_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 13 :=
  of_group record032 13 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record032_frame013_indices record032_frame013_graph record032_frame013_links
def record032_frame014_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0618.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0618.count (({ width := 9, code := 0x26f369acce633097cba5b2c954a6512793496472290c823f1789446210f86c1e0d058240a00ff7f3f1eaf3793c5e0ef75ba5d0e773395c6e17037dbcdd6ab419ece66b318cc56230d84c05faf97ab95aac960ad552a54aa25027534984b2512290462250e84409fcfa7b3c1d8e872379a0ca622d960a44f2611888361a8d0663118084401f0f07036150a04c24110803c1c0c058281204018080200 } : Fields).get c.val)
theorem record032_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record032) (record032.maps 14) (record032.inverseMaps 14) record032_frame014_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record032) (record032.maps 14) (record032.inverseMaps 14) record032_frame014_indices (Fin.ofNat record032.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record032_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record032) (record032.maps 14) (record032.inverseMaps 14) record032_frame014_indices (Fin.ofNat record032.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record032_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record032) (record032.maps 14)
      (record032.inverseMaps 14) record032_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record032_frame014_links_0000 (interval_append _ 64 128 138 record032_frame014_links_0064 record032_frame014_links_0128))
theorem record032_frame014_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 14 :=
  of_group record032 14 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0618
    Papers.RationalityTen.SharedFrameCatalogue.group0618_facts record032_frame014_indices record032_frame014_graph record032_frame014_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (Fin.cases (record032_frame003_supported hcells) (Fin.cases (record032_frame004_supported hcells) (Fin.cases (record032_frame005_supported hcells) (Fin.cases (record032_frame006_supported hcells) (Fin.cases (record032_frame007_supported hcells) (Fin.cases (record032_frame008_supported hcells) (Fin.cases (record032_frame009_supported hcells) (Fin.cases (record032_frame010_supported hcells) (Fin.cases (record032_frame011_supported hcells) (Fin.cases (record032_frame012_supported hcells) (Fin.cases (record032_frame013_supported hcells) (Fin.cases (record032_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82581b8127e07ce7c57ac78c76a76375f75871a7086f96ca6946636596496405ff5c95a859e59158354b54553e52f52952251c4c34ae4a646542e4083f03e43dc38934d33b32331a30c2dd2d02c92c22b62b02ab2472041f91ec1dd1d319c19418517716d15f15811c11410c0f70ed0e60d80cc0c80c40c109209108e08d07106f06d06b06205f05e05b05905505403803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0x663cc197719e25c3d7feea5a9b4166ecad69abb54a985069c3376694cd9532263b4718d718e19c2d85106609c0e812f0ddc3b26f8d3198b25638c5969aa852ea2943a7b4908e119a2943a8650a9cd344660c79842f8524a09342544908d1161d839c708d41a032c608b916c2c8578831042003f8690d0198320600be1782d8590aa1501c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x73172d72a6ff6f06e86ce69a65a64d6476366085fb5ed5c959956a56355554e50f4de4bd4b64ac49c44443942f41440d4063fb3ca3bd3b438a35933532631c3152cd29c28a2782732632182001f61e51d41cd1c219117116d16715f15b13512f12812211c1121100ed0e70e40d70d10ce0c50bd0b70b40b108608508208106a06806606405b05805705405204e04d03803703403302902702502302001d01c01301200f00e00a008007003002001000 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
def record033_frame004_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0449.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0449.count (({ width := 8, code := 0xb9b8b7b5b4b3b1aeabaaa9a8a6a5a4a29f9c9b9a999895939291908b898886858382807f7e7c7976757473716f6d6c6b6a666362605f5d5c5958565554534f4d4b4948464541403f3d3c3b393837363531302f2e2a29282724232221201e1d1a19181714131211100e0d0b0a090807050403020100 } : Fields).get c.val)
theorem record033_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0449.localPairCheck (smallEmbedding record033) (record033.maps 4)
      (record033.inverseMaps 4) record033_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame004_links_0000 record033_frame004_links_0064)
theorem record033_frame004_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 4 :=
  of_group record033 4 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0449
    Papers.RationalityTen.SharedFrameCatalogue.group0449_facts record033_frame004_indices record033_frame004_graph record033_frame004_links
def record033_frame005_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0379.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0379.count (({ width := 9, code := 0x18bc56270983c15faf56eb65aed363b1586bb57a6d329348a2ce6653197cb639198c44e210e8641a0b04803e1e2ee763adccda6b34da4d060af176b759ac55ea84e26930954a215047f3d9e0ea7332188c05e2e970b4592c15cac4c259249041200f87a3a1c8e06a33178b850271289042200f07032160a84c240f070281007018080200 } : Fields).get c.val)
theorem record033_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0379.localPairCheck (smallEmbedding record033) (record033.maps 5)
      (record033.inverseMaps 5) record033_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame005_links_0000 record033_frame005_links_0064)
theorem record033_frame005_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 5 :=
  of_group record033 5 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0379
    Papers.RationalityTen.SharedFrameCatalogue.group0379_facts record033_frame005_indices record033_frame005_graph record033_frame005_links
def record033_frame006_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0307.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0307.count (({ width := 9, code := 0xfa7cbe1e4f077ba9cce17037dbcd86b355a0cb63b198ac460af172b85b2d558aa54a9548a250a6932984923914894421d067f3e9f0f67a3a1c4e06e369acd46630980bc5c2d954a44f269309047231148842209007c3d1e0ec742d160ac54271309446211007c3c1d0d86830170b0542612088401e0d0602c14090401c0a04018080200 } : Fields).get c.val)
theorem record033_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0307.localPairCheck (smallEmbedding record033) (record033.maps 6)
      (record033.inverseMaps 6) record033_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame006_links_0000 record033_frame006_links_0064)
theorem record033_frame006_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 6 :=
  of_group record033 6 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0307
    Papers.RationalityTen.SharedFrameCatalogue.group0307_facts record033_frame006_indices record033_frame006_graph record033_frame006_links
def record033_frame007_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0268.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0268.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record033_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0268.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record033) (record033.maps 7) (record033.inverseMaps 7) record033_frame007_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record033) (record033.maps 7) (record033.inverseMaps 7) record033_frame007_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0268.localPairCheck (smallEmbedding record033) (record033.maps 7)
      (record033.inverseMaps 7) record033_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame007_links_0000 record033_frame007_links_0064)
theorem record033_frame007_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 7 :=
  of_group record033 7 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0268
    Papers.RationalityTen.SharedFrameCatalogue.group0268_facts record033_frame007_indices record033_frame007_graph record033_frame007_links
def record033_frame008_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0193.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0193.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record033_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record033) (record033.maps 8) (record033.inverseMaps 8) record033_frame008_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record033) (record033.maps 8) (record033.inverseMaps 8) record033_frame008_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0193.localPairCheck (smallEmbedding record033) (record033.maps 8)
      (record033.inverseMaps 8) record033_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame008_links_0000 record033_frame008_links_0064)
theorem record033_frame008_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 8 :=
  of_group record033 8 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0193
    Papers.RationalityTen.SharedFrameCatalogue.group0193_facts record033_frame008_indices record033_frame008_graph record033_frame008_links
def record033_frame009_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xdd36e6371daa2d3e69c338d8f4c1a609b03980cb7d5b82d8d5e8a94524a911476a354cf24e521690647f23d909883e4182030ffc7f03f39ca8e3a71734f98f8c0a5fe2fc17ccac650e27d13cc9de4e923791688a0440215908483436f1878c185fc2f617809904b023d11508784061fa0bf05d02d614d0a184e824c11508383e01d2094049824011e07103781b40d606202f81780b605902a815007003701a00cc052027012808c04001d00e004c02400f00700280100070018008002000 } : Fields).get c.val)
theorem record033_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 9) (record033.inverseMaps 9) record033_frame009_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 9) (record033.inverseMaps 9) record033_frame009_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record033) (record033.maps 9)
      (record033.inverseMaps 9) record033_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame009_links_0000 record033_frame009_links_0064)
theorem record033_frame009_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 9 :=
  of_group record033 9 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record033_frame009_indices record033_frame009_graph record033_frame009_links
def record033_frame010_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0845.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0845.count (({ width := 11, code := 0x4e09bf37a5c4af95526641c698c517a2c43585b0960abfb7cef89ed3d6768e4dbf3796e4db19eb35660c7d8d31361aba16f2da586a9147a87504a012ba3544e8850f2163da790f09d5398718e09882dc5a4b215d2b04b49491e226438839031ae358688c117a2ec578a814827c4e07e0fa1ec3d06c0d41a03385e0b816c2c8570a61481c0370680cc1482704a08c1001d03804c0900f01c0280400700600800800 } : Fields).get c.val)
theorem record033_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record033) (record033.maps 10) (record033.inverseMaps 10) record033_frame010_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record033) (record033.maps 10) (record033.inverseMaps 10) record033_frame010_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0845.localPairCheck (smallEmbedding record033) (record033.maps 10)
      (record033.inverseMaps 10) record033_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame010_links_0000 record033_frame010_links_0064)
theorem record033_frame010_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 10 :=
  of_group record033 10 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0845
    Papers.RationalityTen.SharedFrameCatalogue.group0845_facts record033_frame010_indices record033_frame010_graph record033_frame010_links
def record033_frame011_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0769.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0769.count (({ width := 8, code := 0x9e9d9c99989796928e8d8c8b88878684807d7c7b7a777371706f6e6968676564636261605f5d5c5b5a59585655545352514d4c4b4a4948474544434241403c3b3a393837363231302f2e2d2c2b2a29282625242321201f1e1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record033_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record033) (record033.maps 11) (record033.inverseMaps 11) record033_frame011_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record033) (record033.maps 11) (record033.inverseMaps 11) record033_frame011_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0769.localPairCheck (smallEmbedding record033) (record033.maps 11)
      (record033.inverseMaps 11) record033_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame011_links_0000 record033_frame011_links_0064)
theorem record033_frame011_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 11 :=
  of_group record033 11 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0769
    Papers.RationalityTen.SharedFrameCatalogue.group0769_facts record033_frame011_indices record033_frame011_graph record033_frame011_links
def record033_frame012_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0362.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0362.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record033_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record033) (record033.maps 12) (record033.inverseMaps 12) record033_frame012_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record033) (record033.maps 12) (record033.inverseMaps 12) record033_frame012_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0362.localPairCheck (smallEmbedding record033) (record033.maps 12)
      (record033.inverseMaps 12) record033_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame012_links_0000 record033_frame012_links_0064)
theorem record033_frame012_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 12 :=
  of_group record033 12 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0362
    Papers.RationalityTen.SharedFrameCatalogue.group0362_facts record033_frame012_indices record033_frame012_graph record033_frame012_links
def record033_frame013_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0329.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0329.count (({ width := 7, code := 0x74e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record033_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0329.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record033) (record033.maps 13) (record033.inverseMaps 13) record033_frame013_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record033) (record033.maps 13) (record033.inverseMaps 13) record033_frame013_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0329.localPairCheck (smallEmbedding record033) (record033.maps 13)
      (record033.inverseMaps 13) record033_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame013_links_0000 record033_frame013_links_0064)
theorem record033_frame013_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 13 :=
  of_group record033 13 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0329
    Papers.RationalityTen.SharedFrameCatalogue.group0329_facts record033_frame013_indices record033_frame013_graph record033_frame013_links
def record033_frame014_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0249.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0249.count (({ width := 9, code := 0x12a93c8e3f1c8cc52210983c1a0b027f3edeef074ba1cae470365a6d268b398cc4613017ebe5eae96eb35729d46a04ea71309146a2912863f9f0f4793b9d8ea6d349a0ce6531970b6592b954a6522592892462210c82401f8f87a33190c4602b150a450251208c44200f87834190c05c2813090441e0e0682c1409040180a04018080200 } : Fields).get c.val)
theorem record033_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record033) (record033.maps 14) (record033.inverseMaps 14) record033_frame014_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record033) (record033.maps 14) (record033.inverseMaps 14) record033_frame014_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0249.localPairCheck (smallEmbedding record033) (record033.maps 14)
      (record033.inverseMaps 14) record033_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame014_links_0000 record033_frame014_links_0064)
theorem record033_frame014_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 14 :=
  of_group record033 14 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0249
    Papers.RationalityTen.SharedFrameCatalogue.group0249_facts record033_frame014_indices record033_frame014_graph record033_frame014_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (Fin.cases (record033_frame004_supported hcells) (Fin.cases (record033_frame005_supported hcells) (Fin.cases (record033_frame006_supported hcells) (Fin.cases (record033_frame007_supported hcells) (Fin.cases (record033_frame008_supported hcells) (Fin.cases (record033_frame009_supported hcells) (Fin.cases (record033_frame010_supported hcells) (Fin.cases (record033_frame011_supported hcells) (Fin.cases (record033_frame012_supported hcells) (Fin.cases (record033_frame013_supported hcells) (Fin.cases (record033_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18d4c5061cb075806bee59aac71628aa653026d533098f4aca4d9258871433a12906081b4071f70f8c75e3a81d14e7472f3931b80d8c6b234c99f0cc25ed2ef1748b8e5bb2d91698b2e58a2bd95b8aca50827513489804b224f124090445f2280f8478a3bd1c60db06c435419d8c9c62a2b81528a4c4ba23411107803861b90d686583081740b184382020d706481bc0dc05d02e016c0ae05601c80dc06c026012809004602100f8078028013009004001e00e0050024010005002000c002000 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x12b24dc728d91a231c5f8b91221f43285707e09be57b4f4de33bc762e15bdb756dcda9afb5864cc858eb19628c3d7caf25cab75692c3526a1d3f26f4cc9751922a4468750ca0e4107b0f29db3a8730e19bc36a6b8d219c326624c197e2f05bcb014f28a4cc9291c2103e4768e01ae338640b115a2704b8640c61882a8540a613c270340660c81282404607c0f01502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36e9a56c0a5fb2f7d796bb55d02ca9604adb55a2a314c49944b7257123c8fa473a0c101c7f73f29f6cf6a7a536b1b08d5669734099b0bec5ce2d39600ab052e23010e88503ea1e30ecc5f82da1618ac454e28113888e446422b112087442c20f10408043f41f30f6078c3b81d50e707083681a60cb86042e616c0a9051027a12d093047c2320f607803681aa07103781b80ba05c02d815c0ac03901b80d804a024011807c03c01500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x703b7e1bd2dd66e1b6c1a76d1367fb33194cc905d12e4d708b715af2d2d5acaae54d299d482a2b4d7a6a134299a4c9a63130a97e4bba5c12d29624aea55929e948498a48d238916485240d1f88f4476a398ea67283899b58d5e6992f49760b8c5b22cf9630ae85612a794f4a5651824d11dc8ce45921e10ac8384001f78f7c6f43691ab8d0c66031d1828bc85c02ce15e0aa44562080fc07a839a1bc0d686443001700ab854029214209d84d025e128090846821e10908183f01e00e807103701b20d2049824812207003781b804c025012008c04001f00f004402000f007002c014009 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record036_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 128 140 :=
  interval_of_check _ 128 12 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 140 record036_frame001_links_0000 (interval_append _ 64 128 140 record036_frame001_links_0064 record036_frame001_links_0128))
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1079.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1079.count (({ width := 11, code := 0x16caabd3899328235c668c116229c4b8850f61bc2f855089f5be47b8f45e53c577aec9d5b8f716e19c037c6f0d058cb16622c31842e65c4b756a2cd58eb015d2b4552a854c25049290d18a2a43c858fa9ef3d2778eb1cd3846f8dc9b035268cae15629e50c9d9362604688a10f2124107f8f81e23b0730df1b034c668c317c2b85508610a1a0338540a60dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1079.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1079
    Papers.RationalityTen.SharedFrameCatalogue.group1079_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x33fd86ebef554297d3b69c74dc26a93369904bfa5b92b894b49ca4b50e2863426a0b503080a3fa9f68f8875e3a81d14e7472f3931ac8cc065532198b4c385ea2ed973cb885b82d896a4b3458d2bf15c4acc4d226192c090a47222e91388083f21f18f5878e3be1d68e6c71837b1b60d885702a914a89f44d625a12407f43dc1e00e8870c3721a70ca060c2e61640a78500260111080835419009204881ac0d405702b00dc06c03301900a8052028013807c03c01d008804001e00e005002400e0060028010006000 } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
def record037_frame003_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xffde3bbc6ecd919bb30654c8d9031c62ec458730b60abf1662c8584aed5aab2558a995028b510a1541a804fc9912b25349e9292322f4588a51222043c8690aa1241c821011cb38c704d81ab34667cc197e2f05c8b796b2cc588af15c2b25548f91a22a438839031fc3a4720de1b0348660c617e2ec5b0b11542945109a12a220428710e01742e04b0940dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record037_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record037) (record037.maps 3)
      (record037.inverseMaps 3) record037_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame003_links_0000 record037_frame003_links_0064)
theorem record037_frame003_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 3 :=
  of_group record037 3 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record037_frame003_indices record037_frame003_graph record037_frame003_links
def record037_frame004_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb1aa92a5394e90389588b88087286385584683a82d81f80c7f975073f72b70c6f96ee6dc6c46b166a66365d65664b63d5e259d58f58256e56053e53452a51f5125044fb4f24e74dd4cf4c04364244143e73d93c33b437a37036335534833d32d3203133052f52e725a24a23a2242162081f91c21ba1ae1a019118316f16115214213512911a1090f30e80bd0b308c08b06906805505403703603303202a02902802701f01e01d01101000f00e00a009007006005004003000 } : Fields).get c.val)
theorem record037_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record037) (record037.maps 4) (record037.inverseMaps 4) record037_frame004_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record037) (record037.maps 4) (record037.inverseMaps 4) record037_frame004_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record037) (record037.maps 4)
      (record037.inverseMaps 4) record037_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame004_links_0000 record037_frame004_links_0064)
theorem record037_frame004_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 4 :=
  of_group record037 4 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record037_frame004_indices record037_frame004_graph record037_frame004_links
def record037_frame005_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x128234453808fa5df3ba76cec9d53a673ce6dcc39171ce19ab350692cf99ab31658c7d8b2fb5eebd578aeb5ceae54c296524a31432704da9a133a5f4b896129a4f4909051d2043fc7dcf21df3a6720d71a9348678cb190312610c197c2f65d4a113c2684a88f91922c3f47d0f61e03a4718df1b2354678ca18c3045d8b315c2744c0800fe194320530a40dc1b0330640a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record037_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record037) (record037.maps 5) (record037.inverseMaps 5) record037_frame005_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record037) (record037.maps 5) (record037.inverseMaps 5) record037_frame005_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record037) (record037.maps 5)
      (record037.inverseMaps 5) record037_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame005_links_0000 record037_frame005_links_0064)
theorem record037_frame005_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 5 :=
  of_group record037 5 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record037_frame005_indices record037_frame005_graph record037_frame005_links
def record037_frame006_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0563.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0563.count (({ width := 11, code := 0x140272cd48f716a1b42f85509e10c1b82d03202c017eefbdcfb9d72ce29c1b7d6e8da5b0347680ced9c33365ac2d77aea5c4b61682c9584af55cab255cab55329f538a5947a4c4949151aa2e44887504a013f27d0f69e53c275ce89cc3846ecc017b2e258cad1522924b49412123a45c881071fe3dc770e41b233c610b2152238450740e616c2d0490900d41a0310600a81482804e07c0f01d0220400780e0140240380600a01001800 } : Fields).get c.val)
theorem record037_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record037) (record037.maps 6) (record037.inverseMaps 6) record037_frame006_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record037) (record037.maps 6) (record037.inverseMaps 6) record037_frame006_indices (Fin.ofNat record037.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record037_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0563.localPairCheck (smallEmbedding record037) (record037.maps 6)
      (record037.inverseMaps 6) record037_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record037_frame006_links_0000 record037_frame006_links_0064)
theorem record037_frame006_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 6 :=
  of_group record037 6 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0563
    Papers.RationalityTen.SharedFrameCatalogue.group0563_facts record037_frame006_indices record037_frame006_graph record037_frame006_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (Fin.cases (record037_frame003_supported hcells) (Fin.cases (record037_frame004_supported hcells) (Fin.cases (record037_frame005_supported hcells) (Fin.cases (record037_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0xb956bad3d9caff486834fd9eb3463bc508930e60a40e80eff5fb3ed7c8f7dd83a4740e19c0b7c6f0dc5b4360694d0178ae45b0af951a9f516a05392624ae9492323f456890f91e53ba6ecd59a13205fcb81672c0554a59442724a47c0f11d836c6a8d018c3005d8ab0fe1f0328630b41642a8510a01381a8340640a81402704c08c1081f03c0700a0130240400700b0140240380400600800800 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x75236dd814bcb5daacb560aade544a6452d695947d235917e8984182084ff27e73eb1f1cf6e6d634b9a04bf25d12d515548ba4372128f1874438b1b20bf05da2c51598a8852628311c88c845622410e885841e1fa0f9878c3b81ce0e106d034c19d0c786202f61750a9051027a13508c84301fc0f6078036c11a06d03501840c005f02e816c0ae05602a00d4064029014009c04a02300f807803801500a004c024011008003801800a004801c00a0040018008002000 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x7226e668867266463f62e61b6045af59658855554252f5174da4ce4b14a349949348d45b44743c4184093f93e038c37836d34833832b3192ed2e32cd2c42bb2b82b428627a27126625924d2452302262102071f21e41d51c41b51a319718b18715f14613a12d0fb0eb0d80cd0c50aa08106706405d05c05b05905705305205003503202902802702502301f01e01c01501401301201101000e00c00a009007005004003002001000 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x8890b9fcbee7d0f51e53bd75ade1b73696aed39a333b63cc65843025f8be178ad258caf955aa1530a1928a464868ad112174167ccf71e03b6754e79ca3626acd29a133865cc81822f65b4b295629a50c9a92e23e45c8890c1ec3b4730e018a2ec580a814824c3b8610bc1582a8540a41402604b0920d01882905009c1282303e0780e01502804c090110200380600a01201c0280400600800800 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b74c0a5e5aed55b6a4f51d28393729a54ca26052dc95c4a324311f48304102038fee7e53ec1f1cf6e6d634b9a04b4e51b283136890a47123011348744282090f6078c2fc1760b685862b11520a4c50623911908ac44821d10b083c3f41f30f1877039c1a60cf065c30417b0ba859c2c01590a9052c28813d09a04b424c11f08603dc1e00da04681bc0dc06a02f01740b605702b015006e036019009804a02300f807803801500a004c0240110080038014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa989d49ba9ae9488f48e78c289488987e86f86085284581c80975073c72870f6fc6ec6da6c866a65664b5e258f58256053f53752d5225155074fa4da4cc4364264164003f13e53d73c737936d36035234533a32d3052f52d72cb2aa25a2482382081f91e91cd1c21ba1ae1a019118317116315414411c0f30e80bf08706d06c06805c05b05905505405203703603202602502301f01e01c01501401301201101000e00a009008007006005004003001000 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x39f9cbce3c6df3679af8d576a83525a84d3b69a3499a30d0a682b3dd9e0b825b7ad71698b3c5942bf55b0ab050b280d3e09e04e826f132296c4a223bd1d08e146d234d1988c746022e51648a7451226512477d3839b9cdae67233218dcc4c5b22c91608a3a50f27113449744ad253128092c48f24412108fa47523791ac7ac3ab1cb0c6453227a1358984490238114886041c1b60cb86202fc1650aa851826a12b07c83c01d20e206e03500da06b03501780b805b01c00dc06c03301900a4050027012008c01e00e00580280120070028010006001 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record044_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 128 131 :=
  interval_of_check _ 128 3 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 131 record044_frame001_links_0000 (interval_append _ 64 128 131 record044_frame001_links_0064 record044_frame001_links_0128))
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x66232c5940c5961fb0e17dab435952c5158eaae553a97d3ba9c94dda6b133c9914b9253d25e92847c238914a88243a215908082b4099fecfac7c03a81ce8e4c6d835f1acccc05ea2ed973cb885b82d8965caf65652ab14d0a4c4f926d934895e4a0249120c8e24011f80f847a83c51de8e6c6f63621a80c9c62a2e31610ae052427f13689684922000f8878c3a81c60dd06983261820b905842a813d09684902280fd07783881b40c404702340d606a01980c8054029014009c04c024011808003e01e00e0054028013009004401e00e0058028012007 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record045_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record045_frame001_links_0000 (interval_append _ 64 128 132 record045_frame001_links_0064 record045_frame001_links_0128))
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xd25a2f3f66ccc796322e15c137deee5cdb81692bdd73ad5582aa549a7d4b28bd0c9ef39e66cb995726645c7b8d719e2ec56849072063eb7bcf51db388700de1b7b636b2d359f32a63ac297faec5b6b395daae546a714ca6e4c896527a434708a10da073f67a8ee9cb3786bcce19230a5fcbd9642bc550a513f2664848b1081f03c0758e01ac344638be1682a85289a0f41e4308600660c81502905009c130240460800f81e0380540a0130240440780e01602804807 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record045_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record045_frame002_links_0000 (interval_append _ 64 128 132 record045_frame002_links_0064 record045_frame002_links_0128))
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x9c536a684c296f2c24bc708d11722744687b08dff3f97e8fbdf43e17b0f35e03bb758e8dc83856f8dc5b435f6aad3da3b4364ec7586afa5dab8d652a353aa5946a844fa9d9362614b89312123144c87107a053f27d0f79ca3886fcdb9ac348668c81802f25a4ae95028c4f89912923e4648a9001f63d8780ea1ca3706a8d0194318628bd16e2cc570a81462744c8910ee1d8310610620c01482804e0981282304407c0f01d0360540a0130240440780e01602804807 } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record045_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record045_frame003_links_0000 (interval_append _ 64 128 132 record045_frame003_links_0064 record045_frame003_links_0128))
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
def record045_frame004_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x7e4fb5f4be17b6f5de4ba0728e3dbf3756dcd69a3340674cd59832b64ac798cb1660cbfd7a2ef5d4b856bad0592b0d5cab451ea093f2684be96520a274428690aa10416818ff9fb3e879cef9d73a673ce11b93686c0d59802f25c4b59652be558a614527e4c49611f23044c830ff1f43dc790e41c23706c0d419e3185f8ba1682b8560a81462844d894120238458850e41c42e85c0620c01502905009c130240460800f81e0380540a0130240440780e01602804807 } : Fields).get c.val)
theorem record045_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record045_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record045) (record045.maps 4) (record045.inverseMaps 4) record045_frame004_indices (Fin.ofNat record045.n i)) 128 132 :=
  interval_of_check _ 128 4 (by decide +kernel)
theorem record045_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record045) (record045.maps 4)
      (record045.inverseMaps 4) record045_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 132 record045_frame004_links_0000 (interval_append _ 64 128 132 record045_frame004_links_0064 record045_frame004_links_0128))
theorem record045_frame004_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 4 :=
  of_group record045 4 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record045_frame004_indices record045_frame004_graph record045_frame004_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (Fin.cases (record045_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x38e5af2d576a83525a84d3b69a3429a08cfd678b3a97aab825b7ad71698b3c5942ac1542a8d539297d42ca034f827813a09bc4a224d5242906479a3bd1d08e146d234d1988c746022e51648a9451226512488e3c01cb4e3870d37e9bb4dba6723319940c646212ec171cb705a82cc1620a3a50e27d93749984c826092e89664ad2531284934493246120c8fa47523791b06322b91548a6451427a135887441c1d60e306d834e1970c404e82560f707803a41c40d405802bc13809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record047_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record047_frame001_links_0000 (interval_append _ 64 128 135 record047_frame001_links_0064 record047_frame001_links_0128))
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x33f993ec7c636317d8a4c4561d2fc17d2bd35d5ae5562aae956bab2557cab0554297d4a2a3b50e28253b69c74dc26a9336990496247520a8e5467a3151668a144821f90e486c42aa0fd05480c3fb9f64f867bb3939bdcdca6da3659b00d6866032b9914c526182f81780ba85c92de96ccaca55c2a494c0a4451c28593f09da4de269933c9764a824d121c8e845c22691246c430617a0b8c5a62c215c096c4921fd0f707803a21c30dc85982a210f07f83c81ca0c705502a413809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record047_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record047_frame002_links_0000 (interval_append _ 64 128 135 record047_frame002_links_0064 record047_frame002_links_0128))
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
def record047_frame003_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e51d1ae3070db80dbdadd46deb4c5a38d0566cb305746b455982c69610af5570a97d4a2a3c50ea8253789a84cba6112e295f473a36118a8a6449a22d0f286742aa11506682840ba014fe47dc3e59ec8f4479d3379844bf85e62ea1704b5a52b28e94209d24d524411d08c645021e90ac7663a41c88dc86be3571a28ccc64231117f8bd05c62d115f0aa052e27e13709a43d81c90e106ec3681ad0d3060c2f81600ac854829614409e84682260f5077039c1c00d305802bc13809b03581a80b805b01980c8048023007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record047_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record047_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record047_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 3)
      (record047.inverseMaps 3) record047_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record047_frame003_links_0000 (interval_append _ 64 128 135 record047_frame003_links_0064 record047_frame003_links_0128))
theorem record047_frame003_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 3 :=
  of_group record047 3 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record047_frame003_indices record047_frame003_graph record047_frame003_links
def record047_frame004_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8b987e86685f85985384d84682381d81780c80579776275474873e7347286e46d76cb6b66a867366365564b63f6325e65d65c85b059e59858f58757f57756f56a56155955054553d53352b5284b447946945b4514454383ec3dc3ce3b63a437436635a35034633a2f62e92dd2c82ba2b52ac2a429c29428c28727e27626d26225a2502482451d81b71b01a81a119919016916214513e13612f12711e0f70f00d40d00cc0c80c00aa0a909c09b06b06a05c05b03303202402300f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record047_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record047) (record047.maps 4) (record047.inverseMaps 4) record047_frame004_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record047) (record047.maps 4) (record047.inverseMaps 4) record047_frame004_indices (Fin.ofNat record047.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record047_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record047) (record047.maps 4) (record047.inverseMaps 4) record047_frame004_indices (Fin.ofNat record047.n i)) 128 135 :=
  interval_of_check _ 128 7 (by decide +kernel)
theorem record047_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record047) (record047.maps 4)
      (record047.inverseMaps 4) record047_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 135 record047_frame004_links_0000 (interval_append _ 64 128 135 record047_frame004_links_0064 record047_frame004_links_0128))
theorem record047_frame004_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 4 :=
  of_group record047 4 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record047_frame004_indices record047_frame004_graph record047_frame004_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (Fin.cases (record047_frame003_supported hcells) (Fin.cases (record047_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x17d6e6d7fac7576ab5269a33065b4af8ad14224c4081500dff3f87daf91ef3d3760eb1d43856c0d29a032c642c6d78ac857cab551a9f52a9c9272474828ad11a133e4724dd9b2356684cd1702b8530a31392504607c0f11d83846d8d518c3005d8b61041fc3e0690ca18c2d0560aa1402784e0720e01a8340640a81402604808c1081e03a0700a01302003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x7b177972971871370d6c663d62d61b61258c58257456852e52852251d51450e5074fb4c64bc4b648144d42e42240c3ff3f93c238a37536335334b33e3172ff2f92f42e62e02d529425123d23222721720a1d01ba1a819f18e17d16913512611e10b0fa0f20d50cb0c60c108c08a08706e06a06805e05a05905405305203803703403303102a02802602402302101e01d01c01401301000f00e00b009008007004003002001000 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (smallEmbedding record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
def record048_frame003_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0375.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0375.count (({ width := 8, code := 0xb8b5b0afaeadaaa5a4a3a29d9c9b9a94939291908f8e8d8c8b8a858281807f7e7d797675747372716b696867656463615e5d5c5b5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record048_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record048_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0375.localPairCheck (smallEmbedding record048) (record048.maps 3)
      (record048.inverseMaps 3) record048_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record048_frame003_links_0000 record048_frame003_links_0064)
theorem record048_frame003_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 3 :=
  of_group record048 3 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0375
    Papers.RationalityTen.SharedFrameCatalogue.group0375_facts record048_frame003_indices record048_frame003_graph record048_frame003_links
def record048_frame004_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0447.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0447.count (({ width := 8, code := 0xb8b5b0afaeadaaa5a4a3a29d9c9b9a94939291908f8e8d8c8b8a858281807f7e7d797675747372716b696867656463615e5d5c5b5a595352504f4e4c4b4746454342413f3e3d3c3937363331302e2c2b2928272322201f1e1b1a181716141312110f0e0c0b0a080706050403020100 } : Fields).get c.val)
theorem record048_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record048_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0447.localPairCheck (smallEmbedding record048) (record048.maps 4)
      (record048.inverseMaps 4) record048_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record048_frame004_links_0000 record048_frame004_links_0064)
theorem record048_frame004_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 4 :=
  of_group record048 4 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0447
    Papers.RationalityTen.SharedFrameCatalogue.group0447_facts record048_frame004_indices record048_frame004_graph record048_frame004_links
def record048_frame005_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0304.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0304.count (({ width := 8, code := 0x8c8985848382807c7b7a797675747371706f6e6d6c6b6a69686763605f5e5d5c5b595655545352514f4e4d4c4b4a49484544434241403e3d3c3b3a393837363534333231302f2e2d2b2a29272625232221201f1e1d1b1a1918171514131211100f0e0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record048_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record048_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0304.localPairCheck (smallEmbedding record048) (record048.maps 5)
      (record048.inverseMaps 5) record048_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record048_frame005_links_0000 record048_frame005_links_0064)
theorem record048_frame005_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) : Supported record048 5 :=
  of_group record048 5 (smallEmbedding record048) (small_cells_exact record048 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0304
    Papers.RationalityTen.SharedFrameCatalogue.group0304_facts record048_frame005_indices record048_frame005_graph record048_frame005_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (Fin.cases (record048_frame003_supported hcells) (Fin.cases (record048_frame004_supported hcells) (Fin.cases (record048_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x67466c6325f05bf5ad5a855d5245195114c94bc4b149e49048547f46b43b3f93c43b03ab37033d33532f2ec2e22db2ce2c32bc2b62a927826d26424622d2242172101ed1d11b91a519117e17416414212d12511e1060fe0ee0e00d50c908107f06b06906706405b05a05705505105004f04e03903703503202902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
def record049_frame002_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x65a6566335f85bd59d5955555185044f64bb4b44ae4a249b4954904834624223e63c83bf37b33c32931d2e02d82d22c62c02bb2b72ae28928027524922721d2061f91d51c41b119818617216815513e12c1211140f60ec0d80c50bc0b808608306e06c06a06705f05e05b05905505405305203803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record049_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record049) (record049.maps 2)
      (record049.inverseMaps 2) record049_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame002_links_0000 record049_frame002_links_0064)
theorem record049_frame002_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 2 :=
  of_group record049 2 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record049_frame002_indices record049_frame002_graph record049_frame002_links
def record049_frame003_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x518a2b3be5e48b8ef1d22641d82702df03da7a4f19df3b9764e99bbb3b612bd578ac352aa2940a5c4b0949242404788dd1620c4047e4ee1c33726a0cf1842ea59cac94e2764d49291320a3f47b8dd1aa3205d8b616021c4286e0da1ac340600be1742d8570ac1542a03906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record049_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record049) (record049.maps 3)
      (record049.inverseMaps 3) record049_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame003_links_0000 record049_frame003_links_0064)
theorem record049_frame003_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 3 :=
  of_group record049 3 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record049_frame003_indices record049_frame003_graph record049_frame003_links
def record049_frame004_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd1567db029654a89525a8e93228fa46b22fd06081c4061fa4fac7c73db9e54dac5f62aa945ca0c45d1e30e887162fc1740b6056a2a21498a0c4c223911908ac41e1fa0f9878c3b81c20da069832e18a0bd85d42ce1520a204f426a12108c84301fc0f6078024811a07103781b40d406103001740b605702b01540a803901b80d4064029014009404601f00f007403801500a004c0220100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record049_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 4) (record049.inverseMaps 4) record049_frame004_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 4) (record049.inverseMaps 4) record049_frame004_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record049) (record049.maps 4)
      (record049.inverseMaps 4) record049_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame004_links_0000 record049_frame004_links_0064)
theorem record049_frame004_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 4 :=
  of_group record049 4 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record049_frame004_indices record049_frame004_graph record049_frame004_links
def record049_frame005_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x47e8f114210bf87d2f91dcb93712e0db0b5a6aad35a2b3f676cbd88adf570aa952a764a492922222436855052033fc7e8f81d5398710d619731e610c01672ae5249c92922e440808f21d03906f0cd18c2ec580ac1501fc3d8680cc190308580ae1502904e09a1302583906e0d4190290500941181f03c0740e01502804c0881001c0300500901001c0280400600800800 } : Fields).get c.val)
theorem record049_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record049) (record049.maps 5) (record049.inverseMaps 5) record049_frame005_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record049) (record049.maps 5) (record049.inverseMaps 5) record049_frame005_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record049) (record049.maps 5)
      (record049.inverseMaps 5) record049_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame005_links_0000 record049_frame005_links_0064)
theorem record049_frame005_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 5 :=
  of_group record049 5 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record049_frame005_indices record049_frame005_graph record049_frame005_links
def record049_frame006_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x78e7867396f36be69e69564e6025ec5dd58557d57356355654c5405274ef49844d42c4233d63a539538b33b32e32430b3002fb2f12dd2b12a729927224f2472312282071f11dd1c81ba1a219818116415214713d11a10d0fd0eb0e30dc08c08706e06c06a06705e05d05a05805405305205103803603403102902802502301f01e01d01c01501401301101000e00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record049_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record049) (record049.maps 6) (record049.inverseMaps 6) record049_frame006_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record049) (record049.maps 6) (record049.inverseMaps 6) record049_frame006_indices (Fin.ofNat record049.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record049_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record049) (record049.maps 6)
      (record049.inverseMaps 6) record049_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record049_frame006_links_0000 record049_frame006_links_0064)
theorem record049_frame006_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) : Supported record049 6 :=
  of_group record049 6 (smallEmbedding record049) (small_cells_exact record049 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record049_frame006_indices record049_frame006_graph record049_frame006_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (Fin.cases (record049_frame002_supported hcells) (Fin.cases (record049_frame003_supported hcells) (Fin.cases (record049_frame004_supported hcells) (Fin.cases (record049_frame005_supported hcells) (Fin.cases (record049_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x381d8f8c685d1285d4069ae4d3a68130896f4b425612a291b489a4311fe8f747823a91b883234199b8bc65d22e015d0a7a52b28193c88ce454221108c8224011f88f446e83631a88c1459c2bc14a0a0c3f01e50e986d03441920c105882ac14f0a4050427413308b84101ec0ef074824811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
def record050_frame002_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3bdda26cfb605293d4749b64d1264528c90c47d234917e83040f2030fd27d83e39edcf2a6d628d941890446e22e90487b03c61cf0e2c5f82ea16c0ad45482931418984472232115883c3f41f30f1877034c19e0cb862830417b0ba859c2c01590a9052c28813d09084301fc0f7078024811a06f03501880c206002f01740b605702b01540a803701900a8052028013009404601f00f007403801500a004c0220100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record050_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 2) (record050.inverseMaps 2) record050_frame002_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record050) (record050.maps 2)
      (record050.inverseMaps 2) record050_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame002_links_0000 record050_frame002_links_0064)
theorem record050_frame002_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 2 :=
  of_group record050 2 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record050_frame002_indices record050_frame002_graph record050_frame002_links
def record050_frame003_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xeeda934b63cad55728d514a1d3da724de99d3224e49491d2123e4768e519a1835e6a0c39843025d4b61692c2578a41442824f09c1352664b48f11b230430819001f03d46f8db1b034c678cc194310608c017e2f85e8bc1702d4598b21622384486d0d01802f85e0b816c2c8550a814c290370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record050_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record050) (record050.maps 3) (record050.inverseMaps 3) record050_frame003_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record050) (record050.maps 3)
      (record050.inverseMaps 3) record050_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame003_links_0000 record050_frame003_links_0064)
theorem record050_frame003_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 3 :=
  of_group record050 3 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record050_frame003_indices record050_frame003_graph record050_frame003_links
def record050_frame004_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6df67366c6325ae5a857156655d54152d5245185114c94bd4b149e49148547f46b43b3b13ab38137837035934533d33432f2ec2e42db2ce2c52bc2b62a927826d26424622d2242172101b91af1a519118817e17416415814c14213712d1251060ee0e00d60c908107f06906405c05b05a05805705505105004f04e03703202a02902802602502301f01e01d01c01501401301101000e00a009008007006005004003002001000 } : Fields).get c.val)
theorem record050_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record050) (record050.maps 4) (record050.inverseMaps 4) record050_frame004_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record050) (record050.maps 4) (record050.inverseMaps 4) record050_frame004_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record050) (record050.maps 4)
      (record050.inverseMaps 4) record050_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame004_links_0000 record050_frame004_links_0064)
theorem record050_frame004_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 4 :=
  of_group record050 4 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record050_frame004_indices record050_frame004_graph record050_frame004_links
def record050_frame005_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0981.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0981.count (({ width := 11, code := 0xfb5db3b072cd7dacb3665cca18b309606be17a2cc58cb015bab0554a9d4e28b4a693d17a2c452865062063f67d4e59c63826dcd71a9348670c117c2ec598ae15929e5248f918226420818fe1f23c0748e41bc360690cc1702984f09a12a1c4368600b8150298520a21402784b094124240370640a81482804c0941181f03c0740e01502804c0881001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record050_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record050) (record050.maps 5) (record050.inverseMaps 5) record050_frame005_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record050) (record050.maps 5) (record050.inverseMaps 5) record050_frame005_indices (Fin.ofNat record050.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record050_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0981.localPairCheck (smallEmbedding record050) (record050.maps 5)
      (record050.inverseMaps 5) record050_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record050_frame005_links_0000 record050_frame005_links_0064)
theorem record050_frame005_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 5 :=
  of_group record050 5 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0981
    Papers.RationalityTen.SharedFrameCatalogue.group0981_facts record050_frame005_indices record050_frame005_graph record050_frame005_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (Fin.cases (record050_frame002_supported hcells) (Fin.cases (record050_frame003_supported hcells) (Fin.cases (record050_frame004_supported hcells) (Fin.cases (record050_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xdfd68c33e99c4b42596ac5d512a4951ca8953228d146022b113486442120c104280b3fc9f58f907b73ca1838bf25e32aa9454a0a4f122e8e747183781b30cc061c2fc1768b5c58a2a214a0a0c4c023911908ac3f41dd0eb07403921c20dd86d035a1a60ce865831e17c0ba85982a414409e84d424211908984301ec0db04681ec0da06a03081800b605a02c015c0ac05402180d4064029014008c04402000f807803801500a004c02200e006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
def record051_frame002_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb65af0ad4ac5a21a15a0f9b297e96d95e90986184a8368247f77d47c07ae79477f75574272b6fd66e6616596085de5d55c95774ee4e04d24c449b48247746b45744842841d40f3ef3bd3ae3a43412f92e92d82c72b72ad2a12932862732632532252151f11cd1b51a819716b1561451351030cd08d07b06d06a06106005b05a05805705605404303503202902802302202001f01e01c01501401301100e00d00c00b00a009007005004003002001000 } : Fields).get c.val)
theorem record051_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record051) (record051.maps 2) (record051.inverseMaps 2) record051_frame002_indices (Fin.ofNat record051.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record051_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record051) (record051.maps 2)
      (record051.inverseMaps 2) record051_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record051_frame002_links_0000 record051_frame002_links_0064)
theorem record051_frame002_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) : Supported record051 2 :=
  of_group record051 2 (smallEmbedding record051) (small_cells_exact record051 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record051_frame002_indices record051_frame002_graph record051_frame002_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSmall.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (Fin.cases (record051_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x38fdc5ee286d83615ae4d176763365970cb1655329193ac96648b2298f8bae5862b5558eab95582ab1548a9b4f726612ec95349e24d120c8e5461a281112881429a12d08c83d41b20c0e8869a3379984cb46543251914c7a5a02af950ca6a52d28a13e09a44b6254128090e46b23391808b64562290c7c6122fb17709f84d025a12688cc45622310e08543441920bf055428613908b84181f80da06901ec0f007103701780b805b02c815c0ac04202000e006c025012008c04001f00f004801e00e0068028012008002000c002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
def record052_frame002_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x7337257207006f26ea6d06b86af69b69368d68367766c66565863d5f85b959c58b57956756555a5475124ec4de4cb4bb4b849a48f47846545545042c42441d40e4053fd3ba37a35c34a34033732332130e2d02ac29c29228c27626124a23522c22420d1f31ee1df1d51cc1c417116916316113d13512f12d12612011611110e0f60f10eb0de0d70d10c40bd0b70ab0a907307006a06705705505405205004f04103f03803602502402302001f01e01200f00e00d00a009008004003001000 } : Fields).get c.val)
theorem record052_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record052) (record052.maps 2) (record052.inverseMaps 2) record052_frame002_indices (Fin.ofNat record052.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record052_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record052) (record052.maps 2)
      (record052.inverseMaps 2) record052_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record052_frame002_links_0000 record052_frame002_links_0064)
theorem record052_frame002_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) : Supported record052 2 :=
  of_group record052 2 (smallEmbedding record052) (small_cells_exact record052 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record052_frame002_indices record052_frame002_graph record052_frame002_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSmall.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (Fin.cases (record052_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record052_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00024

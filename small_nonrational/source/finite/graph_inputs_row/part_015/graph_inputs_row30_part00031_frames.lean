module
prelude
public import GraphInputsRow30Part00031Data
public import RawFrameSupport
public import SharedFrameGroups029Checked
public import SharedFrameGroups030Checked
public import SharedFrameGroups031Checked
public import SharedFrameGroups033Checked
public import SharedFrameGroups034Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups042Checked
public import SharedFrameGroups045Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups079Checked
public import SharedFrameGroups081Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x37a5b86db069f3459a04cc9651b235708b5e5a5ab65562a9d53228f94509ab4d426853349934c626192ee9694b1255929e9484a024c524691c48824252048ee473a380fa471034b1774ba45ac2c315e0a304f926f933c98446722410c08423fd1b70d8c67a3171848aa4514270130094c3f01d90e086c831c1590a8050826812b093847422c111086040c1f80f707803ac1c40dc06c034015408f047023410e06c03581a806603201500a004e024011807c03c01c00a804c02400f0070028012007 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x3649aded5f67cb35998cca964e3255786b9f5c5ac855faae9566aafd570a2a51228313e69de4e326cd31c96c4ada4e124c913480236d1728a8442a1cd0c084141d20cce6868a32c977cba45b12c495f4a6a51d28413e89e04a824811ec8da45e1f30f5475237e1b80c7c6042ec16d8b3c4fc26112588e84502100fa873c34a1890c185942a414909f84b424211a08604081e00e406e834415408f047023410e06c03581a806603201500a004e024011807c03c01c00a804c02400f0070028012007 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3a7dbd2dc36d833fd91ac6862730e9708b5e5a5aa69450a034f4a7553569a84d0a66932698c4c325dd2d29624ab253d29091c48b243d2068fc479a39d1c08dd3899a58bb85d82e316c8b3e58c2b9953ca56518233916488e42b20e10046da3691ab8d0c66031d1820b805782a90fc07a83b01bc0d686482aa1500a4850827613409784a024211a08884242060fc07803a81c40dc06c8340154092048823811a08703781b80d606a01980c8060025012008c03e01e00e006c02000f0070028012007 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x744b725a9ed17679b3b586ab8458baa6150ca77533286135692c48d242d1f48cb46122bd14c89a3e91cbcd9865932498e0c505da2bb94109e84e3269929493848924011d87a632c16c8b1c4d624b11688344001880b4052825411d06402c813c094049024011a08c03d01bc0d4069030016c0b405702b01540a804201b80c8062028011808803e01e00e8070028013008003801a00a004802000e0040018008002000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x7016dd6b368366666262f6015d75ab5a65a259e57854851651050b5074c94ba49e48e47f43840b3de3ae3a93a63a238635e33232e32c32a2ec2e12ce2c22b626422420a2061b91a519117e1741251151060f50ee09909208808208108007f07e07206906406305a05505405105004f04e04203703203102802302201f01e01d01c01401301000e00d00a009008007004003002001000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xa594166d4b192d23e3544184b001fe3f97e6f75df39d732e51c7b726d4d6da8b48606b4d5aa8950aa093ea624788650aa104187b0f29d639a70cc716129c5249592223843c858e41b033c628c213c254458861082083f87e0e019c318620b615c2b0530a41442804006c0c4180280460880f81e03a0700a0130200380680a0120200380400600800800 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x96326e474858e71ba26c2a816f9df13e07b8f1dd5b86704e01be3616b2d35a233b61cba9652a8546a814ea874ce91d21a4047a8890d20a4047e8e218f2f65d4a493925245c880e41b0334600bb118220428800fe1f43d87a0de198308600ae1482884e09a1302584006e0c8188280460880f81e03a0700a0130200380680a0120200380400600800800 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0xddf61d5748ce734c9306bdae1b7edeb66d0af29ea6e96a427b9da6a9925d8fa2081dee7ade7781d7719b26c1ad6a995641835f57553d2e47d19400f53b4e437cbc2cca827c9b1d8701ac661946418c62160511384d1284611442104400fc350bc2c0ac2808c2207c1e0741c050130400e0340a0240801c0400c0200400 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0535.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0535.count (({ width := 10, code := 0x7cdeb791da751d272dc46d9a7695a36819962d7d5ed775cd6658d5b55d525153d4bd2147d1b45d12410f53ccf13b8e0374d5344cc2f8b62c0ae2809a2588f230781c86e19c6414c5113c4a12447110431043c0e0370d8350d0310c02f0b82c0ac2a0a4240801f0701b0681904c120400e0340a0240801c0400c0200400 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0535.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0535
    Papers.RationalityTen.SharedFrameCatalogue.group0535_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0531.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0531.count (({ width := 9, code := 0xbd5cedd63ae56aa94ea3cfa793b9ccd2592390c7a3711874220d037bbc5d2e06f36db0d365b0d82c05fad162ac54a99349345220fc7a3a9c8e0602e160a852219047c391c0dc6c35190b8582b148a04e261289046210f8783a190b8582a14098481a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0531.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame007_links_0000 record005_frame007_links_0064)
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0531
    Papers.RationalityTen.SharedFrameCatalogue.group0531_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x400df80f0275cb791b0ed58694343d990c115daad1d59aa5f52928e941c9be4a7239d1b28c344c20c10327fb3e99e54dba6813099664a5651e283136891441a1d98e9471e36417e0b9458e29f13088744021f30f6077039c1a60cb86442f616709e84b825011207f025012209004702340dc06b035017c0b805b02b81580aa05401b00cc064027012008c03e01e00e8070028012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0651.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0651.count (({ width := 9, code := 0x56ab152a85268942a04f67134994a6451d8dc66270e83401fcfc7b3cde2ef75b91bedd6b33990c6622f96eb055aa54ea14f271349647a250882401f4f075399c4da6631180bc5a299047e3e1e8f06833190b85a2c150a450271007c3c1a0c8602c150a04c1e0d0602c1408038180a04018080200 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0651.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0651
    Papers.RationalityTen.SharedFrameCatalogue.group0651_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0650.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0650.count (({ width := 9, code := 0x40e02fe7e3e1eaf378bb9d4e772b85b6d66a3499ac961af978ba5aac962b0572ad50a6512712e9549a3914843f9f4f676399c8e26f361a0ca6330978b4572b154a650269309649230f4763a1c8e06431180b0562a1409c4c251007c3c1a0c8602c150a04c1e0d0602c1408038180a04018080200 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0650.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0650
    Papers.RationalityTen.SharedFrameCatalogue.group0650_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a50cc85e5a97d49ea0e4d9a5ad2908e746b226106080c3fd9e54d2e52b28d93688fe43720a0ecc74436417e0b6058e261112087441a2080fd07b03c61ce0d3067832e1910c1059c2be1520a204f426a12808c844c1fc0f0048823811a08703701ac0d406102f81700b605702b01540a804f01b00cc064029013809004601f00f007403801b00a80500240110078038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xe4171d38bdc44db76d3b61dacad1e68733b9998bd85da2e3966cb125762b655aaace563ab01572ab45532a7d4429f04e1a6953369894bca59d2ac94a492a4491e48e846b23191688a344ba1c90be7913989b9cd0e67d3379984cb4654326190cc7a5eb2c49604ac454629c14b8a3650527b93d09aa4b9255928491c4782350e046d234f1980c7c6282ea16c8b2055c28f13f09cc49223811988a844621c10b08003c01b70d106502cc1530a504e825e12308c84341fa0f20730370102077034010408003701b00a004e010007803801600a0048014008003 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame001_links_0000 (interval_append _ 64 128 133 record012_frame001_links_0064 record012_frame001_links_0128))
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe9c7423991c82ddc6e23691b02d596a83509a68c285feaf556deb4c5942c29600aee56dab1d566aa8541a9c14069e04de26793289824b7a56d28e93c48ba4111da8e8470a3691a68cc463a2e51647dd3bd1cb0dae6ce3531a10cea66932798d0c465d72c115e4aa252f29014509f44df26713249744ad253128093048f2440e586f23571960c646162d61618ad053227a135898447022911088303fc1f00f3074436c1970c405f82aa14609f04a423610d08183e41e00e90710370102077034010408003701b00a004e010007803801600a0048014008003 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame002_links_0000 (interval_append _ 64 128 133 record012_frame002_links_0064 record012_frame002_links_0128))
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x284a0e809f67b9ea779d2729c66e9ae5a952519324690e3f8f63a8de348c22d89e2386e1584a0e8320981a037fdfc7d9f27ade9799e3781dc765d373dc16e1b26a5a76819a65d936418b621825e5775c16a59d635815b5615653d49519424fd3a4dd2748d1c4490d428fe3ecf73c0e6384de348cf330c630cc02f0b72c0a62849e2488f2308620c801f0781c86f1b0681605412c360d42f0b8230881003c0e02c0a0240501003 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame003_links_0000 (interval_append _ 64 128 133 record012_frame003_links_0064 record012_frame003_links_0128))
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0x183c1602fd7dbe5eaf177bb5d2e56bb3d96c55eae56ab358ab556a952a752e8f43a0cfe7d3d9dcea733799cc25b2c95ca6512792c863d178943e15098340e05007f3edf2f678bc1daea74b9dcae27037db8d96c359a8d167b1986be5bad164a9542913e984aa4d14894320d027e3d9dce46b34198ba5c2c958a8512712c9046219007035180984a2210870361007838160a048140803 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame004_links_0000 (interval_append _ 64 128 133 record012_frame004_links_0064 record012_frame004_links_0128))
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd2968eb43da02cd8663b2d1944c816363149874b455962c555aeabe5542a4d516a7f53a29a14c0a5b516286538e9aa4c825e12dc95c4a5a4e525a92747ba38517c8b3450a2410fc87243620fd05475f3929bd8d646ae34419accc265b32218a8c325ef2d896bcb1a5712b31584a9053129194849f84de269933896849d2478ef874e38c1b60d886b23251898c045c62c215c0ac04fa26b130091c46822210907dc3c01c30dc86c43061730b5053c28013009184541fe0f20728364102077034010408003701b00a004e010007803801600a0048014008003 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame005_links_0000 (interval_append _ 64 128 133 record012_frame005_links_0064 record012_frame005_links_0128))
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x7046fe6fa6f66dd6d06c16ba6ad6a369a68a6286196115f45eb5db5d35ce5cb5c65c35c05bc5af5aa58256c55a54c54753e53352f52a52750d5044f44ef4eb4e44db4d24cf4b64ad44a4183fb3c93c63bb3b23af3aa3a339b39737834334032b31e3193163052fa2f22f12df2d22ca2c72b62a92a423822821e20d2092041e51dd1d11c41b91b21ad18d18718417b17417016d15e14f13d1371301131081020f50ee0e50e10d80cb0c20be0b707b07306604003f03703602802701000f00e00b00a009005004003 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame006_links_0000 (interval_append _ 64 128 133 record012_frame006_links_0064 record012_frame006_links_0128))
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x82a81e80f8067e57da7d17c17af7a779c79271c70a6fa6ce6bc6ab69d69768b68167867266f6506446146035f05e25dd5d45cc5c05b75b459558a57a57556e56756055b5575495424d74a548044e44c43041941040c3f53e23d73b338137f36434f34333f32831530a3082f92eb2e62e12d92cf2c824823822420c2041fb1dc1d21c61bc1ae1a81a518c18317f16e16715e15914613c12e12812510a1040ff0ee0e50e00d90d00c90c30c00be08107706804104003703602802701000f00e00b00a009005004003 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record012_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record012_frame007_links_0000 (interval_append _ 64 128 133 record012_frame007_links_0064 record012_frame007_links_0128))
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1fd2fc67ce3b95d78e9370c37a9b74d8a6adb4ada3ccef66bae75688adb531295943ea0b4ae252d1ce8dc454a25910486442120c104c7f73f29f74f6a7a53cb99a4c205a729714889d64d7214105c7663a81ba8d8869c3301870bf05e42c31588aa450227113188583d81bb0d686983301730b605942a414409e849823e11307e83681aa09a03c81e00de06e02e016c0b005702b010408003701b009004602000f8078026012007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8758257ea7c47b57b176975b74e7206e26ae69568e63862c5ee5d75d05c05b45ad59759057b5745705094fc4ee4bd4824464294223c33b537a36035934833d33732131b3063002fc2ca2bb29e28227226324622a2031eb1d21c61bb1b318517c17616d15513c1301121091020fa0e00c60c207b07907806f06e05c05b05805705604304104003703602402302001f01e01b01501301201100f00e00d00b00a009008005004003001000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x22b88a198521083a09811fe7e9ee785db75dca71dbb6d5b16b5a768d9e669956458e60d7e5dd6f58550529464cd2f4851b45d134350840cff3ecf73d0ef3b4e9388df374d9348c12f8b82d0b12b499250902348a210801d8711b4691704c1243b0e4380dc360c4300b82d0b0280982508c220701b0641805c16054130481103c0e0340b02809020050100300400 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame002_links_0000 record016_frame002_links_0064)
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x189c1df6f376ba5c2d968b2d82b555a8d2e93449fcee733598cb6532590c7a2d1387c2604fa7abc9d2e770369aed56933992c6612fd78b85b2cd5cac5529d4494492391488431e8ec72381b8d46630170b257271007a33190c4602f150a450271308842200f0742e160a8502612088401e0e06830160a048200e050200c0200 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame003_links_0000 record016_frame003_links_0064)
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
def record016_frame004_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x51e9ef322534999251962e45487b0a605bf77e0f0ddd3a6722e35c03766e4d81acb47680cf57f2f45d6b415ca955009e921239444835051fc3e27b0ed1d43846f0dc99932a620be9772e65a0ad9432764c095927246428821011f83cc748e41a4338650c617429c520710de1b8338660b015c2a0530a41041f83e06c0d41202304007c0f01b02a04c0901101e0380680b0140240400500800c00800 } : Fields).get c.val)
theorem record016_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record016) (record016.maps 4)
      (record016.inverseMaps 4) record016_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame004_links_0000 record016_frame004_links_0064)
theorem record016_frame004_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 4 :=
  of_group record016 4 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record016_frame004_indices record016_frame004_graph record016_frame004_links
def record016_frame005_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0526.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0526.count (({ width := 9, code := 0x1e1f077fbdddee74f9fcde46ef63abd4e73338cc3e170580bede6ed72b7dbac761afd6699419e4ee59298e4622f14894461d0c84c1e0cfa7c3b9d0e571b65a6ca61af970b357a5d269247a21067d371a8cc622b93c9a43209007c3d1d0e46c351a0ac52281309444210f07438190a84c2411078381a0b0502410050200c0200 } : Fields).get c.val)
theorem record016_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0526.localPairCheck (smallEmbedding record016) (record016.maps 5)
      (record016.inverseMaps 5) record016_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame005_links_0000 record016_frame005_links_0064)
theorem record016_frame005_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 5 :=
  of_group record016 5 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0526
    Papers.RationalityTen.SharedFrameCatalogue.group0526_facts record016_frame005_indices record016_frame005_graph record016_frame005_links
def record016_frame006_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf9c749b6e9a56cef66bafcd790b9d5a0ab6d4c4a1f505a5712908e7454a2590c88424181fdcfca7b53d29e5cd7e6943349834b4e52e275935c8504141d98dd46c43301870bf05862b114089c44c6237119089042c20d10407e83d81c80dd86b434c19e0cc05cc2d81650af854828813d093047c23211307e83681aa07b03c81e00de06e02e016c0b005702b010c08204001b80d8048023010007c03c01b00a804c024011007803801a00b0050024010005002000c002000 } : Fields).get c.val)
theorem record016_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 6)
      (record016.inverseMaps 6) record016_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame006_links_0000 record016_frame006_links_0064)
theorem record016_frame006_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 6 :=
  of_group record016 6 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame006_indices record016_frame006_graph record016_frame006_links
def record016_frame007_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0612.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0612.count (({ width := 9, code := 0x17bb95a2c15cad552a34da550e7d3599cb253228e4662b11874260f027fbf1e6ef75ba5c4dd6ab4d9aca61af976b95b2c958aa522853c974b24d2490472351682409f8fa7a3b9b8d86a3499ccc642e96cb256289248e401f8f8783b1a0cc602f170a850271208c361a0c05c2c13088401e0e06830160a048200e050200c0200 } : Fields).get c.val)
theorem record016_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record016) (record016.maps 7)
      (record016.inverseMaps 7) record016_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame007_links_0000 record016_frame007_links_0064)
theorem record016_frame007_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 7 :=
  of_group record016 7 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0612
    Papers.RationalityTen.SharedFrameCatalogue.group0612_facts record016_frame007_indices record016_frame007_graph record016_frame007_links
def record016_frame008_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7557296f46cf6af6a366064d6406275f95ce5a859b55554f5255024f54df4ce4c94a449747946d4664254164063ed3bf39436b36131b3152eb2c52bc2a229428f26725c23c23222c2072011f21e51df1d91c81b919718817717016b16614013713012c1221161100ff0f70f20ee0d90b90b407907707606d06c05a05905605505404304104003703602402302001f01e01b01501301201100f00e00d00b00a009008005004003001000 } : Fields).get c.val)
theorem record016_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record016) (record016.maps 8)
      (record016.inverseMaps 8) record016_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame008_links_0000 record016_frame008_links_0064)
theorem record016_frame008_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 8 :=
  of_group record016 8 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record016_frame008_indices record016_frame008_graph record016_frame008_links
def record016_frame009_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x370d6b4dd0b3ccdf1fc5b0fc16fabaadcb5ec1aeaa7a528ea127e9ee709a25c95e518ea338a61e82df8795de72dc56e9ab6a1a066195625815d1705ad575514c50d3d4ed334a51543103400fa3d8de36cd5344c8300bc2bca7290a02447f1ec5915c561445011c4610c42104360d0330bc2e090230801f0781b054130481103c0e0340b02809020050100300400 } : Fields).get c.val)
theorem record016_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record016) (record016.maps 9)
      (record016.inverseMaps 9) record016_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame009_links_0000 record016_frame009_links_0064)
theorem record016_frame009_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 9 :=
  of_group record016 9 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record016_frame009_indices record016_frame009_graph record016_frame009_links
def record016_frame010_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0525.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0525.count (({ width := 10, code := 0x2699664d91a408fa368ca2f89a1b8420680df27bde476dd8755d1735c6705bb6d9b46859b661946257e5cd715956255d4d52d49519434e9384bd2d4a91b4650e41d0540cf83c4e4370d7340cb31cb12b0a929c9f268932107f1e8761b05f1704911c4610c420f03b0e0370d82f0b42c0a428088210781d07019054130481103c0e0340b02809020050100300400 } : Fields).get c.val)
theorem record016_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0525.localPairCheck (smallEmbedding record016) (record016.maps 10)
      (record016.inverseMaps 10) record016_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame010_links_0000 record016_frame010_links_0064)
theorem record016_frame010_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 10 :=
  of_group record016 10 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0525
    Papers.RationalityTen.SharedFrameCatalogue.group0525_facts record016_frame010_indices record016_frame010_graph record016_frame010_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (Fin.cases (record016_frame004_supported hcells) (Fin.cases (record016_frame005_supported hcells) (Fin.cases (record016_frame006_supported hcells) (Fin.cases (record016_frame007_supported hcells) (Fin.cases (record016_frame008_supported hcells) (Fin.cases (record016_frame009_supported hcells) (Fin.cases (record016_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x36d9a64c96616b03d810b7d5b82d8d606ab4551a951494a3b51a273d2f696a48b24311fa8f645d22350ee85341ea0b50267fd3f69fa0e6072438b9b00cdc65f3069810bf05f22cf1558a9250127c93b89d24bb24b12148d445922690ec85441e20d8ef075c38e1b78d7069c32e1878c105ec2f01708ae451a279133896c45a2210fd07b03901a40c906082ee1510a304982100f707383701a406f03701ac0d406002f81700b603701b00cc064028013809004601b00a804c024011007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x38f1af8d3468533dd9e0c255fd2f496fcb22588aac153ea76532284936c9a54a224cd2148f8470a34d1988be45aa2b91448994492234f8c7a03be9ca4dae6c63391984c6e6262ea1608ae251d28613889a24ba256929893048f24411f48ea46f23590047d43bc1c98df46d434118c8c085b02c515c0a644f426b12d093043820e0f2075436c1970c405dc2d213909584041e00e9071036c1a806f03701ac0d406002f81700b603701b00cc064028013809004601b00a804c024011007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0613.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0613.count (({ width := 10, code := 0x22a8861a8561183e0a815ff7e9ee7ade077ddc761d4725c76edb96d9b26b9a8691a167599661946418f6117f5e16f5855d53d4d52d47501324bd214791c4611443909415023f8fd3e8f63d4ef3b4e9388df374d9348d1330c7304be2e0b42c4ad2849e2448d228842007e1ec6d1a45d168561444b120370d8350d0330c8310c023088210801e0741c06c16054130481103c0e02c0a0240801c050100300801 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0613.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0613
    Papers.RationalityTen.SharedFrameCatalogue.group0613_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0611.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0611.count (({ width := 8, code := 0xb8b4b2b0afaeaba9a8a6a3a29f9e9d9b9996959291908e8d8b8a898886858482817e7d7b7976757271706f6d6a696665646362615f5e5d5c5b5a5958555453504f4e4d4a494846454442403f3e3c3b393837353332312f2e2c2b2a2827262524232221201f1e1918171614131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0611.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0611.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0611.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0611.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame004_links_0000 record017_frame004_links_0064)
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0611
    Papers.RationalityTen.SharedFrameCatalogue.group0611_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0608.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0608.count (({ width := 9, code := 0x623057ebd5deeb71b6da6cb60af566b156a953e9549a250a813c9d4da652f964a24f249047e2f148842604ff7cbe1ecf3773a1cee06eb6db0d669b3d96c862b1182be5eae16cb3572b154a7512853c994a2491c8a44218fe7e399c0dc6a33194c8592b93c9a4a228fc7830178b85a2c158a8521e0e87036190c05c2c12088401e0e0683014090401c0c050200c0401 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0608.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame005_links_0000 record017_frame005_links_0064)
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0608
    Papers.RationalityTen.SharedFrameCatalogue.group0608_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
def record017_frame006_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x33fd940c3a5f82f01754b435952c515caaa654d297d49ea1f506275d31c97e496246d1d08d2450a1f90e484c417a068fee7d93e19ed0ea073a3931bccd646a63301954c5a61c2f616c4b505652ad14d0a4c4fc26f134c96849d24791d08b844d2228ffc7e03d41de8eac73637b1b10d4064e3151828b8c5842b81538a504b424910807f03c01c30dc86a83301650a884841fe0f2072835818e06f03701ac0d406002f81700b603701b00cc064028013809004601b00a804c024011007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record017_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 6)
      (record017.inverseMaps 6) record017_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame006_links_0000 record017_frame006_links_0064)
theorem record017_frame006_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 6 :=
  of_group record017 6 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record017_frame006_indices record017_frame006_graph record017_frame006_links
def record017_frame007_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8047bf79277276175a71a7086f96d66a96a067166764963e61b5ee5e55b65ac58f58356e56055b54e54453d53252852151d4cc4b74a647d44e44540f4053e43da3b038137834233831830c2f92eb2e62d92cf2c82be2b52af2ac27b27225b24723a23221a2041f31dd1d31ca1bc1ae1a81a019717b17015814a13c12e1281201170fb0f00d80c90c30c00bd0b706f06e06b06a06005f05c05b03703603303202802702402301b01501301201100f00e00b00a009008007005004003002001 } : Fields).get c.val)
theorem record017_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record017) (record017.maps 7)
      (record017.inverseMaps 7) record017_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame007_links_0000 record017_frame007_links_0064)
theorem record017_frame007_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 7 :=
  of_group record017 7 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record017_frame007_indices record017_frame007_graph record017_frame007_links
def record017_frame008_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x14767b4ca95126a49c668bb15a1ec29843026023f87e4f65e0bba74ce85c9b8e702dddba3676bed61a734567ecf97faf55dab415cab1526a3540a7c4bc9011ca2243a83d059fd3e47b8f11d93a6728e01bb374664ca9882fa5dcb99682b6558a69482864ec9812b24e48c8a9102043f0798e91c83786c8ca18c2ec590ad152298518670cc1903185b0b41602b83606a0c81882804e0901181b02a04c0901101e0380580a0120200380500800c01001 } : Fields).get c.val)
theorem record017_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record017) (record017.maps 8)
      (record017.inverseMaps 8) record017_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame008_links_0000 record017_frame008_links_0064)
theorem record017_frame008_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 8 :=
  of_group record017 8 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record017_frame008_indices record017_frame008_graph record017_frame008_links
def record017_frame009_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0520.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0520.count (({ width := 9, code := 0x73391c5e17037db5d86bf57a1d06733797ca6431589bfdfaf577bb5cee16db5da2cd63b057ea34da5d167b3c9b4d6652f94c8a43198c456250f85c260b03803f9f6f87bba5d0df6db65aed06531986c05f2e566af562a53e9d4aa491a8a42200fc753a1a8c66230170b24a249208e4421904802b150a450251208842190a84c241107838160a048200e050200c0401 } : Fields).get c.val)
theorem record017_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0520.localPairCheck (smallEmbedding record017) (record017.maps 9)
      (record017.inverseMaps 9) record017_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame009_links_0000 record017_frame009_links_0064)
theorem record017_frame009_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 9 :=
  of_group record017 9 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0520
    Papers.RationalityTen.SharedFrameCatalogue.group0520_facts record017_frame009_indices record017_frame009_graph record017_frame009_links
def record017_frame010_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e5dd20dbd698b3c19b0bf65e5ae81682adb563a97d49ea2250726e12b2948473a359156898433a1150668103fb1f90f967b23d11e60d846973361834b4e593295946c9dc4da24210948283b31d10ddc6c83331888bfc5b82c21580a5c4fc26e13208dc46422410b08344101fa0f6078c3aa1ce0e406ec35a1a60cf066030417c0b3857c2a414409e84d425e11908983f81dc0e707003641a606f03701ac0d406002f81700b603701b00cc064028013809004601b00a804c024011007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record017_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 10)
      (record017.inverseMaps 10) record017_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame010_links_0000 record017_frame010_links_0064)
theorem record017_frame010_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 10 :=
  of_group record017 10 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame010_indices record017_frame010_graph record017_frame010_links
def record017_frame011_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x76a7417116ee6db6d467e6716676406106065d45ce5c15ba58d56355952a52251550e4f24df4d64c54b64ae4a149048648242e4214173ed3bb3b438437e37136a33b30c3032d92d22c52be2a228f28627126025624c23d23523220d2061f61e71dc1d51c51b61af1a71a319e19118317d17416d15114a13112d12311911310b1060f10ec0d90ce0c70c10bb0b406f06e06b06a06005f05c05b03703603303202802702402301b01501301201100f00e00b00a009008007005004003002001 } : Fields).get c.val)
theorem record017_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 11)
      (record017.inverseMaps 11) record017_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame011_links_0000 record017_frame011_links_0064)
theorem record017_frame011_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 11 :=
  of_group record017 11 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record017_frame011_indices record017_frame011_graph record017_frame011_links
def record017_frame012_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0612.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0612.count (({ width := 9, code := 0x5eae369b0d76b755a953e9543a14f277369a4c25529914863b1a8b44a210b8441a07017f3f5e8f076ba5c4e16db65acd468b2d94c360afd78ba5bad160ab54a9d46a04fa5d2c93492411c8d45a250a8341204fc7d3d1dce470359a4ce6632184be592b1489e4c251208c3c1d8e872371b0d0662411888421e0e86c3413088401e0e0683014090401c0c050200c0401 } : Fields).get c.val)
theorem record017_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0612.localPairCheck (smallEmbedding record017) (record017.maps 12)
      (record017.inverseMaps 12) record017_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame012_links_0000 record017_frame012_links_0064)
theorem record017_frame012_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 12 :=
  of_group record017 12 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0612
    Papers.RationalityTen.SharedFrameCatalogue.group0612_facts record017_frame012_indices record017_frame012_graph record017_frame012_links
def record017_frame013_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7537286f56d16b06a46636506416275f95f35cd5c55aa59d57f55454f52551e5034f64e24d14ca4b54a349648847646a4674284194073ed3bf3b939338b36d36334531a3152eb2e42c62bd2a529729027b26625b24e23922f22d2072011f21e51df1d91c81b91b41a619e19718817717016b16614e14a13212c12211611010c1080f20ee0da0ce0c70bf0b80b206d06c06906805e05d05a05903703603303202802702402301b01501301201100f00e00b00a009008007005004003002001 } : Fields).get c.val)
theorem record017_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record017) (record017.maps 13)
      (record017.inverseMaps 13) record017_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame013_links_0000 record017_frame013_links_0064)
theorem record017_frame013_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 13 :=
  of_group record017 13 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record017_frame013_indices record017_frame013_graph record017_frame013_links
def record017_frame014_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x36fd674fd133dce320c5f11c16fabd6e8b8eddb62ceafebaa9ea0a568fa167f9f6749be6798a5a95a528ee348ae1e82e057d9f0799df759c9715ba6d1ac6a5a166597639886017b5c96f5b1575514c50d3d4ed334a526479184550c40d003e8f63a0e5358d1320c02f0b72d0a42809222c8820c7e1e8511404f1384a124471182f0b82d0b02809c2408c1b054130481103c0e02c0a0240801c050100300801 } : Fields).get c.val)
theorem record017_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record017) (record017.maps 14) (record017.inverseMaps 14) record017_frame014_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record017) (record017.maps 14) (record017.inverseMaps 14) record017_frame014_indices (Fin.ofNat record017.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record017_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record017) (record017.maps 14)
      (record017.inverseMaps 14) record017_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record017_frame014_links_0000 record017_frame014_links_0064)
theorem record017_frame014_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 14 :=
  of_group record017 14 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record017_frame014_indices record017_frame014_graph record017_frame014_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (Fin.cases (record017_frame006_supported hcells) (Fin.cases (record017_frame007_supported hcells) (Fin.cases (record017_frame008_supported hcells) (Fin.cases (record017_frame009_supported hcells) (Fin.cases (record017_frame010_supported hcells) (Fin.cases (record017_frame011_supported hcells) (Fin.cases (record017_frame012_supported hcells) (Fin.cases (record017_frame013_supported hcells) (Fin.cases (record017_frame014_supported hcells) (fun j => Fin.elim0 j))))))))))))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1d20ce36642fd9796ba05a0ab1d49ea2650726e12b2948473a3591568984212034ff47c83db1e54d846973361834b2651b279136890842520a0ecc7443771b20c385b22c614a0a084c2237119089042c20d10407e83d81e30ea87383901ad0cf06603201820be05d02ce15f0a9051027a13509784642260fe074824411a06e03501800be05c02d81600ac05502a00d8064028013809004602000f007403801b00a804c0240110078038016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1a64c0d602adf56e0b63581aa8d494a3c51a273d2f696a48b24311fa8f644521450808114001f9ce6072438b9b00cbe6042fc97c8b3c5562a494049f24ee274924c8d045c21c90b48343bc1d70e386de35c1a70cb861e30417b0bc05c228d133896c49822d11088483f41ec0e406903241820bb854428c12607c824411a06e03501800be05c02d81600ac05502a00d8064028013809004602000f007403801b00a804c0240110078038016009004001c00a0040018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x7416d96d167e6716676406065ce5c25ba58d56355952a52251550e4dd4c34b949f49348142e4214173ed3b437e37236a33b30c3032d92d22c52be28d26f26324a24023120d2061f61e71dc1d51c51b61af1a71a319e18317416d16315114a14013112d12311911310b1060f10ec0d90c909108d06e06a06005f05c05b05805605505403603202802702402302001e01d01c01b01501301201100f00e00b009008007005004003002001000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2f65c9b55602b7565ac354ea5544a1f3ce6a4c797d2ea564a393b2123fc738d315624c4386b0aa12410808ff9f83e57bef61ea3d0798e5db2b53692d1197327602bc9712d7592af95dab553aa5d41a764e2959262384668b9162013e4788e49bc36e670c91842ec5acb41622945109c13325c4b08e11521e424810f91d63946c8d219c3285d8b41602b05389712c21c430660ca17c2c8570ac0d0198320600941202303602c0500900c01402003 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x19fcccd64fb0e9828bfa5f82f41756b9558b2b9554ca82535a98547aa1b504274d3869a64c7257927692e483a39119c8a143f21c909882f40d1ffcfd47d43df1c9cd686853341980c526182f01724b665a52c515b8aca55c29814889f84de26992a093446c22e11348923f41ec0efc71c36e1b18cc86403051718b085702ac13d89a448a232110085c3dc1e00e8870c3721a40c085c429a13e09704981fe0f2072836c1940aa054827013606f03701a00c406002f80d0066032018009404802300d802c0140090030014008003 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x7523819b5ad6267fb33194cc90634b12d86eba15a42bf5534a67520a8ad4089e64e926c535099a4c626192ee9694b125712a89494a1250126292348e245921c90347e23d11da8e646f9f54e266d63579a64cc864d2ec16c8b185732a794aca3050926d132897a49a23b919c8b242b20e10007de3df1eb0da468631d1820b805782a914d09ac4b624e11588203f01ea0de06b43221800b8059c2aa1500a485082761340978484234111084840c1f80f807803a01c40dc06c834813809b04902440f207803781b8060025012008c04001f00f006c02000f007002c014009 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record020_frame001_links_0000 (interval_append _ 64 128 136 record020_frame001_links_0064 record020_frame001_links_0128))
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x680b33593ec7661bb03d7eabee5e5aeb172cb51589ab9554ca7f5342981474a1d505278d3929ac4c8a6212c093d497a4952128e3466a32d14a88243a21ad0a282c40ba000fd67d53df9c9cd686883359984c6e6262f01724b665a52c515b8aca55c2981488a304f926d934899049c24711bc8be4502238fd07b03bf1d60e306d83621ab0c8c6223051718b085702ac13d89a448e23411108543f01f10f1875038c1ba0da86382fc1690a604f425a12808a03f41de0e206e832c13809b04902440f207803781b8060025012008c04001f00f006c02000f007002c014009 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record020_frame002_links_0000 (interval_append _ 64 128 136 record020_frame002_links_0064 record020_frame002_links_0128))
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x24fc868d114e2043a843011f4bdb7aaee9d93a6730e39c33776e6d59a833e66acb18fb16626be9732b95309bd36a674b893d20a3a4608a9122043fc77ce99c83866a4cf19031060cbd9752e05a0b11422784a88f9162023e87b0f01d238c6f8d519e318608bb1702cc5709d130248488800fe194320620a61482084006e0d8198320620c01502804e07c0f01d0360400780e0140240380600a01001800 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (smallEmbedding record021) (small_cells_exact record021 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c78d7c6acb541a84d34697347da22d0a67bb3c17a4b695a32c89626ab053b29913fa9da4db269d28890a47c23c51d08da466230d16a8ae454a28d1328924469df4e586d73519a04ce4637313175cb0454e29614749c44d126492e895a4a6250126091e48823d91d48de46b1c98c645b02c515f09ac4ac20b0f2076c31017309404041f20f107483881b60d403881bc0dc06b03501880c005f02e016c06e03601a00cc0640280138094048023009804801e00e0050024010007002000c004001 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8047bf7af7a779c79278e78177677276175a6f96ca6b76a96a267164963e60f5ff5ee5e75b658f58357e57556755b55354453d53953352852151d4a648044e42e41640f3e43da3b338136134d34231830c3082f92eb2e62e12d92cf2c82bc2b52af2ac2472041dd1d31cf1a819c16d15814f12811c0ed0d80d00ca0c30c00bd0b707106f06e06b06a06206005f05c05b03703603403303202802702502402301301200f00e00a009008007004003002001 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
def record022_frame003_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x298511a073f27aced9cf37a6b4d19872f641c698c11562842d841069fd3f27d2f91e0bb0756ea1d1b97712df5b8b696ced85a934968ec457fadc596b0d5daae550a3935a5d4ac93d1f23946c8b10f217420818fd9f23ca77ceb9d533a5e4b31632c251c9f91d21a42c788e818c2d85a0af14e2884f09a0ce198328620c21642c0570a814c1a8340660c81882704c094120230260480780e0140240400700800c01001 } : Fields).get c.val)
theorem record022_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record022) (record022.maps 3) (record022.inverseMaps 3) record022_frame003_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record022) (record022.maps 3)
      (record022.inverseMaps 3) record022_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame003_links_0000 record022_frame003_links_0064)
theorem record022_frame003_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 3 :=
  of_group record022 3 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record022_frame003_indices record022_frame003_graph record022_frame003_links
def record022_frame004_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x299511a0b3fe7bcf19db3966ecd999731e4a4848fb1da39c5789711a15c2182b045f5bd77a0f31e1bb775ae9dcdb94722e25beb756e0ced94b035e6bad712ce58eae14e29451ea213e2774e698d2ca5449e9191da334508890da173ba6d0d099d3365d4b814825e4a8820fc1aa2f85c0b21582a0508990ce198328620c21642b8560a6148198320600bc1702604a090118220260480780e0140240400700800c01001 } : Fields).get c.val)
theorem record022_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record022) (record022.maps 4) (record022.inverseMaps 4) record022_frame004_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record022) (record022.maps 4)
      (record022.inverseMaps 4) record022_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame004_links_0000 record022_frame004_links_0064)
theorem record022_frame004_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 4 :=
  of_group record022 4 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record022_frame004_indices record022_frame004_graph record022_frame004_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (Fin.cases (record022_frame003_supported hcells) (Fin.cases (record022_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x90b1c632c4387b0820b3f17bcf61d2b856ecdc9b7b4d680ca590b125ceb5562ab4540a354326d4ce9712ba38456899112123e678cee1d63886b4c71832f65d4b49642c05249c93325a440810fe1c6380638b71642b4540810fe1ec338660c816c2d0580ae1482885007e0e41b0340640a81402704808c1081e03a0700981202003c0700b0120200380400600800800 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3a419c6cc85d02c0958ca2650726e12b291e47d239d1568984452070ff47c73db1e54cd85ce2c913c89b44842128fa878c3b31bb8d906ac2e81630a4c50426111b88c844821610708043e61ec0ea873838e1b40c8060c2f61740b3857c2a414409e84d425e0fe07b03c01d209104681c40dc06a030017c0ba05c02d81580aa05401c80d8064028013809404802300f007403801b00a804c0240100078038018009004001c00a0040018008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xe9f6d833fd91ac4e61d2d2d534a284f4a7553629a84cd263130c9774b4a58929e94848e24592068fc479a39d1c08dd3e91c34d2c65431f9784ba45ac2c315cca9e52b28c137c99e46722a10047a23721b18cf462e3041700af055227013007e03ca1920b105542a01490a104ec26812b093047422c111084840c1f80f707803a81c40dc06b034012409104702340de06e03581a806e03601980c806002a014009c04a024011807c03c01d00e006c02a013009004001e00e0050024010007 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x36e99cacc3604ab6d4469a54c0a57128a8fa46aa2b912c8304101fdcfca7c73db9e48daa5a727791c489a4282088f1874237a1b10bf05d82c31588a4c50625e11b88c844821610707cc3c81de0eb069833c17b0ba85642a414b0a204f426812608f84682180fd07b83c01b40af04681e00de06e03501a40d005d02d815c0ac05402000dc06c03201880c004a02300f807803801b00a804c0240100070034014009004001c00c005002000c002000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1c72d796acb541a84d3468534119e2cea5eaadbd698b285582a854e4a5f501a78137894449aa4191e68ed47423851b48d3466231d1728b2454a2891328924471de8e586d7339175cb0451d26492e895a4a6250126091e48823e91d48de4691cb0c645ac2c315a0a644f426b13088e045220e0f0874436c1970c405f82aa14609583f81f20f007483881b80d405802bc13809b03b81ac0d406802e016c08204001b80d806603201880a004e024011808801e00e00580280120070028010006001 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x38259e8c74627b0f1748a8f507a7a93ae9684a9a52d28a91b47fa3c11d482d3b01bd4d806553209794ae252b28113d09c04d1260119c8a442320790047e23761810af052628513889884a21f80f186d03401920c10520274133092845c2080e9059024811a08c03781a80d206002e816c0b405702b01540a804902180e406e03501900c4050025011808803e01e00e80700260100070034014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c0cca5a0ab1d494a2350826e12908d145622690c88424182034fd27c83db9834b2651627793709084141ce8de06cc3301870bf05b22b514a0a0c46e23210687e83ac1d00e406ec35a1a60cf06603141820be05d42be1520a204f426a12f090846422610c049023411807b03781a80d206002d81680b005702b01540a804301b80c8062028011808804001f00f007403801b00a804c02200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19e6ced5bf2c45534a77533284934a92e485a3e91c08d2465a2f515e8a144d1ca4d8c65c31c18a0ba8571283938c9a64b9256129492e48923e11d88023ea1be8d045b22c715c0a644f426b12d093045a21c10708003aa1b60cb86202ee1690a504e425611d049023411807b03781a80d206002d81680b005702b01540a804301b80c8062028011808804001f00f007403801b00a804c02200e006802c014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x80e80875f7196d16bb6af6706215d05b55a558657656e55e54c53c5344764273d63bb3ab37132b2e32cd2c12a329328b27b26925925121e21a1f81e61c21bd1b61a819919018718117116816215b14413612711e11510f0ff0f60f00e909208d08c07b06f06a06906005b05a05805705605505404303703203102802302202001f01e01d01c01b01501301100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
def record030_frame004_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6666625fc5d25ac5a259e57354351750b5074e64cf4c94b249e48647f4083db3af3a63a238335b33332c32a30b2f32ec2dc2ce2bd2b627626d24422d20a2061fc1dd1c11b91af1a619118817f17415714212d12511e1161060fe0f60ee08107f07e07306906406305a05505405205105004f04e04303703203102802302202001f01e01d01c01b01501301100e00d00b00a009008007005004003002001000 } : Fields).get c.val)
theorem record030_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record030) (record030.maps 4)
      (record030.inverseMaps 4) record030_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame004_links_0000 record030_frame004_links_0064)
theorem record030_frame004_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 4 :=
  of_group record030 4 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record030_frame004_indices record030_frame004_graph record030_frame004_links
def record030_frame005_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x239c6e851025f43e07b8f15d4387700df1b73656c2d59a6b40676ba1642a9540a75422654909011ea2f44c8890b20a3fe7e8e99cc35465cbd9752dc578a71492844e8949202304407e0f21d03906f0d919a318608bb0fe1ec3d0700cc184300570a41442784e09a1302584106e0c8188280460881001f03c0740e01b02a04c0880e01a02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record030_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record030) (record030.maps 5) (record030.inverseMaps 5) record030_frame005_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record030) (record030.maps 5)
      (record030.inverseMaps 5) record030_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame005_links_0000 record030_frame005_links_0064)
theorem record030_frame005_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 5 :=
  of_group record030 5 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record030_frame005_indices record030_frame005_graph record030_frame005_links
def record030_frame006_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x24b48f87b086013f97e6f65dd39f728e3dc03766e4d99adb4d690b4158a8b5049f52f239436841061fc3e27b0f09d639270ccc9952ee5a0a71492864ec9812b24e48c8e11522042c7e0f31d23906f0d919e328630c21081fc3f0710ce18c3105b0ae1582a0530a41442804106c0c4180280460881001f03c0740e01b02a04c0880e01a02c0500901001c0280400600800800 } : Fields).get c.val)
theorem record030_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record030) (record030.maps 6) (record030.inverseMaps 6) record030_frame006_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record030) (record030.maps 6)
      (record030.inverseMaps 6) record030_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame006_links_0000 record030_frame006_links_0064)
theorem record030_frame006_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 6 :=
  of_group record030 6 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record030_frame006_indices record030_frame006_graph record030_frame006_links
def record030_frame007_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0xce734c16f5b8adeb66ceaea9fa5a90a127e9ee739aa619761e815ef79de0759c56cdad6a9a066195635835e97555d544f53347d194550c40d003e8f63b4e8394df344c8300bc2dcb42a0a42809b19463188591444e1344a1184510c42104400fc360bc2c0ac2808c220801f0781d0701b054130440e0340b02809020070140400c0200400 } : Fields).get c.val)
theorem record030_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record030) (record030.maps 7) (record030.inverseMaps 7) record030_frame007_indices (Fin.ofNat record030.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record030_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record030) (record030.maps 7)
      (record030.inverseMaps 7) record030_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record030_frame007_links_0000 record030_frame007_links_0064)
theorem record030_frame007_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 7 :=
  of_group record030 7 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record030_frame007_indices record030_frame007_graph record030_frame007_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (Fin.cases (record030_frame004_supported hcells) (Fin.cases (record030_frame005_supported hcells) (Fin.cases (record030_frame006_supported hcells) (Fin.cases (record030_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x288d0e9dd2f250c788df1aa2dc1d81901a01bff7c0f69e33b9764dd99db205ecbb173ad352aa093e2794ea9712c2484788dd052023b66e4d49a032c640c49842ea59ca71442764d48f91320a3f47b8ef1ba3205b0b010e2144206e0da1a03385f0ba16c2d0570ac1542a03906e0c81882804a08c1101f03c0740e01b02a04c0800e01a0300500901001c0280400600800800 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c0cca604aca958ca4c511a8413708fa460a2b113488a4182070fd27c73db9b54bec59228c13bc9b84841e30e346f03661ab0bf05d02b51498a0c46e23210707cc3c81de0eb074038e1c20da06983141830bd85d42be1520a204f426a12f09084301ec0f0049023411807103781a80d206002e816c0b405702b01540a803901b80c8062028012808c04401f00f007403801b00a804c02000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x77c7727386f36d669f68d6836616025de5d15c45bc58557d56354c5404ee49846642d41440a3eb3a538c38037a37233b32e30b2fb2f12af2a727124723222a22021820e2071f11dd1ba1ad1a219817816415214713d13111a0fd0e30dc08c08708606e06c06706605d05a05805705405305205103803603103002802502302201f01e01d01c01b01501301000e00d00c00a009008007005004003002001000 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xd0165f32ad944c3759c2c7d62aaa8545a9d14c0a2c50ca6e13369904ae24e525a90e47ba385188871426a0b503075a3a11cb0e4a6f23591a64cf866132b18a8c325cf2dc16c4b1a5712b31500a6252328d93489603e31e38ef873638c1bd8db06c43391928c4c6082f41698ae052a27d135896446822210907f03c01c30dc86503061730a7850026012308804041aa09204882040ae056024810808204001b80d8052028013807c03c01d00d804402000f00700300140090028010006000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d48e056d6b4eda26cff648312d86eba05a42b5955ca9a515a7993a49b04d0a64d3189874bf25c12c495b4aaa525284940498a48d23890a481a3f11da8e646f9f54ea67283899a64cc864d2e3167cb185722b094f4a304f826d132897a49a23b919c87842b20e0fbc7be3d61ab8cc063a3031790b38552289135896c49c22b10407e039a1bc0d686002e01670aa854029214209d84d025012108d043c21610307e03e01e00e807103701b20d204e026c12609204881e40f007003781b8060026012008c04001f00f006c02200f007002c014009 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record034_frame001_links_0000 (interval_append _ 64 128 130 record034_frame001_links_0064 record034_frame001_links_0128))
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1a02ccc64fb159878c375f72eb172cb50589ab11556aa653028754149e04dda67932298a4b9253d25e922486238d19a8cb452a2090e8841416205cfd67d53df9c9cdb46c035a1984c6e6262ea16f4b665a42cb95ecaca5492981488a304f926d934895449c247117c8a04471f28f2477e3ab1cd8dec6c43411918c4460a2e31610ae051a27b13488d04442150fc07c43c61d40e306e834218e0bf05842a813d09684a02280fd07783881ba0cb04e026c12609204881e40f007003781b8060026012008c04001f00f006c02200f007002c014009 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record034_frame002_links_0000 (interval_append _ 64 128 130 record034_frame002_links_0064 record034_frame002_links_0128))
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x72c7046ec6c26b26ae68165d64f62c6145ed5de5d65a958357656255454854454053952c52051a5145064fd4fc4ee4e14dc4cb4c34bb4ac4a449c45842f41b4103dd3c13b437836635f35234b33832b31d30a2ff2f82e92da2d42b82b02a528727c27523c22b22121420b1fc1ed1df1ca1c11ba1aa19d19617a16f16714713d13712812311c11610f10b1000fa0f40ea0e60dd0d60d30cc0c40be0b90b70af08e08d08708608507507406e06d06c03002602402302001f01e01b01100f00e00b00a009 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record034_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record034_frame003_links_0000 (interval_append _ 64 128 130 record034_frame003_links_0064 record034_frame003_links_0128))
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (smallEmbedding record034) (small_cells_exact record034 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x8b987e8458227937226e46345ec5af59c59359058858057857056856055154954653e53152a5224b043a3f23b53a23342f62b02ad2a529d29528d28527d26e26626325b24e24723f2001d81b41b11a91a219a19118918217616e16a16315815014914213f13713012811f1171101040fc0f80f10e60de0d70d50d10cd0c90c50c10aa0a909c09b09a09209108e08d08c07907807706f06e06b06a06904104003002802702402302201b01301200f00e00d } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
def record035_frame002_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x7d9ef765cf6f5a7675795b9655855f5795c56958559545494f5354c52947515434f1234610f42cf53acde374db364d7354d3344ce330cb324c6310c22b0a225494248902388c2288821483208801f47b1e4771d8741c8701b86c1a867194641885f1745b16859160571585513c4e1244811c3f0f83b0e8390d0330c82a0a4260942407c1e07415050110400f038060140200400 } : Fields).get c.val)
theorem record035_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record035) (record035.maps 2) (record035.inverseMaps 2) record035_frame002_indices (Fin.ofNat record035.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record035_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record035) (record035.maps 2)
      (record035.inverseMaps 2) record035_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record035_frame002_links_0000 record035_frame002_links_0064)
theorem record035_frame002_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 2 :=
  of_group record035 2 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record035_frame002_indices record035_frame002_graph record035_frame002_links
def record035_frame003_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x926428b222841fa7c1cc705b66c5af6b9ab6a1a56899f67197651936418c629886056857552535374b52047d1c4651644d104350841504404fd3ecf938cd9330cb320c5308bf2f0b92d0b12c0ad2a4a7294a32889f27099258932408b22087210801f87c1ec7a1e4781dc761c06f1a8691a06017c5c16c5a1545414c4b12847118450d8350c02809c2408c2206c130480f0380d } : Fields).get c.val)
theorem record035_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record035) (record035.maps 3) (record035.inverseMaps 3) record035_frame003_indices (Fin.ofNat record035.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record035_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record035) (record035.maps 3)
      (record035.inverseMaps 3) record035_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record035_frame003_links_0000 record035_frame003_links_0064)
theorem record035_frame003_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 3 :=
  of_group record035 3 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record035_frame003_indices record035_frame003_graph record035_frame003_links
def record035_frame004_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x2724d097d2b63bc4e862f85dd396712e05c037a6eadbdb5b656b8d3da4347682ce19a32f628ba160a9d52099d2521e43885d08a0d410800fc9ec3ca78cef1d53a2730d398a2e25b8b49622b6554a71462744cc9892a23c4648990d2164107e8f71e23a4710d619e330630ba16a2bc568a71402744c89511822c430851082003f87c0f61e83706d0d8194320620c21801f83e05c09c130240460880d81302403c0700d } : Fields).get c.val)
theorem record035_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record035) (record035.maps 4) (record035.inverseMaps 4) record035_frame004_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record035) (record035.maps 4) (record035.inverseMaps 4) record035_frame004_indices (Fin.ofNat record035.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record035_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record035) (record035.maps 4)
      (record035.inverseMaps 4) record035_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record035_frame004_links_0000 record035_frame004_links_0064)
theorem record035_frame004_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 4 :=
  of_group record035 4 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record035_frame004_indices record035_frame004_graph record035_frame004_links
def record035_frame005_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0653.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0653.count (({ width := 8, code := 0xd6d4d2d0c8c6c4bbb9b3b1afaeadacabaaa8a6a3a1a09f9d9c9b9996948e8c8a88807f7e7d7c7b7977747271706e6d6c6a68605f5e5d5c5b5957545251504e4d4c4a494847464543413e3c3b3a3837363534333231302e2d2b2a2925242322211f1e1d19181716151312110d0c0b0a09080403020100 } : Fields).get c.val)
theorem record035_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record035) (record035.maps 5) (record035.inverseMaps 5) record035_frame005_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record035) (record035.maps 5) (record035.inverseMaps 5) record035_frame005_indices (Fin.ofNat record035.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record035_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0653.localPairCheck (smallEmbedding record035) (record035.maps 5)
      (record035.inverseMaps 5) record035_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record035_frame005_links_0000 record035_frame005_links_0064)
theorem record035_frame005_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) : Supported record035 5 :=
  of_group record035 5 (smallEmbedding record035) (small_cells_exact record035 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0653
    Papers.RationalityTen.SharedFrameCatalogue.group0653_facts record035_frame005_indices record035_frame005_graph record035_frame005_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (Fin.cases (record035_frame002_supported hcells) (Fin.cases (record035_frame003_supported hcells) (Fin.cases (record035_frame004_supported hcells) (Fin.cases (record035_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x32e9962ca464b323d902c7856e2b39580ab9555aa915369b14a9a46d1fc8a0434213508a83d41b20bccf467533799a0cc265a3299930c8a63d2ba95b0aa253529314289d04df26212a093247d23291848b64562288da869e33018f8bf85dc2c91570a3c4fc25d12688c845422310e08544101a20b5051427610807f034813609103c01b80be05c02d81680ae05602a812408003f01b009c04c024011808804201f00f0074024010007803801a00b00500240100040018008002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x1652c6582ae55a2abd489db38a6a4cb9772c250c728ad10a1b4147fefc5f43dd7aef45afb5d6aed35a1b3b662c998e30b59cb215f2ad54aa5d43a814e49892ca4846a8bd1121942274ce49bb36468cce18c2fe5c0b395729a4f49892723c458890f81ce36c6a8c0176298438800dc19c2c8560aa1502885009e11c2003f06c09c130240460881081f03c0740901001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
def record036_frame003_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x12b653ca093124a43c7e8730c214c2483304e053dd77cea1ccb7a6c8d51a7348688d016eadb5aeb4d67acb58cb055e2b44f29d9362614ba9391d2364588710ba073e67c0f49e33b8678ca9893005c8b59562a05189f13325646c8a11021440c7f8e41a2320618ab154248400790d41902b0530a41442704d09810c1e03b068098128230440841001e03a0700901001e0380680b0140240400400600800800 } : Fields).get c.val)
theorem record036_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record036_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record036) (record036.maps 3)
      (record036.inverseMaps 3) record036_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record036_frame003_links_0000 record036_frame003_links_0064)
theorem record036_frame003_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 3 :=
  of_group record036 3 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record036_frame003_indices record036_frame003_graph record036_frame003_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (Fin.cases (record036_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a56ce4662aad1518a62528289d416948473a2b510a86442120c101a7fb3ed9ed4f4a7932c01560a5c51c279935c8283b31bc8d4466030e17e0b6458e2a714089c44be20d10407e83d81e50eb87083761b40d6869833e1980c886042e616c0b2857c2a414409e84bc25011908983d81aa09b04881e00ee06e02f81700b605a02c015c0ac05502000fc06c027012008c04402000f807803a01b009004401e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
def record037_frame002_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x171ab595a6a8e94249f14f12705366931463a2410e4846410203cfd87db3e11e40efa76b3191838bde5e12e116d0a7a4e725e128890246422b90f085e41b1fa8f9c7b634e19d0c545ee2e81650a7451427813689804a424711d08883fe1f20f2875436a19c0c805e42da1560a2042019009b04881e00ee06e02f81700b605a02c015c0ac05502000fc06c027012008c04402000f807803a01b009004401e00e006803001600a004802000a0040018008002000 } : Fields).get c.val)
theorem record037_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record037) (record037.maps 2) (record037.inverseMaps 2) record037_frame002_indices (Fin.ofNat record037.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record037_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record037) (record037.maps 2)
      (record037.inverseMaps 2) record037_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record037_frame002_links_0000 record037_frame002_links_0064)
theorem record037_frame002_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 2 :=
  of_group record037 2 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record037_frame002_indices record037_frame002_graph record037_frame002_links
def record037_frame003_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x69867e6765ce5bb5a859d58657b52d4f34cc4ba4aa49949247f47546844f44643b39237e36735d34a33f2f12b029027e26e25924f24023922c2132071fe1bf1bb1ae19e19618617917216b16515d15514f14713c13312e12712211a10d1070f90f30ea0e60cd0b309908f07707606d05e05b05a05905705605505404003f03602702402302202001f01e01d01b01201100f00e00d00c00b00a009008005004003002001000 } : Fields).get c.val)
theorem record037_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record037) (record037.maps 3) (record037.inverseMaps 3) record037_frame003_indices (Fin.ofNat record037.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record037_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record037) (record037.maps 3)
      (record037.inverseMaps 3) record037_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record037_frame003_links_0000 record037_frame003_links_0064)
theorem record037_frame003_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) : Supported record037 3 :=
  of_group record037 3 (smallEmbedding record037) (small_cells_exact record037 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record037_frame003_indices record037_frame003_graph record037_frame003_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (Fin.cases (record037_frame002_supported hcells) (Fin.cases (record037_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x648314d86ea2b4f7274930497d4b7a5852b494c49ea4c124491b486a4191d08e146d1a64cb263c2b91584a7a518282938497a49a23b919c8864321f78f7c79e3031790b3855229613909384562080fc07503861800b8058029e1480a084e826612c09284782140ef068826c12207803701a00be05e02e016c0b405802b81580aa04001b00c004e026012008c04402000f807803a01b009004401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
def record038_frame002_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x695b39198aa62513a82d288932486239d1a88ad443a1910848304069fecf6a7a53c994b89e64d72080ff87b03b31d00de46a63301870bf05b22c714089c44be20d10407e83d81e50eb87203761ad0d306603221730b605942b21520a5851027a13609784a02260f706a826c12207803701a00be05e02e016c0b405802b81580aa04001b00c004e026012008c04402000f807803a01b009004401e00e006802c014009004001800a0040018008002000 } : Fields).get c.val)
theorem record038_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 2) (record038.inverseMaps 2) record038_frame002_indices (Fin.ofNat record038.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record038_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record038) (record038.maps 2)
      (record038.inverseMaps 2) record038_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record038_frame002_links_0000 record038_frame002_links_0064)
theorem record038_frame002_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 2 :=
  of_group record038 2 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record038_frame002_indices record038_frame002_graph record038_frame002_links
def record038_frame003_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1111.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1111.count (({ width := 10, code := 0x9865491e1e84604799e577dd9759d0725c56fdbc6d9b3695a267d765a55c4f93d4dd314b9284851d45d144390b3f4fa3dcd9360d2330c930cbc2e0b22bca929898254922408f2388d2308b22889218821f4741b862170571384d12c4a12447118451103b0d43009c26090230882007c1e0741b0481103c0e0340b02809020060140400c0200400 } : Fields).get c.val)
theorem record038_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record038) (record038.maps 3) (record038.inverseMaps 3) record038_frame003_indices (Fin.ofNat record038.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record038_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1111.localPairCheck (smallEmbedding record038) (record038.maps 3)
      (record038.inverseMaps 3) record038_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record038_frame003_links_0000 record038_frame003_links_0064)
theorem record038_frame003_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 3 :=
  of_group record038 3 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1111
    Papers.RationalityTen.SharedFrameCatalogue.group1111_facts record038_frame003_indices record038_frame003_graph record038_frame003_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (Fin.cases (record038_frame002_supported hcells) (Fin.cases (record038_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
def record039_frame001_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a14cf56752ac14f094448623b51d08e146d234d1988c545f22dd15c8a9451226512488b33918e4a3a4e426313049744b3256929893e498248922090647d23a91bc8d231916d0aa453228a13d09ac4b624c11e087441c1c60db069c32e1880bc05a42b213a09583dc1e00e9071036c1a80af04d81e00ee06e03581a80d206802f81700b605a02000fc06c03301900c4060027012008c04401b009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record039_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1) (record039.inverseMaps 1) record039_frame001_indices (Fin.ofNat record039.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record039_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record039) (record039.maps 1)
      (record039.inverseMaps 1) record039_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record039_frame001_links_0000 record039_frame001_links_0064)
theorem record039_frame001_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 1 :=
  of_group record039 1 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record039_frame001_indices record039_frame001_graph record039_frame001_links
def record039_frame002_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a62cea660a97d4488e7456a20d0f286742aa1150668224081ff8fc87dc3e59ec8f4479029593c07663791a78d146663211888bfc5dc2dc1650ac055029713f09b84b81ec0eb87083761b40d6869833e1980c8860c2f81590a9052c28813d09b04bc25011a08983d41dc0e707003641a60af04d81e00ee06e03581a80d206802f81700b605a02000fc06c03301900c4060027012008c04401b009003c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record039_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2) (record039.inverseMaps 2) record039_frame002_indices (Fin.ofNat record039.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record039_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record039) (record039.maps 2)
      (record039.inverseMaps 2) record039_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record039_frame002_links_0000 record039_frame002_links_0064)
theorem record039_frame002_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 2 :=
  of_group record039 2 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record039_frame002_indices record039_frame002_graph record039_frame002_links
def record039_frame003_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa55a28a039038d67f77bf79a79378377276375373e72a7166fb6f06de6c36b069d59d5704bd4904744704634554474394284184073f03e93db3c23b33a32e72be29628627526725a2492392282091fa1ba1ae1a019118317316515613712b0f10e60d90cc0be0b209f09507607506c06906806706605d05a05905804003f03603303203103002702402302201b01200f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record039_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 3) (record039.inverseMaps 3) record039_frame003_indices (Fin.ofNat record039.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record039_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record039) (record039.maps 3)
      (record039.inverseMaps 3) record039_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record039_frame003_links_0000 record039_frame003_links_0064)
theorem record039_frame003_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 3 :=
  of_group record039 3 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record039_frame003_indices record039_frame003_graph record039_frame003_links
def record039_frame004_indices (c : Fin record039.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x67164962f5765574cb4aa49449248647b46f46845c44d43f42b42941c40b4023f633d31e29227125b25624d24023822f2212142061f21ed1e41d21c91bd17116115414f14914313d13813212d12511f10a1051000fb0f60f00ea0e50da0d40be0b80b30af0aa0a709708b07006f06706406306206105805505405303f03e03603303203103002702402302201b01200f00e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record039_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record039.data.requiredEdges q = true := by decide +kernel
theorem record039_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record039_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record039) (record039.maps 4) (record039.inverseMaps 4) record039_frame004_indices (Fin.ofNat record039.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record039_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record039) (record039.maps 4)
      (record039.inverseMaps 4) record039_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record039_frame004_links_0000 record039_frame004_links_0064)
theorem record039_frame004_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) : Supported record039 4 :=
  of_group record039 4 (smallEmbedding record039) (small_cells_exact record039 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record039_frame004_indices record039_frame004_graph record039_frame004_links
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (Fin.cases (record039_frame001_supported hcells) (Fin.cases (record039_frame002_supported hcells) (Fin.cases (record039_frame003_supported hcells) (Fin.cases (record039_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1a62d2b692b46da28cfe65a32518f4c3f60eaf31646af556aaa4d4e6a1a4a525111e08dd45ca29906c8224011fb8f767a839e1cd8e207013749b68d3c69133c99b0c526142c995b8aa254829794189d24db25f12688ea45922690c48263f41d18dec6ca3601950c245f02dc1658a444e026112508ec41a1fe09204601c00d605f02f41660b2053824010606c02f815009403301380700240070018008002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
def record040_frame002_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x87e1c8661684e1182e047f1f47b1e3755cf71dbf6ddaa6859e64d8e61d825e1735b16757d5c5394b519424f93a4d5314b5294891f4711844d0e42d08404ff3e0f53c8eb3a4e2378d9350ce318c42fcb92d4b02b0a72849d260942348b1886014850128491144410c400f0390c42a094200641202c0400c0200400 } : Fields).get c.val)
theorem record040_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record040) (record040.maps 2) (record040.inverseMaps 2) record040_frame002_indices (Fin.ofNat record040.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record040_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (smallEmbedding record040) (record040.maps 2)
      (record040.inverseMaps 2) record040_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record040_frame002_links_0000 record040_frame002_links_0064)
theorem record040_frame002_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 2 :=
  of_group record040 2 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record040_frame002_indices record040_frame002_graph record040_frame002_links
def record040_frame003_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x30760cc1380f00dfcbc5762e7db6b5f6229cd30a5143e83cde9011ee3245e8a112611c1c81d01df6be4786ef9dc3b475aea5c738a706df9ac352606bd570ad5598b01572a7530a153aa634b892919a214087d8f11da39a6f4d99a533a60cb99682b453c97926196318588ab1422804b09511e1fc3b0650b21382403304e0700900700600800800 } : Fields).get c.val)
theorem record040_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record040) (record040.maps 3) (record040.inverseMaps 3) record040_frame003_indices (Fin.ofNat record040.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record040_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record040) (record040.maps 3)
      (record040.inverseMaps 3) record040_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record040_frame003_links_0000 record040_frame003_links_0064)
theorem record040_frame003_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 3 :=
  of_group record040 3 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record040_frame003_indices record040_frame003_graph record040_frame003_links
def record040_frame004_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0573.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0573.count (({ width := 9, code := 0x35dadd569b479fcbe57258ac3dfee771b75a2cb5da4d1e833f9ecf26933984ba53278dc662d1387c3609027fbf1e8f272385badb6c355a4cf6631d88c15faf16eb355a9d46a14fa6d329649a3d188943210fc7c30978ae56279389449239047635188b04e1d0b8401805018080200 } : Fields).get c.val)
theorem record040_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record040) (record040.maps 4) (record040.inverseMaps 4) record040_frame004_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record040) (record040.maps 4) (record040.inverseMaps 4) record040_frame004_indices (Fin.ofNat record040.n i)) 64 98 :=
  interval_of_check _ 64 34 (by decide +kernel)
theorem record040_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0573.localPairCheck (smallEmbedding record040) (record040.maps 4)
      (record040.inverseMaps 4) record040_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 98 record040_frame004_links_0000 record040_frame004_links_0064)
theorem record040_frame004_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 4 :=
  of_group record040 4 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0573
    Papers.RationalityTen.SharedFrameCatalogue.group0573_facts record040_frame004_indices record040_frame004_graph record040_frame004_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (Fin.cases (record040_frame002_supported hcells) (Fin.cases (record040_frame003_supported hcells) (Fin.cases (record040_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x71e71d71971370f7097087067056ee6ec6e56d56d36ca6b56a569d69468364a64463c63962a6236066035ed5e65cf5cc5c75c45bf58357956d56354853f52251450a4e54dc4ca4bc4aa49f49846c46645745343d4324084043e33d83c13bc3b83b33ae37036635a35033332c3133072fe2da2d32c42b82a829e2992081e71b118917517111510a0ef0e00bf0b60aa0a908a08907c05204801c01601301200f009007002001000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (smallEmbedding record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
def record041_frame002_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73172e72b72472171670f70e7076e56e26d76c86c76c06a169768d68a68063162c62161c60f60a5e55df5ca5c45af5a259458b57d53753152852250d5004d34ca4bc49c49548848147346c46543b43442241b40b4043de3d63ba3b539e39238037736b32031830b3062ef2e32b22a929d27c27626926325624e2481b419916d15713f13a0f90f50dd0d20bf0bd0b40b308c08b07e05204801c01601301200f009007002001000 } : Fields).get c.val)
theorem record041_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record041) (record041.maps 2)
      (record041.inverseMaps 2) record041_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame002_links_0000 record041_frame002_links_0064)
theorem record041_frame002_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 2 :=
  of_group record041 2 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record041_frame002_indices record041_frame002_graph record041_frame002_links
def record041_frame003_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0925.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0925.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0925.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0925.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0925.localPairCheck (smallEmbedding record041) (record041.maps 3) (record041.inverseMaps 3) record041_frame003_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0925.localPairCheck (smallEmbedding record041) (record041.maps 3)
      (record041.inverseMaps 3) record041_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame003_links_0000 record041_frame003_links_0064)
theorem record041_frame003_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 3 :=
  of_group record041 3 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0925
    Papers.RationalityTen.SharedFrameCatalogue.group0925_facts record041_frame003_indices record041_frame003_graph record041_frame003_links
def record041_frame004_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0950.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0950.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0950.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0950.localPairCheck (smallEmbedding record041) (record041.maps 4) (record041.inverseMaps 4) record041_frame004_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0950.localPairCheck (smallEmbedding record041) (record041.maps 4) (record041.inverseMaps 4) record041_frame004_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0950.localPairCheck (smallEmbedding record041) (record041.maps 4)
      (record041.inverseMaps 4) record041_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame004_links_0000 record041_frame004_links_0064)
theorem record041_frame004_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 4 :=
  of_group record041 4 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0950
    Papers.RationalityTen.SharedFrameCatalogue.group0950_facts record041_frame004_indices record041_frame004_graph record041_frame004_links
def record041_frame005_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0911.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0911.count (({ width := 9, code := 0x592c762b0d82bf5eaed72b559ac55ead55a9d4aa350a751287409ecea73369acbe5d2b94c9a49238e46e351789446190b8541a0b02803f1f4f9793c5dceb7439dc8e36eb71b2d86ab4da4cb653258cc1602f176ba5b2d564b156aad548e45a04ee733817cba572a1309648239007e38158902e11070341607028080200 } : Fields).get c.val)
theorem record041_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record041) (record041.maps 5) (record041.inverseMaps 5) record041_frame005_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record041) (record041.maps 5) (record041.inverseMaps 5) record041_frame005_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0911.localPairCheck (smallEmbedding record041) (record041.maps 5)
      (record041.inverseMaps 5) record041_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame005_links_0000 record041_frame005_links_0064)
theorem record041_frame005_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 5 :=
  of_group record041 5 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0911
    Papers.RationalityTen.SharedFrameCatalogue.group0911_facts record041_frame005_indices record041_frame005_graph record041_frame005_links
def record041_frame006_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0883.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0883.count (({ width := 8, code := 0xd9d7d5d0cdc9c7c4c2c1bfbdbab8b7b3b1adacaba4a2a19f9d9c989692918e8c8a88868584838281807d7c7b7776757472706e6a68676563625e5c58575452504e4c4b4a494847464342413d3c3b3a3836342f2e2b292826242322201e1d1918100f0e0d0c0b0a0908070403020100 } : Fields).get c.val)
theorem record041_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0883.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record041) (record041.maps 6) (record041.inverseMaps 6) record041_frame006_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record041) (record041.maps 6) (record041.inverseMaps 6) record041_frame006_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0883.localPairCheck (smallEmbedding record041) (record041.maps 6)
      (record041.inverseMaps 6) record041_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame006_links_0000 record041_frame006_links_0064)
theorem record041_frame006_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 6 :=
  of_group record041 6 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0883
    Papers.RationalityTen.SharedFrameCatalogue.group0883_facts record041_frame006_indices record041_frame006_graph record041_frame006_links
def record041_frame007_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0878.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0878.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0878.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0878.localPairCheck (smallEmbedding record041) (record041.maps 7) (record041.inverseMaps 7) record041_frame007_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0878.localPairCheck (smallEmbedding record041) (record041.maps 7) (record041.inverseMaps 7) record041_frame007_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0878.localPairCheck (smallEmbedding record041) (record041.maps 7)
      (record041.inverseMaps 7) record041_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame007_links_0000 record041_frame007_links_0064)
theorem record041_frame007_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 7 :=
  of_group record041 7 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0878
    Papers.RationalityTen.SharedFrameCatalogue.group0878_facts record041_frame007_indices record041_frame007_graph record041_frame007_links
def record041_frame008_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0882.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0882.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0882.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0882.localPairCheck (smallEmbedding record041) (record041.maps 8) (record041.inverseMaps 8) record041_frame008_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0882.localPairCheck (smallEmbedding record041) (record041.maps 8) (record041.inverseMaps 8) record041_frame008_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0882.localPairCheck (smallEmbedding record041) (record041.maps 8)
      (record041.inverseMaps 8) record041_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame008_links_0000 record041_frame008_links_0064)
theorem record041_frame008_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 8 :=
  of_group record041 8 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0882
    Papers.RationalityTen.SharedFrameCatalogue.group0882_facts record041_frame008_indices record041_frame008_graph record041_frame008_links
def record041_frame009_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0873.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0873.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0873.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0873.localPairCheck (smallEmbedding record041) (record041.maps 9) (record041.inverseMaps 9) record041_frame009_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0873.localPairCheck (smallEmbedding record041) (record041.maps 9) (record041.inverseMaps 9) record041_frame009_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0873.localPairCheck (smallEmbedding record041) (record041.maps 9)
      (record041.inverseMaps 9) record041_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame009_links_0000 record041_frame009_links_0064)
theorem record041_frame009_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 9 :=
  of_group record041 9 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0873
    Papers.RationalityTen.SharedFrameCatalogue.group0873_facts record041_frame009_indices record041_frame009_graph record041_frame009_links
def record041_frame010_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0877.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0877.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0877.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0877.localPairCheck (smallEmbedding record041) (record041.maps 10) (record041.inverseMaps 10) record041_frame010_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0877.localPairCheck (smallEmbedding record041) (record041.maps 10) (record041.inverseMaps 10) record041_frame010_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0877.localPairCheck (smallEmbedding record041) (record041.maps 10)
      (record041.inverseMaps 10) record041_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame010_links_0000 record041_frame010_links_0064)
theorem record041_frame010_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 10 :=
  of_group record041 10 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0877
    Papers.RationalityTen.SharedFrameCatalogue.group0877_facts record041_frame010_indices record041_frame010_graph record041_frame010_links
def record041_frame011_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0872.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0872.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0872.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0872.localPairCheck (smallEmbedding record041) (record041.maps 11) (record041.inverseMaps 11) record041_frame011_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0872.localPairCheck (smallEmbedding record041) (record041.maps 11) (record041.inverseMaps 11) record041_frame011_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0872.localPairCheck (smallEmbedding record041) (record041.maps 11)
      (record041.inverseMaps 11) record041_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame011_links_0000 record041_frame011_links_0064)
theorem record041_frame011_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 11 :=
  of_group record041 11 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0872
    Papers.RationalityTen.SharedFrameCatalogue.group0872_facts record041_frame011_indices record041_frame011_graph record041_frame011_links
def record041_frame012_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xb56b55b53b4cb49b41b3eb3db39b12b10b07afaaf7af2ac4abdaafaa6a869f19ed9e09da9ce9c798e98796795c93993092291590588d88287486583e8317e57d47c177676774072c7026e76d568868267867166565f62c6246035f75d65cd5c15b359f53b5315265194f64eb4b14a349245844a42a41a3f73e03d22e52bc2592181e81db15514511b0fe0cd0c00ac0ab08a08907e05204a01c01601301200f009007002001000 } : Fields).get c.val)
theorem record041_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 12) (record041.inverseMaps 12) record041_frame012_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 12) (record041.inverseMaps 12) record041_frame012_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record041) (record041.maps 12)
      (record041.inverseMaps 12) record041_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame012_links_0000 record041_frame012_links_0064)
theorem record041_frame012_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 12 :=
  of_group record041 12 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record041_frame012_indices record041_frame012_graph record041_frame012_links
def record041_frame013_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x104a08c0e81902603c0680b011fe3fb7f4fddfb3f07d0f95f03df7a8ebdd73ac752e8dcdb8b714df5bc3686cad89afb5b67ece59a32f648c818a30b608bc5772e65beb39622be540a7d4d297522a253aa744cc98528a4d49491d2122443a86109a074047e0f79e93ac750e61c636c6b4d41442624487d0ed1d42f05b0a914023c450821021d03986a0901000e0160260480780900e00800800 } : Fields).get c.val)
theorem record041_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record041) (record041.maps 13) (record041.inverseMaps 13) record041_frame013_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record041) (record041.maps 13) (record041.inverseMaps 13) record041_frame013_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record041) (record041.maps 13)
      (record041.inverseMaps 13) record041_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame013_links_0000 record041_frame013_links_0064)
theorem record041_frame013_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 13 :=
  of_group record041 13 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record041_frame013_indices record041_frame013_graph record041_frame013_links
def record041_frame014_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0600.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0600.count (({ width := 11, code := 0x10be1742d8590ae1442784d0920e41b8310560a41381501a013ff7f2f55e9bce798f25e43bd770ebdd4b9d72ce39c237e6b6d61a9b4f684cf59231d622bed7a2ea5cab6168acc568ac955aa7542a794828a4fc9e136a654c296129a2b4508890f21141a7ccf79e53a0728e09bc3626a8d295227c474840f61e42ec5b8a51342284307e0fa1c83886c0981100e0160260480780900e00800800 } : Fields).get c.val)
theorem record041_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record041) (record041.maps 14) (record041.inverseMaps 14) record041_frame014_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record041) (record041.maps 14) (record041.inverseMaps 14) record041_frame014_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0600.localPairCheck (smallEmbedding record041) (record041.maps 14)
      (record041.inverseMaps 14) record041_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame014_links_0000 record041_frame014_links_0064)
theorem record041_frame014_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 14 :=
  of_group record041 14 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0600
    Papers.RationalityTen.SharedFrameCatalogue.group0600_facts record041_frame014_indices record041_frame014_graph record041_frame014_links
def record041_frame015_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0459.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0459.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0459.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0459.localPairCheck (smallEmbedding record041) (record041.maps 15) (record041.inverseMaps 15) record041_frame015_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0459.localPairCheck (smallEmbedding record041) (record041.maps 15) (record041.inverseMaps 15) record041_frame015_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0459.localPairCheck (smallEmbedding record041) (record041.maps 15)
      (record041.inverseMaps 15) record041_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame015_links_0000 record041_frame015_links_0064)
theorem record041_frame015_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 15 :=
  of_group record041 15 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0459
    Papers.RationalityTen.SharedFrameCatalogue.group0459_facts record041_frame015_indices record041_frame015_graph record041_frame015_links
def record041_frame016_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0466.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0466.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0466.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0466.localPairCheck (smallEmbedding record041) (record041.maps 16) (record041.inverseMaps 16) record041_frame016_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0466.localPairCheck (smallEmbedding record041) (record041.maps 16) (record041.inverseMaps 16) record041_frame016_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0466.localPairCheck (smallEmbedding record041) (record041.maps 16)
      (record041.inverseMaps 16) record041_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame016_links_0000 record041_frame016_links_0064)
theorem record041_frame016_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 16 :=
  of_group record041 16 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0466
    Papers.RationalityTen.SharedFrameCatalogue.group0466_facts record041_frame016_indices record041_frame016_graph record041_frame016_links
def record041_frame017_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0458.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0458.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0458.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0458.localPairCheck (smallEmbedding record041) (record041.maps 17) (record041.inverseMaps 17) record041_frame017_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0458.localPairCheck (smallEmbedding record041) (record041.maps 17) (record041.inverseMaps 17) record041_frame017_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0458.localPairCheck (smallEmbedding record041) (record041.maps 17)
      (record041.inverseMaps 17) record041_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame017_links_0000 record041_frame017_links_0064)
theorem record041_frame017_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 17 :=
  of_group record041 17 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0458
    Papers.RationalityTen.SharedFrameCatalogue.group0458_facts record041_frame017_indices record041_frame017_graph record041_frame017_links
def record041_frame018_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x422e113083831c14e0650248104049ef2f6f7a1bbddddaed6735b8adbe4dd96ceb1d98ccc3c613aff57ccb6d5ad2c315f2ab9552aa394f2a614d5266530c97349d24991b28c6457a1650928244091facfa67c23a11cc8e106f33649ac8c726262ec1714b0a5712ad1514a5a476232914887e4061f90e9472437b1928c545e02de15b8a7c51c1ea0ea86943101740b7049c24010b07f03841b60ce066824011e08202a0128038016009804801e0090038008002000 } : Fields).get c.val)
theorem record041_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 18) (record041.inverseMaps 18) record041_frame018_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 18) (record041.inverseMaps 18) record041_frame018_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record041) (record041.maps 18)
      (record041.inverseMaps 18) record041_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame018_links_0000 record041_frame018_links_0064)
theorem record041_frame018_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 18 :=
  of_group record041 18 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record041_frame018_indices record041_frame018_graph record041_frame018_links
def record041_frame019_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0881.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0881.count (({ width := 7, code := 0x1bb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record041_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0881.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0881.localPairCheck (smallEmbedding record041) (record041.maps 19) (record041.inverseMaps 19) record041_frame019_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0881.localPairCheck (smallEmbedding record041) (record041.maps 19) (record041.inverseMaps 19) record041_frame019_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0881.localPairCheck (smallEmbedding record041) (record041.maps 19)
      (record041.inverseMaps 19) record041_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame019_links_0000 record041_frame019_links_0064)
theorem record041_frame019_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 19 :=
  of_group record041 19 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0881
    Papers.RationalityTen.SharedFrameCatalogue.group0881_facts record041_frame019_indices record041_frame019_graph record041_frame019_links
def record041_frame020_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x74574474374073d73b73673573471771470b6ff6fb6f86d46cf6bc6b369a62061e61661260a6025dd5d75bf5b559d59358c57f57852851d51450a4f04e74c44b64ac47d47245d44e4324204143eb3e53dd3db3d13cc3a43a038638036335d35134b33f2ef2e72db2d22b62b028a27f27324323a2222151f91e51db16f15f13c1271171130e40df0ce0c50b00ac0a30a208208107804d04701c01601301200f009007002001000 } : Fields).get c.val)
theorem record041_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record041) (record041.maps 20) (record041.inverseMaps 20) record041_frame020_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record041) (record041.maps 20) (record041.inverseMaps 20) record041_frame020_indices (Fin.ofNat record041.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record041_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record041) (record041.maps 20)
      (record041.inverseMaps 20) record041_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record041_frame020_links_0000 record041_frame020_links_0064)
theorem record041_frame020_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) : Supported record041 20 :=
  of_group record041 20 (smallEmbedding record041) (small_cells_exact record041 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record041_frame020_indices record041_frame020_graph record041_frame020_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSmall.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (Fin.cases (record041_frame002_supported hcells) (Fin.cases (record041_frame003_supported hcells) (Fin.cases (record041_frame004_supported hcells) (Fin.cases (record041_frame005_supported hcells) (Fin.cases (record041_frame006_supported hcells) (Fin.cases (record041_frame007_supported hcells) (Fin.cases (record041_frame008_supported hcells) (Fin.cases (record041_frame009_supported hcells) (Fin.cases (record041_frame010_supported hcells) (Fin.cases (record041_frame011_supported hcells) (Fin.cases (record041_frame012_supported hcells) (Fin.cases (record041_frame013_supported hcells) (Fin.cases (record041_frame014_supported hcells) (Fin.cases (record041_frame015_supported hcells) (Fin.cases (record041_frame016_supported hcells) (Fin.cases (record041_frame017_supported hcells) (Fin.cases (record041_frame018_supported hcells) (Fin.cases (record041_frame019_supported hcells) (Fin.cases (record041_frame020_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x48890d1fe3bc6d8d119630c5f8a110a20432845036053df7b0f3dd9bac734e4db3b636b4d359e338666c7987b0a5febdd792d45a2b31632be56aa714c2814fa9ad3225e4b09451a21f432831019f23c8758e59c23786a0cf99830c5e0b19602a8534a313a264458850f91de39c640be1762c45409a12c2404787d0f61c4360640c0130210260440680900900e00800800 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (smallEmbedding record042) (small_cells_exact record042 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSmall.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x73172e72b71d7097066de6c26bf69e69468d68662b61e60c5de5ca5be5a159458957f53052851c4ff4d34c84be49c48e48847a47346c45e43341c4053d53ba3af39138037536d31730b3002e22b22a729f27c26f26925c25624e2421be1a317115714913a0fd0f50e70d20bf0bd0b40b30ae0aa0a209e09508c08a07f05204901c017014012010009007002001000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x422e113083822c05601ef5b76d3b4dc96e0e6f937058cac2a5f4ad65618ae55522a394eca644cc26192c292546ca30d16485941c20910007eb3e99ec4e626f635a9894bb05b12b81568a84530232114885a3f11d28e3c6fc3251820bc05982b714f89f43e21dc0d606202f616e09704802240fe070836c19c0cd06002dc1520a304c824011c08302a012c03801700a00480200090038008002000 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 95 :=
  interval_of_check _ 64 31 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 95 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (smallEmbedding record043) (small_cells_exact record043 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSmall.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0599.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0599.count (({ width := 11, code := 0x38870ee19c1b82702de9bcb786dada9afb5a6aecf99e33b658ca191b1d630c4d88af45ceb8d712cd590b015729a52aa19402784d896d2ca5848c9011ba3245688d102013f87d0f99ed3ba76ce29b436068cce98f312590b015429a520a212422c4147f0f11902f8590a612e2083e0760ea1cc3906f0dc198308590aa1001e82704a0700900900e00800800 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0599.localPairCheck (smallEmbedding record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (smallEmbedding record044) (small_cells_exact record044 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0599
    Papers.RationalityTen.SharedFrameCatalogue.group0599_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0976.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0976.count (({ width := 10, code := 0x38fe378ae2386e0f80dfb74d9f65d8353d1b3fca321c6f07c06ffb96d1b36b8aceadaa2a2a5e879ea779c2659665191a358be2186a168460c801f2789d86f5bb6d99b6519262d7e5c16b5754e4b50d411013d4f3374d5328c12f4b127c97244872087f1ec741cc6f1b4691a06717c58144420e03508c1e050100340800400 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0976.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0976
    Papers.RationalityTen.SharedFrameCatalogue.group0976_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0490.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0490.count (({ width := 8, code := 0xe0dedbd9d7d5d3d2cfcccbc9c6bfbdbcbab9b5b2b0a7a4a3a2a09e9d9c9b9a999795928e8d8b8887858483817f7e7d7c7a6f6d6c69686665615d5c5a58524e4d4c4a4842413f3e3d3b3733322f2d2b2928272422201f1e191715120f0e0b09050403020100 } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0490.localPairCheck (smallEmbedding record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0490
    Papers.RationalityTen.SharedFrameCatalogue.group0490_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0469.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0469.count (({ width := 8, code := 0x9694918f8d8b89888582817f7d7977767473706f6e6b6a69686664636261605f5e5d5b595857545351504f4d4b4a49484744434241403f3e3c3a39383734302f2e2d2c29282726252422201f1e1d1c1b1a191715141312110f0e0c0a090706050403020100 } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0469.localPairCheck (smallEmbedding record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record045_frame003_links_0000 record045_frame003_links_0064)
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0469
    Papers.RationalityTen.SharedFrameCatalogue.group0469_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record045_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031

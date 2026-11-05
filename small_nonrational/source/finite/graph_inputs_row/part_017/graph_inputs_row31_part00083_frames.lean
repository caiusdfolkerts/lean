module
prelude
public import GraphInputsRow31Part00083Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups054Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083
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
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e6dd34dd16df3679a54cfd6743339810b99577ab6158ea6151ba88541e9944b72551288932472a30915289b443a10905e8093fe1f94fb07c83db1e9cf246d433296ecb48593296940c9da4db23010e88404101ff0ec471c3751b38d4c61c2fb16a8b205622a414a0a084e625e11c08ac43a20d10407a83ca1dd0e7872035a1a50c806082f81740b705642a414b0a204b424c11f08984141fa0f7074836810407903801b80d206803181780b805802b015009404101c00d8062030015809804802000f007003601600a004c0240110078034016009004001c00c005002000c002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record002_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 128 139 :=
  interval_of_check _ 128 11 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 139 record002_frame001_links_0000 (interval_append _ 64 128 139 record002_frame001_links_0064 record002_frame001_links_0128))
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x6e3b6e1a70d3367132558f2c2c609b03980cb61582aac154aa5052228ed46a9d14bc25b122690647f23d91bc876430a13107c830410a030ffc7f03f39ca8e3a71535e9a7ccd465c31f1824bfc5f82f9966cac65532a314389fc4f327793a490847422d114088a42b210906877e35f17f0bd85e02de16709dc4d025811e88b843c2030fd07a436e1910c185d02d61520a184e824c10707c03a413409304782080f806f035817c0b605902a815009404401f80e006e03401980c0052027012808c04202000e807002c013009003c01c00c005002000e0060018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record003_frame001_links_0000 (interval_append _ 64 128 136 record003_frame001_links_0064 record003_frame001_links_0128))
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x8128077c57c27ab79178b77176375f7586f76d86a86a267065964964061d5ed5e75b559e59158357855a55454b54553e53852f52952251c4c34ae4a447a46544d44242e40e3f03e43dc3ad38938037534d34132331a30c2e52df2d02c92c42b62b02ab27e23d1ec1dd1d31c71c31a71a119418517c16d15f15814713512712111410c0fc0ed0e60d80c80c40c109809108d08207c06f06b05f05b05905505404a04403f03803703403303002902702502302102001d01c01601301200f00e00c00a008007006003002001000 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record003_frame002_links_0000 (interval_append _ 64 128 136 record003_frame002_links_0064 record003_frame002_links_0128))
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0xa4947e7ccf89c33265fca793925e4845387d09e114077fcfe1fa3da77eeedd239b72ce39c4b736dad95b0b5a6a8d31a3341678be9782ea59cb0d5bab0548a45432814fc9752223e46e8991021642482cf69e73b6754e79c137a6e0ce17a2a6534a41422804a894121236458871052043ec770e31be35c698cb1883045d8b115c2a8440851021dc390670c81682b8550a21402384207a0dc1b0330640bc1482704a08c1082003a0700b01302403c0700c0140200380600600800800 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record003_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record003_frame003_links_0000 (interval_append _ 64 128 136 record003_frame003_links_0064 record003_frame003_links_0128))
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe3b6bdb561a92d366973445a16cf867b33b97a2b805902c4d55ea8553ba9994289b44d3a50d23290b47d23c51d08da465231517e8b545822a514689b449222cef87263839b54d8668133898e0c505d12d91600adc52c28e138c9a64c626092e89664ad252127c92c48f245120c8f647723791a48083911c00c605da2d91638ad455228a12d892445a21d10588003a41c60d385e02cc14a09d04a023a0f707883a41c40db06a02c413a07203781a80d2063030016c0b404201f80e807003701a00c806203001580a4050025011808802c013007003401800a004802000e006002000c004001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record006_frame001_links_0000 (interval_append _ 64 128 141 record006_frame001_links_0064 record006_frame001_links_0128))
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6fb6d36c16ae6a069a67e67966a6686646205fe5da5d45b05a55a259e57554c54551c50f50b5075044f44dd4c84c04b74a549f49448b48047146a42a4053ef3e03d83ba3b33a63a238037035f35833d33732c32a32131930e3012f62eb2e72d82d22cf2c82b92b72ad2a827924d24721b20f20a2061f91ed1d11b01a319118917c17415414c13711f1131060ff0f30ee0d40cb0bc0b00a80a009108706c06906406305d05a05505404203f03a03803703403203103002b02902802502302201601300e00d00c00a009008007006004003002001 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record006_frame002_links_0000 (interval_append _ 64 128 141 record006_frame002_links_0064 record006_frame002_links_0128))
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x51c9eb3966b4cb9872b654c9b9312462ac3e85108a043fb7f2fcded3c0776e95cc39471ee31c3b7d6e2db9b4b5f6bad55a834a67eced762ce586ae158298524a093ea5d49e8fd1ba26442841062064047f4fb9f23d67a0ef9d93b0740e39c53766dcce17c2f4568a894e292508a01352504848e11621c42c7d8f81dc37c6b8cf196310610b61662b4548a6146250450690ce18c3105d0b615c2b04007a0e41b8360660c41802f0560a4140250460880b01301c0340600a0120200380600800c01001 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record006_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 128 141 :=
  interval_of_check _ 128 13 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 141 record006_frame003_links_0000 (interval_append _ 64 128 141 record006_frame003_links_0064 record006_frame003_links_0128))
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x6285df5af59c59359058858057856b56856055154954653e53152a52242e3e53b53a22b02ad2a529d29528828527d26e26626325b24e24723f1b41b11a91a219a18d18918217616e16a16315815014914213f13713012811b1171101040fc0f80f10e60de0d70d50d10cd0c90c50c10b70b10ad0aa0a90a309f09c09b09a09509209108e08d08c08207c07907807707206f06e06b06a06904a04404104003002b02802702402302201b01601301200f00e00d } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
def record008_frame002_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x1785b5655855f5795c56958555545494f5354c52947515434891743d0b378dd36cd935cd434cd1338cc32cc9318c430895250922408e22c8a2208520c822007d1ec791dc761d0721c06d1b06a19c651906217c5d16c5a1645815c56154541445013c4e12c4a1244811c420fc3e0ec3a0e4360d4340cc320b42a0a426094240842007c1e07418054140441003c0e024060140200400 } : Fields).get c.val)
theorem record008_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2) (record008.inverseMaps 2) record008_frame002_indices (Fin.ofNat record008.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record008_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record008) (record008.maps 2)
      (record008.inverseMaps 2) record008_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record008_frame002_links_0000 record008_frame002_links_0064)
theorem record008_frame002_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 2 :=
  of_group record008 2 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record008_frame002_indices record008_frame002_graph record008_frame002_links
def record008_frame003_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x1cb6fdb66c5af6b9ab6a1a56819f67197651936418c6298859d5b5494d4811f47119459114410d42105411013f4fb3e4cc32cc8314c22f4bc2e4b42c4b02b4a929ca528ca227c9c2649424c9022c8821c842007e1f07b1e8791e0771d8751c8711c06f1b06b1a8691a0631805f1705b1685715855150531384b12847118450e0370d8350c02b0a027090230881b058130480f0380d } : Fields).get c.val)
theorem record008_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3) (record008.inverseMaps 3) record008_frame003_indices (Fin.ofNat record008.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record008_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record008) (record008.maps 3)
      (record008.inverseMaps 3) record008_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record008_frame003_links_0000 record008_frame003_links_0064)
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
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e59d1edb26d2349d9c0cca5cfab65582a8952f2935446a104aba50d1f48e6460a2b113488a3f49f58f8e7b73359694b1a55529514649de4dc211903c78c3b21c68de06cc35615a8a8852628310a07e83e61eb0f287783ac1d00e3870836819f0c505ec2ea15f0a9051025e12108c84301ec0f004a824811a08c04081c80de06d03501a40c606002e816c0b405702b01540a804901d00dc06a03201880ac050025011808803e01e00e8070036016009804402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x33318b6bf75f62e296acb4e55fa969492a0f4f6a77d37a9b449fa4b11b68c6452223d10a8773e91ef4f54792360994cc8060b2f59778b7c5b52a494e09e84e626492ec9644a721310588103f71b08c5460c2f61740b645922bf1578a744f025211888484021d50da86702f21640ab04c42100fb04a824811a08c04081c80de06d03501a40c606002e816c0b405702b01540a804901d00dc06a03201880ac050025011808803e01e00e8070036016009804402000e0068030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1d3cdaf67eb3b9918c4f61e2d29530a89513a7a93ae9894c125bd2c095a4a5a51527a93049124351fe8f7478a3a8fa270b37d9a54caa6412c215c8a7a51728293809a24bd24d11dc88642320890087e23151818b38550296138898849c22b10407503681a20c9860829e1480a084e825812508b84282080ef04a824811a08c03901bc0d4069034018c0c005e02d81680b005702b01540a803a01b80c806203001580a004c023011008003e01e00e8070036016009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f2ce8f6d93679a4ece06652e7d5b2ac752f288d4209574a224311cc8d4456226910e8644212034fd27d83e41edccd65a52c994a89de4dc21190407b03b21d00de06cc3531980c385b22b51520a5050621410687e83d61e50eb07403901bb0d686603141820be05d42b21520a5851026c12f090844c2180f704a824811a08c03901bc0d4069034018c0c005e02d81680b005702b01540a803a01b80c806203001580a004c023011008003e01e00e8070036016009804401c00d0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x1ea3aa6f4dd9ab342678c356ead9572a954fa7c4f29c935a694c49812e2574a29212123e4788e5039d73a66cccf9992ec5ccb61652c6570ad1562a252ca113c2704d89990d21440c7e0fa1e63c4768e81c4364698cf19a328600bf17c2f45d8ba1702d85a8b2122238448880e01b4340670cc1842f05c0b21602b0550a814c2903a06e0c8188300560a0130230440800f81e03a0700d8160260440700d0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x38edaf6d3168433cd9dabd15902abd4eea664da250d2168fa473a3811b28d246222f515e8a8450a268ef86d533898e0c5058028e138c9a64c025c92c895849e24b922490447c23b0e446302d91638aa453228a13d096c49822d10e88384001c60db069c32e1780b4852827412b08e826812a09204682300ee07203781a80d206803181800b605a02c81600ae05602a815007e03a01b80c806203001580a0046022010808003e01e00e8070036016009803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x3a79b5ecfd646313d878b4a54c289d3d49d74c4a58129694549ba4c125292248a24351fe8f8478a3a8fa270b34a9954c8258428b93809a24ac24d12208ee455221908c8244021f88c5455027113108f445621910407983a81b40d1864c30414f0a4050427412c092845c22010a082026812a09204682300ee07203781a80d206803181800b605a02c81600ae05602a815007e03a01b80c806203001580a0046022010808003e01e00e8070036016009803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1108.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1108.count (({ width := 9, code := 0x4da6b3093c86411e8cc42150981be9e8f3783bddced75ba9d0e773395c6de6ab3d9cc85fae570b55a2cd64b057ab558ab5529136954a245208f4723116894421d0c8341205007e3e9ecf4793c1d0de6c33998c85f2e15cac55281349047231148843211047e3a1b8c86230158a04622108803e1e0e8703616098381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1108.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1108
    Papers.RationalityTen.SharedFrameCatalogue.group1108_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e59d1edb2693b381994b9f56ca979446a104aba39915889a43b21910a484240fa034fd27d93e41edccd65a529513bc9b84231d90de06cc3421980c7861c2eb16c8ad454a29414188503d61d60e807083761b40d6867c33018a0c185f02ea1590a9052c2881360978484234113086026812a09204682300ee07203781a80d206803181800b605a02c81600ae05602a815007e03a01b80c806203001580a0046022010808003e01e00e8070036016009803801a00c0058028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame004_links_0000 record013_frame004_links_0064)
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
def record013_frame005_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0xf51d537a6acd099e30d5baae552a9f4f89ad312604b495d2a2514969212123f4788e5039d736667ccc9762ca570ad1542a2538a59452844f09c9362664347e0f31e23ac740e51c43706c8d31a0334650c017e2f85e8bb1742e05b8b616a2584888e1122203a8700da1a0338660c21782c8580ae1582a8540a61481f83a06e0c8188300560a0118220420800f81e03a0700d8160260380680c0160280480800e0180280400600800800 } : Fields).get c.val)
theorem record013_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record013) (record013.maps 5)
      (record013.inverseMaps 5) record013_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame005_links_0000 record013_frame005_links_0064)
theorem record013_frame005_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 5 :=
  of_group record013 5 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record013_frame005_indices record013_frame005_graph record013_frame005_links
def record013_frame006_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1107.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1107.count (({ width := 9, code := 0x4da6b3093c86411e8cc42150981be9e8f3783bddced75ba9d0e773395c6de6ab3d9cc85fae570b55a2cd64b057ab558ab5529136954a245208f4723116894421d0c8341205007e3e9ecf4793c1d0de6c33998c85f2e15cac55281349047231148843211047e3a1b8c86230158a04622108803e1e0e8703616098381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record013_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record013_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1107.localPairCheck (smallEmbedding record013) (record013.maps 6)
      (record013.inverseMaps 6) record013_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record013_frame006_links_0000 record013_frame006_links_0064)
theorem record013_frame006_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 6 :=
  of_group record013 6 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1107
    Papers.RationalityTen.SharedFrameCatalogue.group1107_facts record013_frame006_indices record013_frame006_graph record013_frame006_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (Fin.cases (record013_frame005_supported hcells) (Fin.cases (record013_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x8078037fc7f77f07ea7e17dd7d67d17ca7c477376a75c74f71d7146f96e26de6d26c36ae66865c64d6386296206055ee5ca5c75bb5ad5a55a159759058958557b5745125034f64ef4b74a548e48247b4674534463f83e43d03c33af39d38637a35334833d33733232832131b31730d3063002d328227b22a22421c21520e2081c61b81b119a19118517c17213012711e1121090ff0f80da0d50c60c20b20a409a07106f06e05e05c05b05905705603803703602502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame001_links_0000 (interval_append _ 64 128 136 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x63831a98b8c5062130e584cc1d607b00d7eabee5ae2d0d654b1456eab49572aa6551aa2d4e8a604f1271535098f4bb25ad29092c45e22c111a87142da14106081b4039fe0fb87c63b19d14e5e7263759b54d766b23571a20cd66612fa1748b765b22d01628adc56528993e49b64d226612b493c49024491bc8be4502038ef47683621ab8cfc64e3151858ae0546291130092c46822210106e436019a0c205d02c014e08583f81ae0c9059029013407103781b80bc05c02d81640ae05601c00dc06c025012008c04001f00f004c02400f0070028012008002000c002000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame002_links_0000 (interval_append _ 64 128 136 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x9c13726acd299b3225f4bb96d2ce564a68df19a2ec568790e61742984d07a0a40b7bcf59e63c3772ed9d7ba6712e19be3726d8da1b03596a6d3da3b4060ebe9782ed598b0d5d2b956ca994da954c69492324246a8bd1322240a7f0f89ec3d2780ed1d43a2720e11bc33a5f4bd95b2b054ca694828a4ac92921230444851041fc390708da1a4338640c41682c4538a413423c440680ce1982c8580ae1542985206e0d81a82504808c1001f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame003_links_0000 (interval_append _ 64 128 136 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6cc6c86c16b86af6a569969368d68367766c6106085fb5ed5ce5c95b95a85a259c58b57952e5255124fe4f14ec4de4cb49348f47846545545043842c42441d40e4053d73ca3bd3b439538a37a36f36935c34a3402f52e42d02c52b82ac29c29225a24a23522c22420d1ff1f31ee1df1d51cc1ad19118c17116d16715f15b15813d13512f12612011611110d0f60f10eb0e30de0d70d10bd0b70ab0a909c09008a06a06806705705505405205004f03803703602502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame004_links_0000 (interval_append _ 64 128 136 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0xa033fa7ccf69e53c274ce79c937e6e4d896129a4dc9490f2123ec768eb1ba32c5a8690b611c1881f031fdbeb78ef09db3ac750e8dce39571ce21bf3766aed1da033b64ec6185303602bd576ae5574ab952a9f532a5147a884dc9892c25349a9091e23445c8a511a1c404774ec9b435c69cd099d3365d4b81662a252c9f136254410800f61d43886c0d516a2bc5109a12222c430670cc1942a8530a41402784e0680cc190240460881001f03c04c0900f01c0280480800800c00800 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame005_links_0000 (interval_append _ 64 128 136 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7e77df7d47cf7c87c37b97b27ae7a87a079573b7317237166f56f36e96dd6d96d16c06a866365b64863562a6256105f35b95b359f58557c57756b56055755053f5314f14dd4d44cc4a448c47a46d46845644743a3ee3d83c93bd3b53ac3a539d36f35934733b3343233163093042fa2ef2e52b327b27423c23422b21f2162111dd1d21c71af1a519618a17b14714113212411810c1050e10d90c10b90ac09a09206e06c06b05b05905805605405303703603502502402302001f01e01301200f00e00a009008004003001000 } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 128 136 :=
  interval_of_check _ 128 8 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 136 record014_frame006_links_0000 (interval_append _ 64 128 136 record014_frame006_links_0064 record014_frame006_links_0128))
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
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
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x354da94d3e69933b99accb3648b2158dac4a6142e156ecb695b1ac255caac855baaa550aa6852ba7512f696f48b243520a8fd47b23b10e886442920fd05e8244091ffcfde7353981ca8e4871d38b9ae4d646a23491a08ce26583289904c626213081660b1c5722ab150ca7251d28093e09e84ee274936c9964a524111c88d245b227910c87442c2100eec73c37e1b78d6c67c31e1878c145fa2f61780b7c57228d13c89a44b224b11e08bc43e21110107bc3241800bb053c28a12608c04241ba0d3030017c0b805b02b815809e04901f80a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame001_links_0000 (interval_append _ 64 128 151 record016_frame001_links_0064 record016_frame001_links_0128))
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
def record016_frame002_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x36d9b42d826afb475a10ce966332e9962ca464b2fad786b9f5c5ad25642afd574ab7159cac055ca8e537a9b14a9a51525e91948423f914089243e21990aa84d422a0f506c7893c01db4eb674739a1b7cdac6c33589a74d1467a33a99bccd066132d1788ba45b12c495d4ad855129a9490a3450827d13a09be4c4254125c91a47b23691948c245b22b0fa87803951bf0da869e33018f8c405f82ec16d8b2455c28f13f09bc4b624b11d08c845422310e082034418b0bd851427611808403f81b60d2030017c0b805b02b815809e04901f80a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2) (record016.inverseMaps 2) record016_frame002_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record016) (record016.maps 2)
      (record016.inverseMaps 2) record016_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame002_links_0000 (interval_append _ 64 128 151 record016_frame002_links_0064 record016_frame002_links_0128))
theorem record016_frame002_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 2 :=
  of_group record016 2 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record016_frame002_indices record016_frame002_graph record016_frame002_links
def record016_frame003_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0xf61ea3cc78cf01de3b475ceb1d43a0734e21c03796eadadb1b5c6b0d55a6b46684cf18eb1a5f6be179aee5d2b9963ac457eae95aab255aaa151a7e4f69e13a2704d895d2a25149a92522a4047a8e91b23245c89d12a1a41a821031fb3dc7a4f39e33c0770ed1cf3846f4dd9b73686c0d71aa34e678c99842f65ccb41592a0524a21402764dc9611d228434841041fe3f07b8f31dc3b0680cb18c2d05789e134254420810a41442704d0921202283f06e0a0130250480881081f03a0700a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record016_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3) (record016.inverseMaps 3) record016_frame003_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record016) (record016.maps 3)
      (record016.inverseMaps 3) record016_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame003_links_0000 (interval_append _ 64 128 151 record016_frame003_links_0064 record016_frame003_links_0128))
theorem record016_frame003_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 3 :=
  of_group record016 3 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record016_frame003_indices record016_frame003_graph record016_frame003_links
def record016_frame004_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0x3c3ef7b5ec3abe979de6396e4388e0f6fd9f60d7752d2b43d033dcd72ecaf25c2706baae7b8addb62d5ae6b6ac6aca9ea4a7e9aa56709b66a99a6297a4991a438fe3b8de328be2c8a2248821985a0a7fdfb7e1ec785dd76dd7751d0735c16d9b26c1ac6a5a568d9f6719261d7a5c56a57d52525434f93a4d531499194410a415013f0f93d0f03ace9340cb318b42bc9e26895210811404f1304b11c4610c3d0d42809825090220841f0741c050130481003c0e02c0a0240400c0200400 } : Fields).get c.val)
theorem record016_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4) (record016.inverseMaps 4) record016_frame004_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record016) (record016.maps 4)
      (record016.inverseMaps 4) record016_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame004_links_0000 (interval_append _ 64 128 151 record016_frame004_links_0064 record016_frame004_links_0128))
theorem record016_frame004_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 4 :=
  of_group record016 4 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record016_frame004_indices record016_frame004_graph record016_frame004_links
def record016_frame005_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1060.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1060.count (({ width := 10, code := 0x2418f6398d6328ba2a89a258861d8661283a0781a017f5f67d5f27b9e7799e174dd2711c36fdbb6ddb569da66899e6699865190631775d5745c56e5ad5f5755c5655654d4f5354c5254650d3e4f5374c52f4b9284891f4751a461154510e4210540d003f8fa3e0f53ccec39ce0370d834ccc320c5304bf2ecb82ccac2a0a52849f26c992549323c8e2087f1f0731c069198631705b11444104400f03b0e0350c026090230882007c1d06c1a050130481003c0e02c0a0240400c0200400 } : Fields).get c.val)
theorem record016_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record016) (record016.maps 5) (record016.inverseMaps 5) record016_frame005_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1060.localPairCheck (smallEmbedding record016) (record016.maps 5)
      (record016.inverseMaps 5) record016_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame005_links_0000 (interval_append _ 64 128 151 record016_frame005_links_0064 record016_frame005_links_0128))
theorem record016_frame005_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 5 :=
  of_group record016 5 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1060
    Papers.RationalityTen.SharedFrameCatalogue.group1060_facts record016_frame005_indices record016_frame005_graph record016_frame005_links
def record016_frame006_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x335d988cb165032018d0c4e61c30c983ac035f72d6566ab1c58a2bb558eaae553aa814fea68530277131c98449624792068e846923210e2864425a0c903a80e3fb1f70f8c7573a81d14e7472f3931bb0dc66d83649af8d6669f34c9a20cf866b3309798bb65c42d89688b2e57b2b29558a8e5342931454a104ea26913089664a024912088e645f2280ff87c23c51de8ea871836c1b10d5067632718a8c0c5c62c215c0aa852427f136897448e23411107fc3721a80cb858c2a012108704001b00c9030017c0b805b02b815809e04901f80a8050027013009004602100f8078028013009004001e00e00580280120040018008002000 } : Fields).get c.val)
theorem record016_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 6) (record016.inverseMaps 6) record016_frame006_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record016) (record016.maps 6)
      (record016.inverseMaps 6) record016_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame006_links_0000 (interval_append _ 64 128 151 record016_frame006_links_0064 record016_frame006_links_0128))
theorem record016_frame006_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 6 :=
  of_group record016 6 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record016_frame006_indices record016_frame006_graph record016_frame006_links
def record016_frame007_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0983.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0983.count (({ width := 12, code := 0x6e16dc6d86d46c26b66a869e69b69268667763362a6246216025e95e05dc5d85c95b85b257854d54851d51a51250a5065014c94c14b34a649c49548747d47243943743443142e42b4013fc3f23ea3e73e23d43d13ce3c73bd3b537d37836936035535034533833433032b3293223172ff2ec2e32dd2d42cc2c42be2b42af27526425324e24323622421c2182102092051fa1dd1c11b91b11a419a18f18a17d17216c15a12511c1150fc0f50e00d30c80a90a105a05905605505105004904603f02a02802702602402302101f01e01401301201000f00e00b00a009004003002001000 } : Fields).get c.val)
theorem record016_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record016) (record016.maps 7) (record016.inverseMaps 7) record016_frame007_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0983.localPairCheck (smallEmbedding record016) (record016.maps 7)
      (record016.inverseMaps 7) record016_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame007_links_0000 (interval_append _ 64 128 151 record016_frame007_links_0064 record016_frame007_links_0128))
theorem record016_frame007_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 7 :=
  of_group record016 7 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0983
    Papers.RationalityTen.SharedFrameCatalogue.group0983_facts record016_frame007_indices record016_frame007_graph record016_frame007_links
def record016_frame008_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0971.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0971.count (({ width := 8, code := 0xbab9b8b7b6b5b4b3b2b1b0afaeaba9a8a7a4a2a1a09d9b9a9998979695939291908f8e8c8b8a89878685838281807f7e7c7b7a7978777574737271706f6e6d6c6b6a6968666564636261605f5d5c5b5a5857565553514f4e4c4a484746444342403e3c3b3a38373635333231302f2d2c2a2928262524232221201f1e1d1c1b1a1918171615141312110f0e0d0b0a090706050403020100 } : Fields).get c.val)
theorem record016_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0971.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record016) (record016.maps 8) (record016.inverseMaps 8) record016_frame008_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0971.localPairCheck (smallEmbedding record016) (record016.maps 8)
      (record016.inverseMaps 8) record016_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame008_links_0000 (interval_append _ 64 128 151 record016_frame008_links_0064 record016_frame008_links_0128))
theorem record016_frame008_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 8 :=
  of_group record016 8 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0971
    Papers.RationalityTen.SharedFrameCatalogue.group0971_facts record016_frame008_indices record016_frame008_graph record016_frame008_links
def record016_frame009_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0659.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0659.count (({ width := 11, code := 0x174ae6dcab876cad75a7b39652c6582ae54ae93521a3942e834fd9eb3b6714d499723e3bc728ad14224c408730da0a40e80eff5fb3f17d0f75ebbae758ea1d23a0736e11c0b7c6f0dc5b435f6bad5da6b43676bd978ae45b0b39642be55aa8d4fa95516a1d40a724c495d2924647e8d517a224327ecf91e53ba74ce49bb3646acd099a320630bf9702ce580aa94b2884f49892723c4487c0f11d836c6a8c61802ec558a60b41642b0550a21402584707e0a81402704c0901182103e0780a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record016_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record016) (record016.maps 9) (record016.inverseMaps 9) record016_frame009_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0659.localPairCheck (smallEmbedding record016) (record016.maps 9)
      (record016.inverseMaps 9) record016_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame009_links_0000 (interval_append _ 64 128 151 record016_frame009_links_0064 record016_frame009_links_0128))
theorem record016_frame009_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 9 :=
  of_group record016 9 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0659
    Papers.RationalityTen.SharedFrameCatalogue.group0659_facts record016_frame009_indices record016_frame009_graph record016_frame009_links
def record016_frame010_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x139e714da9a132262cbe9612b653ca09311ce374628b91522744687b0e618429848ff5f03dd77cee1d83a673ae65bd3766dcd89acb5469cd21a232964ec8d8eb1361abfd7f2fa5e8bb571add5b6b5d69acf596a894ea8d4fa9e53b26c4c29712b24c4848e91b22c43885508a053f27ccf81e93c6724df9ac348678ca9893005ecb81692ba558a814627c4e89912923e46c8a1102143fc720dd1ac320618b21562a84c0920ae1582985209c134240430760a41382604a08c1102003c0740a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record016_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record016) (record016.maps 10) (record016.inverseMaps 10) record016_frame010_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record016) (record016.maps 10)
      (record016.inverseMaps 10) record016_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame010_links_0000 (interval_append _ 64 128 151 record016_frame010_links_0064 record016_frame010_links_0128))
theorem record016_frame010_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 10 :=
  of_group record016 10 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record016_frame010_indices record016_frame010_graph record016_frame010_links
def record016_frame011_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0616.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0616.count (({ width := 8, code := 0xacabaaa9a8a7a6a5a4a3a2a1a09f9e9d9c9b9a99989796959492918f8e8d8b898886858482807f7e7c7a78777675747371706f6e6d6c6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a3938373635343231302d2c28272622201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record016_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record016) (record016.maps 11) (record016.inverseMaps 11) record016_frame011_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0616.localPairCheck (smallEmbedding record016) (record016.maps 11)
      (record016.inverseMaps 11) record016_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame011_links_0000 (interval_append _ 64 128 151 record016_frame011_links_0064 record016_frame011_links_0128))
theorem record016_frame011_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 11 :=
  of_group record016 11 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0616
    Papers.RationalityTen.SharedFrameCatalogue.group0616_facts record016_frame011_indices record016_frame011_graph record016_frame011_links
def record016_frame012_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0549.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0549.count (({ width := 11, code := 0x112a22c3d8730be1542083105a08c06802f55e6bc677eee1da3af74ee95ceb97720dc1acb56680cf19c331656ca18930f614c097eafa5eabb5732bf578ad157aa8548a3d45a855009ed3a26d4d498d2ea574a48ad1221541a821039fc3ee7bcf59e43ba75ce99c93826dcda1ab34c684cf1973245fcba1682c256ca914a28a5009a9302524948f11a228440838fe1f23dc788ea1ca380638c41822e0598a814a28c4b0950b015c2a05309e138238410720a0130250480881081f03a0700a0130240400780e0160280480400600800800 } : Fields).get c.val)
theorem record016_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record016_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record016) (record016.maps 12) (record016.inverseMaps 12) record016_frame012_indices (Fin.ofNat record016.n i)) 128 151 :=
  interval_of_check _ 128 23 (by decide +kernel)
theorem record016_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0549.localPairCheck (smallEmbedding record016) (record016.maps 12)
      (record016.inverseMaps 12) record016_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 151 record016_frame012_links_0000 (interval_append _ 64 128 151 record016_frame012_links_0064 record016_frame012_links_0128))
theorem record016_frame012_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 12 :=
  of_group record016 12 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0549
    Papers.RationalityTen.SharedFrameCatalogue.group0549_facts record016_frame012_indices record016_frame012_graph record016_frame012_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (Fin.cases (record016_frame002_supported hcells) (Fin.cases (record016_frame003_supported hcells) (Fin.cases (record016_frame004_supported hcells) (Fin.cases (record016_frame005_supported hcells) (Fin.cases (record016_frame006_supported hcells) (Fin.cases (record016_frame007_supported hcells) (Fin.cases (record016_frame008_supported hcells) (Fin.cases (record016_frame009_supported hcells) (Fin.cases (record016_frame010_supported hcells) (Fin.cases (record016_frame011_supported hcells) (Fin.cases (record016_frame012_supported hcells) (fun j => Fin.elim0 j))))))))))))))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1a64c916142e096fab765b82da56c6b0057bab955aeac855baa8152ea8553ba9a14ae97b48b243120a8fd47b21d10c485241fa0bd0448123ff9fbce6a7303951c90e3a71735c9ac8d4469234119c4cb065132098c4c426102ab14049f24f427713a4904475234916c89e44621d10b08403ae1cf0e386fc36f1a70cf865c31e1878c105fa2f61780b385722a314689e44cc25912588f045821f10888083241820bb054428a12608d04241ba0d304382040ee06002f81700b605702b013c09203f014009c04802300f807803601500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame001_links_0000 (interval_append _ 64 128 142 record017_frame001_links_0064 record017_frame001_links_0128))
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1abecc664b2f7d7aabc35d8ae7d716b3d599ac8561eafd574ab655aaace563ab015729bd4a9a50925e919484228111e87c433215509884541ea0d8f127803b69d6ce8e73436f9b58d866b134e9a28cf467533799a0cc265a2c494d4a5051a28413e895049b24691ec8da466230916c8ac3d51e00ea472a37e1af8d3c67e33018f8c305f82ec16d8af855c29e14789f84d625b12588e846222a111887034418d0bd851c27611808503f81b60d204382040ee06002f81700b605702b013c09203f014009c04802300f807803601500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame002_links_0000 (interval_append _ 64 128 142 record017_frame002_links_0064 record017_frame002_links_0128))
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x1e33ae734e19c23806fade5bab696ced8db035c6b0d4da8b4d694d19a131d5f6bdd79aee5d2b1d61abf574ad558aad550a8d3f27b4f09d13826c4ae95128a4d4929152023d4748d91922e41a7b8f51e73c6780e11be3766dcda1b135c6a8d399a326630c217b2de5a0b09592a0520a21402764cc9612523a450861082083fc7d8f71e63b8680cc18c2d45789e136254420810d018c2e8520a2138268490901141f83704c0941102103a0700c81502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame003_links_0000 (interval_append _ 64 128 142 record017_frame003_links_0064 record017_frame003_links_0128))
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
def record017_frame004_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xec398e0f6ddaf67d9360d7750d3b4ad1f43d033bce735ccb2ecaf09baae6b8addb62b9ad6b1ab2a7a8e9fa6a959c26d9aa6698a5e9264690e3f8ee378ca2f8b228892207fde1779db75dd46d9b36c1ac6a5a668d9f6718e61d825e9715995f56952525424f93a4d52d499214651042505404fc3e0f43c0eb340cc318b52bc9e26c9521081194601685013c4c12c47118430f43509825088210741c0641505013048110400f0380c02c0a0240400c0200400 } : Fields).get c.val)
theorem record017_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record017) (record017.maps 4) (record017.inverseMaps 4) record017_frame004_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record017) (record017.maps 4)
      (record017.inverseMaps 4) record017_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame004_links_0000 (interval_append _ 64 128 142 record017_frame004_links_0064 record017_frame004_links_0128))
theorem record017_frame004_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 4 :=
  of_group record017 4 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record017_frame004_indices record017_frame004_graph record017_frame004_links
def record017_frame005_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1d20db7695b0097ecbdf5e5aed5740b3a596ac5d60aaf256f2b01568aa054629dd4c4959473a3591868ab44c20c104280f3fc9f9cfb67ca3da9e94d9c6c23559a5cd0266c30317e4bc65d12df16a8b185802b61560a8652e2128ecc74438f1bb8d905f82ed16d8b145662a714b0a044e2232115889043a21610408043f41f30f6078c3b81d50e707083761b40d6869833a1960c7862030217a0b985b027a13509704642240fe07b03bc1b60d504382040ee06002f81700b605702b013c09203f014009c04802300f807803601500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record017_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5) (record017.inverseMaps 5) record017_frame005_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 5)
      (record017.inverseMaps 5) record017_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame005_links_0000 (interval_append _ 64 128 142 record017_frame005_links_0064 record017_frame005_links_0128))
theorem record017_frame005_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 5 :=
  of_group record017 5 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame005_indices record017_frame005_graph record017_frame005_links
def record017_frame006_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74170d6ea68367e67767166c66763a63562c62361d6136035fc5f35ea5e35d756352a52251c51550e4d34ca4c44b84b04a94a049248843342e42742141c4173ea3e33da3d13ca3be3ae3a93a039739138730c2d92d22cc2c52be28327927026225825124b23f2372061fd1f61ee1e71d51cc1c51bd1b61af1ab1a71a319819118a18317d17316b16215915014813f13611310b1050f10eb0d90d50cf0bc0b508708107706005f05c05b05705604f04903f02802702402301f01e01b01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record017_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 6) (record017.inverseMaps 6) record017_frame006_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record017) (record017.maps 6)
      (record017.inverseMaps 6) record017_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame006_links_0000 (interval_append _ 64 128 142 record017_frame006_links_0064 record017_frame006_links_0128))
theorem record017_frame006_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 6 :=
  of_group record017 6 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record017_frame006_indices record017_frame006_graph record017_frame006_links
def record017_frame007_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x3696b0d278f31c631c5187f0c5f2bdd79aeedd4b9b70ee05bab696bed552e9f13ba72cd899f25a45c828e91aa3145b8a914206408800fddf73e7784ef9dbbae74ae79ca391716e15c037b5feb1d5e2b354aa6d31a594a090d1d233458895109f93e47b4f41e33aa738e31c03706b8d39a033262cc217c2ec5b8b215d2ac53ca51462844f88c1112163e4788dc1a43285a8ae1061f43a05e0ba1682c8550a81342383e05009c1202303e0780d81502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record017_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record017) (record017.maps 7) (record017.inverseMaps 7) record017_frame007_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record017) (record017.maps 7)
      (record017.inverseMaps 7) record017_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame007_links_0000 (interval_append _ 64 128 142 record017_frame007_links_0064 record017_frame007_links_0128))
theorem record017_frame007_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 7 :=
  of_group record017 7 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record017_frame007_indices record017_frame007_graph record017_frame007_links
def record017_frame008_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1063.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1063.count (({ width := 8, code := 0x9695949291908f8e8d8b8a8988878684838281807f7e7d7c7b7a797877767574737271706e6d6c6b6a69676665646362605f5e5d5c5b5a595857565554535251504f4e4d4c4a4948474644434241403f3e3d3c3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record017_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1063.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record017) (record017.maps 8) (record017.inverseMaps 8) record017_frame008_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1063.localPairCheck (smallEmbedding record017) (record017.maps 8)
      (record017.inverseMaps 8) record017_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame008_links_0000 (interval_append _ 64 128 142 record017_frame008_links_0064 record017_frame008_links_0128))
theorem record017_frame008_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 8 :=
  of_group record017 8 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1063
    Papers.RationalityTen.SharedFrameCatalogue.group1063_facts record017_frame008_indices record017_frame008_graph record017_frame008_links
def record017_frame009_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x251259146a33188bc5a2b1087c3a1b0c85c2611078341608fe7c3ddecf3793b1d6ea73b99cae470b81b0d76b355a8d36733598cb653258ec662b1186c25e2d96ab458ac154a95429548a35127d3c964a2491e8c43211047f3e1e4ee75399b8d86a33990c25f2e96cb2572a94c9a4a24108803a1c0d8602e168b05629140984a2311084401f0e87034190b8582a110803c1c0d0602c14090401c0c04018080200 } : Fields).get c.val)
theorem record017_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record017) (record017.maps 9) (record017.inverseMaps 9) record017_frame009_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record017) (record017.maps 9)
      (record017.inverseMaps 9) record017_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame009_links_0000 (interval_append _ 64 128 142 record017_frame009_links_0064 record017_frame009_links_0128))
theorem record017_frame009_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 9 :=
  of_group record017 9 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record017_frame009_indices record017_frame009_graph record017_frame009_links
def record017_frame010_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1940c385f72d31686b355952c71628adf56aab1d578aae553aa4d516a7f53a29a14c098e496246d2068e846921c50c284b41920750167f63ee1f18eae7503a29ce8e5e7263761b8cdb06c935f1accd3e69934419f0cd66612d89594ab454729a14989a44c62599280924486239917c8a03f01f08f5078a3bd1cd8e306f636c1b10d4067632718a8bd05c62d31610ae054c29213f89b44b224711a08883721aa0cb85942a012108804001b00c904382040ee06002f81700b605702b013c09203f014009c04802300f807803601500a004c024011008003c01c00c00580280120040018008002000 } : Fields).get c.val)
theorem record017_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 10) (record017.inverseMaps 10) record017_frame010_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record017) (record017.maps 10)
      (record017.inverseMaps 10) record017_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame010_links_0000 (interval_append _ 64 128 142 record017_frame010_links_0064 record017_frame010_links_0128))
theorem record017_frame010_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 10 :=
  of_group record017 10 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record017_frame010_indices record017_frame010_graph record017_frame010_links
def record017_frame011_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0974.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0974.count (({ width := 8, code := 0x9695949291908f8e8d8b8a8988878684838281807f7e7d7c7b7a797877767574737271706e6d6c6b6a69676665646362605f5e5d5c5b5a595857565554535251504f4e4d4c4a4948474644434241403f3e3d3c3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record017_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0974.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record017) (record017.maps 11) (record017.inverseMaps 11) record017_frame011_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0974.localPairCheck (smallEmbedding record017) (record017.maps 11)
      (record017.inverseMaps 11) record017_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame011_links_0000 (interval_append _ 64 128 142 record017_frame011_links_0064 record017_frame011_links_0128))
theorem record017_frame011_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 11 :=
  of_group record017 11 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0974
    Papers.RationalityTen.SharedFrameCatalogue.group0974_facts record017_frame011_indices record017_frame011_graph record017_frame011_links
def record017_frame012_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad4a95a519d29cb9c49ba9ae9a297e97796d96195694b93c93592c9209139068507f77e27d17bd7a675073d7297116fe6ef6dd6c66b366866365d65664b63d61861360a5ff5f35e55d75d25c95bf5b15a05044bd4ae4a048e47e4364274174023f33e83da3c53b636d36035234533a3203133052f52e72d72cb2bc2aa29628627526725a2472372262182071f81e71d918317216413612a0fe0f20e70c00b408307d07505e05d05a05905505404f04903f02802702402301f01e01b01501401301201101000f00e00c00b00a009004003002001000 } : Fields).get c.val)
theorem record017_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 12) (record017.inverseMaps 12) record017_frame012_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record017) (record017.maps 12)
      (record017.inverseMaps 12) record017_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame012_links_0000 (interval_append _ 64 128 142 record017_frame012_links_0064 record017_frame012_links_0128))
theorem record017_frame012_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 12 :=
  of_group record017 12 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record017_frame012_indices record017_frame012_graph record017_frame012_links
def record017_frame013_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x32d636c2d78ef0ddebb3752e85bcb716d2d6da7b43656ca58fb1360abd5169c936e6accf99123e40c758d316a2944986f0a1fcbf77e8fc5f63e6798f21e23be76cebdd23a373ce65c8b87666c3d84b055febe9662c4576ac9542a1538a3d42a5549c91d1f23544e8850ca1140e7f4fb9f33da77cea1c837a6d0d499e32e630c017a2e0594919192223d4768d3196304500990f21d43685b0b41602b8530a412c2303d05009c1202303e0780d81502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record017_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record017) (record017.maps 13) (record017.inverseMaps 13) record017_frame013_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record017) (record017.maps 13)
      (record017.inverseMaps 13) record017_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame013_links_0000 (interval_append _ 64 128 142 record017_frame013_links_0064 record017_frame013_links_0128))
theorem record017_frame013_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 13 :=
  of_group record017 13 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record017_frame013_indices record017_frame013_graph record017_frame013_links
def record017_frame014_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x33f658c8d8670ae11c137fefbde2bc3772eadcdb816dada5b1b5b6a6d2d44a2341a7dcec9bb2964ec939011c6354668c11661442484107209c0c7e0fbdf5be67bcf51e43c6786f01de3b76b2ca990317614bfd672c557cab951a9d534a55482644b293d21a384508810da1240e7ecf81ea3ba748e59c33786bcd199c324614bf17a2ec5bc989242323cc748d018a3045209b0ea1bc340560aa1482884d09811c2183b05009c1202303e0780d81502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record017_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record017) (record017.maps 14) (record017.inverseMaps 14) record017_frame014_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record017) (record017.maps 14) (record017.inverseMaps 14) record017_frame014_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record017) (record017.maps 14) (record017.inverseMaps 14) record017_frame014_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record017) (record017.maps 14)
      (record017.inverseMaps 14) record017_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame014_links_0000 (interval_append _ 64 128 142 record017_frame014_links_0064 record017_frame014_links_0128))
theorem record017_frame014_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 14 :=
  of_group record017 14 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record017_frame014_indices record017_frame014_graph record017_frame014_links
def record017_frame015_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0618.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0618.count (({ width := 9, code := 0x26f369acca633097cba5b2b954a6512793492472290c823f1789446210f86c1e0d058240a00ff7f3f1e8f3793c5e0ef753a5d0e773395c4e17037dbcdd6ab419ece66b318cc56230d84c05faf97ab5592c15aaa52a89409d4d2612c9448a31128742204fe7d3d9e0ec74391bcd0653116cb052279308c441e8f074361a8d06631180b45829108803e1e0e06c30150a04c24110803c1c0c058281204018080200 } : Fields).get c.val)
theorem record017_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record017) (record017.maps 15) (record017.inverseMaps 15) record017_frame015_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record017) (record017.maps 15) (record017.inverseMaps 15) record017_frame015_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record017) (record017.maps 15) (record017.inverseMaps 15) record017_frame015_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record017) (record017.maps 15)
      (record017.inverseMaps 15) record017_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame015_links_0000 (interval_append _ 64 128 142 record017_frame015_links_0064 record017_frame015_links_0128))
theorem record017_frame015_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 15 :=
  of_group record017 15 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0618
    Papers.RationalityTen.SharedFrameCatalogue.group0618_facts record017_frame015_indices record017_frame015_graph record017_frame015_links
def record017_frame016_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x288ce999b25a48c8d91721641c6f8d91963145a8af13625c4287d0d617be9782ef1dabb0756e1dc13796e6dadb335e6a8d2d9231f638c618b3115f8bdd792e95ccb796aad259cb1d62abd4d693d2424447c8e50aa0d40a7f4fa1ee3d4784ec9b435c6a0d119d32262cc217e2f25c4b51662c6574ab95129851ca01382644ac9211e22e440788e91c2334638b61642b44f89b0ee1cc360580ae1502984f09c11c2203c04e0981202303e0780d81502804c0901102003c0700c0160280480400600800800 } : Fields).get c.val)
theorem record017_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record017) (record017.maps 16) (record017.inverseMaps 16) record017_frame016_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record017) (record017.maps 16) (record017.inverseMaps 16) record017_frame016_indices (Fin.ofNat record017.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record017_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record017) (record017.maps 16) (record017.inverseMaps 16) record017_frame016_indices (Fin.ofNat record017.n i)) 128 142 :=
  interval_of_check _ 128 14 (by decide +kernel)
theorem record017_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record017) (record017.maps 16)
      (record017.inverseMaps 16) record017_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 142 record017_frame016_links_0000 (interval_append _ 64 128 142 record017_frame016_links_0064 record017_frame016_links_0128))
theorem record017_frame016_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 16 :=
  of_group record017 16 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record017_frame016_indices record017_frame016_graph record017_frame016_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (Fin.cases (record017_frame004_supported hcells) (Fin.cases (record017_frame005_supported hcells) (Fin.cases (record017_frame006_supported hcells) (Fin.cases (record017_frame007_supported hcells) (Fin.cases (record017_frame008_supported hcells) (Fin.cases (record017_frame009_supported hcells) (Fin.cases (record017_frame010_supported hcells) (Fin.cases (record017_frame011_supported hcells) (Fin.cases (record017_frame012_supported hcells) (Fin.cases (record017_frame013_supported hcells) (Fin.cases (record017_frame014_supported hcells) (Fin.cases (record017_frame015_supported hcells) (Fin.cases (record017_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x400dfc8fc07cbbc09dc4eb97483849bc8db46c3b561a50d0f66fb321822bdf5daae8168eadb566a97d4a4a3a511283937c9594a7239d1b28c3455a2610608193e99e54dba6ab34099b0c265a72cc94aca3c506277136891442520d0ecc74a38f1bb8d905f82e514f898445621d10b08043e61ec0ee075439c1a60cb85ec2ce13d09704481fc094049024412008e04681bc0dc06b03501800be05c02d815c0ac05502a00dc06c03301900a004e024011807c03c01d00e0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x34a1a36d0d67fb35d988cb16503195896c3760d30017dabdd5d7ae656b2b3558e2c515d6aa654fa97d4a4a3950fa8313b898e4c224b123c90347423490e28594019ec4ec67453979c98df26b23561980cb06433169870be45b12d69594aba54729a14989a44be23f11087c23c51de8e306d836219d8c9c62a2b814989204201b90cb8540242094049024412008e04681bc0dc06b03501800be05c02d815c0ac05502a00dc06c03301900a004e024011807c03c01d00e0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x75e75c75875373b73572e7287117016f26e66db6ce6c16a669a66e65a64764162b5f95f55cd5c85b95aa59d5825545515255215125034f64c94ba48a46443441f4104073f13bf3bb39338e37f36d36334831a3172eb2e72d82c62bd28f28025022a1fa1eb1e51d01bf1b91ad1a619e1701651491321101070ed0da09008e08d08c08a08906d06c06906805e05d05a05905505405305203703603303202802702402301f01e01d01c01401301201000f00e00a009008007004003002001000 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x3755b98dc16db354da94d3e699334d960c8e635311d84ac1a606301570ab765b4ad8d610ab45542951496a4351da8d13a897b4b7a45921a90547ea3d90e885c40e1f9ce7072a38e9c5cd8a66e3321834c0a5ff2fc17c8b465562a714049f44f427713a490446f220106873c37e1b78cf863c30f17e8bd85e027912d08803f41920bb051424c094049024412008e04681bc0dc06b03501800be05c02d815c0ac05502a00dc06c03301900a004e024011807c03c01d00e0050026012008003c01c00a004802000e0040018008002000 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7f6353141872c1d601afb96b2b3558e2c515d6aa6530277d36a9984c7a5dd2b2936496231d0e286742520c103680e3ee1f18eae7503a29ce8e5e7263769b80d8c6b234c99f0cc25e52ef1748b8e5bb2d9165cb1457b2b71594a2e50827513489804b224f124090445f2280ff87c23c51de8ea871836c1b10d5067632718a8c205702a514989744682220fd07803861b90d686583081740b184382020d706482900de06e02e81700b605702b013c09203901b80d8060026012809004602100f8078028013009004001e00e0050024010005002000c002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record019_frame001_links_0000 (interval_append _ 64 128 133 record019_frame001_links_0064 record019_frame001_links_0128))
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1872bee5a62d0d66ab2a58e2c515c0ad255caa99516a7453026d533098f4bca56526c92c46221c509483040da02cfb87c63ab9d40e8a73a3979c98dda6e03631ac8d3267c3309748b765b22d19628adc56528d934896449e24812188be4501f80f847a83c51de8e6c71837b1b60d886a033b1938c546082f41698ae052625911a08883f81e00e186e432c1840ba059422010106b832410e08103881bc0dc05d02e016c0ae056027812407203701b009404802300f807803601500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame001_links_0000 (interval_append _ 64 128 130 record020_frame001_links_0064 record020_frame001_links_0128))
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x25649b8df1b2344638bf1722744887d0ca15c1f826f95ed3d379af19de3b1732e15bdb756dcda9afb58646c858eb19628c3d7eaf95e4b956ead2586a4d43a7e4ea9bd3325d48c8c91522343a865072083ca76cea1cc3866d4d71a433864cc49832fc5e0ba16f2c053ca293324a470891081f23b4700d719c320588ad13825c3986f0c818c310550a814c2784e08e1041a0330640941202303e0780d81502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame002_links_0000 (interval_append _ 64 128 130 record020_frame002_links_0064 record020_frame002_links_0128))
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
def record020_frame003_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x298d1b9d739e724df9b135a61cbc95d2964dc8d90113a1fc3a8690a60ec167fef81ea3cc788f01d8baa6e6dc1b53656bed699fb3b65ac958cb0b5feb155c2b2550a7d4aa8e4ea9712a24c48c90d1b2304047e4f91e73c2748e59c33726c4d419e32a638c49842ea59cac9422664a88f91320a3f4768e31b63545b0b013825c4087c0dc1b43605d0b816c2b85609e1241c83706c0941202303e0780d81502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record020_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 3) (record020.inverseMaps 3) record020_frame003_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record020) (record020.maps 3)
      (record020.inverseMaps 3) record020_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame003_links_0000 (interval_append _ 64 128 130 record020_frame003_links_0064 record020_frame003_links_0128))
theorem record020_frame003_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 3 :=
  of_group record020 3 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record020_frame003_indices record020_frame003_graph record020_frame003_links
def record020_frame004_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b74d2b6012fd97bebcb5daae81676b2a5812b6d568a8c53126512dc95c4a1a4791f48e744520c101c7f73f29f6cf6a7a53671b08d5669734099b0c0e5f62e7169cb0055829711808744282078fa878c3b31ab0bf05b42c31588a9c50227111908ac44821d10b08204021fa0f987b03c61dc0ea873838e1c20da069832e1810b985b02be1520a204f425a12608f84641ec0f006d035410e08103881bc0dc05d02e016c0ae056027812407203701b009404802300f807803601500a004c024011008003c01c00c0050024010005002000c002000 } : Fields).get c.val)
theorem record020_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4) (record020.inverseMaps 4) record020_frame004_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record020) (record020.maps 4)
      (record020.inverseMaps 4) record020_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame004_links_0000 (interval_append _ 64 128 130 record020_frame004_links_0064 record020_frame004_links_0128))
theorem record020_frame004_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 4 :=
  of_group record020 4 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame004_indices record020_frame004_graph record020_frame004_links
def record020_frame005_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6f46cf66766365a65064764162261c6085f95eb5db5ce56c55a55554a53d52a5254f04c94b34a449749147946d42d42841f4194104073e83e13d03bf3b03a239433132231b3103012f22eb2b628f27926725c25723c2322011fa1f21eb1e51d91d01c81bf1b91b41ad1a619e19619017f17016514d14013712c1221161101060ff0f70f20d40d00b90b408307f06f06d06c05b05a05905505404d04903903703602502402301f01e01b01501401301201101000f00e00c00a009008005004003001000 } : Fields).get c.val)
theorem record020_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record020) (record020.maps 5) (record020.inverseMaps 5) record020_frame005_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record020) (record020.maps 5)
      (record020.inverseMaps 5) record020_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame005_links_0000 (interval_append _ 64 128 130 record020_frame005_links_0064 record020_frame005_links_0128))
theorem record020_frame005_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 5 :=
  of_group record020 5 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record020_frame005_indices record020_frame005_graph record020_frame005_links
def record020_frame006_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x2784d895729a4f49b92f252444848fb1da374658b509e0f418821005fa3eb792eb1d0b9c72ae41bf3766a4d2da3b42680ced9431e61ec0d7d2f15caab952a9f534a5147a884e094d22a3c4688b111a1c3f07b8f39e23ba73ce41c03746d0d61a5342674cc1923085d4b394f27c4d89391b21a4107a0ea1c43645b8b11442683c0740ce198328540a61482784e09010c1a8330640901182203e0780d81502804c0901102003c0700c0140240400500800c00800 } : Fields).get c.val)
theorem record020_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record020) (record020.maps 6) (record020.inverseMaps 6) record020_frame006_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record020) (record020.maps 6)
      (record020.inverseMaps 6) record020_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame006_links_0000 (interval_append _ 64 128 130 record020_frame006_links_0064 record020_frame006_links_0128))
theorem record020_frame006_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 6 :=
  of_group record020 6 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record020_frame006_indices record020_frame006_graph record020_frame006_links
def record020_frame007_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7c37957357317297237197166f66f36e96dd6d16c06a865063f63562b6196025f35bc58557556b56055953f5314eb4e14dd4d84d44cc4a549848246d45e44f43a3d83c93bd3b63ac3a539d37233b3263163093022ef2e52a729929128427b26625c24f24723c23122821f21620e2071f11dd1c81ab19618a17816415214712f12411810d0e30dc0c10b908207d06e06c06b05a05905805405304d04703803603502502402301f01e01b01501401301201101000f00e00c00a009008005004003001000 } : Fields).get c.val)
theorem record020_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record020_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7) (record020.inverseMaps 7) record020_frame007_indices (Fin.ofNat record020.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record020_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record020) (record020.maps 7)
      (record020.inverseMaps 7) record020_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record020_frame007_links_0000 (interval_append _ 64 128 130 record020_frame007_links_0064 record020_frame007_links_0128))
theorem record020_frame007_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 7 :=
  of_group record020 7 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record020_frame007_indices record020_frame007_graph record020_frame007_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (Fin.cases (record020_frame003_supported hcells) (Fin.cases (record020_frame004_supported hcells) (Fin.cases (record020_frame005_supported hcells) (Fin.cases (record020_frame006_supported hcells) (Fin.cases (record020_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record020_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083

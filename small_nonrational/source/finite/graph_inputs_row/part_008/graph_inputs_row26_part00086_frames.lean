module
prelude
public import GraphInputsRow26Part00086Data
public import RawFrameSupport
public import SharedFrameGroups006Checked
public import SharedFrameGroups008Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups012Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups015Checked
public import SharedFrameGroups016Checked
public import SharedFrameGroups017Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups024Checked
public import SharedFrameGroups025Checked
public import SharedFrameGroups029Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups061Checked
public import SharedFrameGroups062Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups077Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups087Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x697297d4729b649aa43d1d48cf45822750c8842418202cfb47b33d19e58a5650524110047b63b61cd8df06d23301870bf05ae2a613f89bc4c423910407e83d81dd0eb87403761ad0d3065830417c0b305802b21520a5851027a128090846021410307e03dc1b60d403d81ac0d406203081600ae05602180cc06402a014808003e01e00a805002200f007003401600a004801c00c005002000c004000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
def record000_frame002_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x5f7a97d4709d54b7252d25a914476a35d13c87b438a11d0147da3e21ec8cc06422f51668afc5662a994e4a564f926d934895e48522e91388864011cd8dec6c433c1948c5c5c62c215c0a484b424910787f43dc1e00e8870c3721860bb059028013008f84441b00c803d81ac0d406203081600ae05602180cc06402a014808003e01e00a805002200f007003401600a004801c00c005002000c004000 } : Fields).get c.val)
theorem record000_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2) (record000.inverseMaps 2) record000_frame002_indices (Fin.ofNat record000.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record000_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record000) (record000.maps 2)
      (record000.inverseMaps 2) record000_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record000_frame002_links_0000 record000_frame002_links_0064)
theorem record000_frame002_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 2 :=
  of_group record000 2 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record000_frame002_indices record000_frame002_graph record000_frame002_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (Fin.cases (record000_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xd576933461a14d055582a89288936470a34d1988c645e22dd1608aa451226512488d3939ad0d2267232e9748abe53c28e94209904c125d12cc95a4a624e925892248a24091f48ea46f2358c6460c29913d09ac4b023c116886841c1e40db065c3101750ac852826e12b08083e01e00e9071036c1a807003581a80c205c02d80e407003501980c80540290130090046014007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
def record001_frame002_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xc7c61030197e0beb52fa94925891e450a1f90e486a42220dd0448123fb9f64f867b43789a58cf266032897a8b2e57b2b29558a3850b27e13b49bc4d325f92b094a49723f91d08b844d2228d886a82e31610ae054a28113789604922100f0070c3721a80c305d82c6151090844c1fe0f2072835818e07003581a80c205c02d80e407003501980c80540290130090046014007803801600a004802000e005002000c004001 } : Fields).get c.val)
theorem record001_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2) (record001.inverseMaps 2) record001_frame002_indices (Fin.ofNat record001.n i)) 64 101 :=
  interval_of_check _ 64 37 (by decide +kernel)
theorem record001_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record001) (record001.maps 2)
      (record001.inverseMaps 2) record001_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 101 record001_frame002_links_0000 record001_frame002_links_0064)
theorem record001_frame002_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 2 :=
  of_group record001 2 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record001_frame002_indices record001_frame002_graph record001_frame002_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (Fin.cases (record001_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1ac0c8d63cb1958a0c3c57da8a1428a004f5a75d35e9624ae255529a94649fa4e126292a491a47122290a483a4011f28f2473a3811b277d34f9a30cf065f324978ca3050427993849a24c4259128091c47d236913487643821410608103e91ec8f246e82a914a8a104e426212a890c46221f10707f83bc1cc0e486e43521990bd05a82b41570a8052428413b09a04ac24811f08c044421610307e03d41e40ec07303801b40d404a024c11c08d04601c40e006b03501a4054029012008c04401500a003c01c00d } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86582281a81480f80875d6e46d26c66bc6af6755ec5dd5cd5bd5ab59959058858057857056255a55754e54653e53152a52247b3f23e33d33c33b136f2f62e42d82ce2c12b62ad2a529d29528d27f27727426b26325b24e24723f2201d81d01c91c31bd1b81b11a91a219a19118517e17a17216a16315815014914613f13713012811f11310c1081000f80f10e60de0d70d50d10cd0c90c50c109409308e08d08c07107006b06a06902a02902402302201501400f00e00d } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
def record002_frame003_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1106.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1106.count (({ width := 10, code := 0x79dcf731ca725c66d59d6699865d9461d6e5b16a599625815e5715a5615654d515414e5314a51d4550d314611645110431033ace8398e5388df374db364d7354d2340cf334cb324c6310c22e8a227c9d2709925894248902388c2248721884208801f47b1e4781d8741c8701b86b1a468198641885f1745b168591605715855104400ec3a0e42c0ac260942405c160441003c0801c0200400 } : Fields).get c.val)
theorem record002_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3) (record002.inverseMaps 3) record002_frame003_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1106.localPairCheck (smallEmbedding record002) (record002.maps 3)
      (record002.inverseMaps 3) record002_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame003_links_0000 record002_frame003_links_0064)
theorem record002_frame003_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 3 :=
  of_group record002 3 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1106
    Papers.RationalityTen.SharedFrameCatalogue.group1106_facts record002_frame003_indices record002_frame003_graph record002_frame003_links
def record002_frame004_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1104.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1104.count (({ width := 10, code := 0x856027fdfd7f1f97b5da75dd5751d171db36c1ae6a9a46859e66d98655926358a6258660d805ed795d96a559535454d51d3f4b12949d2648d204751a45d144450c42508415023fcfa3e0f53bcdc364d7358d3340cd328c7310c12f0b92e0b52c8af2a8a8294a42849e26c98254902348c2248620c7e1f0791e0771d8751d073190631785d170511404b128490a82909023088150500f0380d } : Fields).get c.val)
theorem record002_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4) (record002.inverseMaps 4) record002_frame004_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1104.localPairCheck (smallEmbedding record002) (record002.maps 4)
      (record002.inverseMaps 4) record002_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame004_links_0000 record002_frame004_links_0064)
theorem record002_frame004_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 4 :=
  of_group record002 4 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1104
    Papers.RationalityTen.SharedFrameCatalogue.group1104_facts record002_frame004_indices record002_frame004_graph record002_frame004_links
def record002_frame005_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1103.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1103.count (({ width := 10, code := 0x856027fdfd7f1f97b5da75dd5751d171db36c1ae6a9a46859e66d98655926358a6258660d805ed795d96a559535454d51d3f4b12949d2648d204751a45d144450c42508415023fcfa3e0f53bcdc364d7358d3340cd328c7310c12f0b92e0b52c8af2a8a8294a42849e26c98254902348c2248620c7e1f0791e0771d8751d073190631785d170511404b128490a82909023088150500f0380d } : Fields).get c.val)
theorem record002_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5) (record002.inverseMaps 5) record002_frame005_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1103.localPairCheck (smallEmbedding record002) (record002.maps 5)
      (record002.inverseMaps 5) record002_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame005_links_0000 record002_frame005_links_0064)
theorem record002_frame005_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 5 :=
  of_group record002 5 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1103
    Papers.RationalityTen.SharedFrameCatalogue.group1103_facts record002_frame005_indices record002_frame005_graph record002_frame005_links
def record002_frame006_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1102.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1102.count (({ width := 10, code := 0x8ea2287e1d87219821f07b5eb7a9e7769c16f9bc6e1b36c1ae6ada8695a26759a6659664d906318a621765755a5615453d454b52a4a1274912147d1c4651644d0e42d0a41d04404fd3ecf93c4d9358d434cd0334cb320c5308bf2e8b72d8b32c0ad2a4a7294a42889f27099258912388d22887210801f87c1ec7a1e4781dc76188611705b1684d13047118450a82909023088150500f0380d } : Fields).get c.val)
theorem record002_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6) (record002.inverseMaps 6) record002_frame006_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1102.localPairCheck (smallEmbedding record002) (record002.maps 6)
      (record002.inverseMaps 6) record002_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame006_links_0000 record002_frame006_links_0064)
theorem record002_frame006_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 6 :=
  of_group record002 6 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1102
    Papers.RationalityTen.SharedFrameCatalogue.group1102_facts record002_frame006_indices record002_frame006_graph record002_frame006_links
def record002_frame007_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabca4ea3ba2ea1fa0c97f9038f18e48d68c48967fe7ea7d97c67af79e79678677776875773472071a7066f46e26c16ad69a61c5a559458757856753e4bd4ab49d49048047747246545744943b41e40e40a3f93eb3dd3c03b03a03792e72d82cc2be2ac2a229b28b27a26c25f24323322d21d20e1ff1e31d31c61c31bc1b01a319418516e16015814813a12e1171060f90f70ec0e10d30c70b908e08d08808708606f06e06906806702a02902402302201501400f00e00d } : Fields).get c.val)
theorem record002_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 7) (record002.inverseMaps 7) record002_frame007_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record002) (record002.maps 7)
      (record002.inverseMaps 7) record002_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame007_links_0000 record002_frame007_links_0064)
theorem record002_frame007_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 7 :=
  of_group record002 7 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record002_frame007_indices record002_frame007_graph record002_frame007_links
def record002_frame008_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0649.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0649.count (({ width := 8, code := 0xfcf6f4f2f1f0efe9e7e5e4e3e2dcdad8d6d4d2d0cecccac8c5c3c2c0bebdbcbbbab9b3b1afadaba9a3a19f9e9d9c9a989694928f8d8c8a8887868584837d7b797877767472706e6c696766646261605f5e5d5b59575553504e4d4b494847464544434241403f3e3d3a39383736333231201f1c1b1a13120f0e0d } : Fields).get c.val)
theorem record002_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0649.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record002) (record002.maps 8) (record002.inverseMaps 8) record002_frame008_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0649.localPairCheck (smallEmbedding record002) (record002.maps 8)
      (record002.inverseMaps 8) record002_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame008_links_0000 record002_frame008_links_0064)
theorem record002_frame008_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 8 :=
  of_group record002 8 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0649
    Papers.RationalityTen.SharedFrameCatalogue.group0649_facts record002_frame008_indices record002_frame008_graph record002_frame008_links
def record002_frame009_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18e8bed5ef2f1d762b9b571a97d498a36510a8393ba92f492a4311e48dc464a2dd14a89444121d10ae84141e209d0227fb3eb1f00f506fa3319970c9663631297a8aca5572a214d8a5051f28693f89de4e026a12f09524a724c92288ee45a22590e88023621a88cf06523171850be45d02d81638ae854228c14309d04c224e11788744102000f8878c3a81c60dd06983261890bc85a42a813d096847023210907c83b01be0cf04a024c11c08d04601c40e006b03501a4054029012008c04401500a003c01c00d } : Fields).get c.val)
theorem record002_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 9) (record002.inverseMaps 9) record002_frame009_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record002) (record002.maps 9)
      (record002.inverseMaps 9) record002_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame009_links_0000 record002_frame009_links_0064)
theorem record002_frame009_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 9 :=
  of_group record002 9 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record002_frame009_indices record002_frame009_graph record002_frame009_links
def record002_frame010_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6d368067666b6616525fb5a859e59358657a56152051b51450c5034fb4f54ee4e84e14dc4d24cb4c84c04b84b14a549d4974403df3d83cd3c03b338a32b32331930e3042fe2f32ec2e42de2d62c72b72b62ad2a229828427826b24c1ed1e51db1cf1c51c01b41ae1a71a019818917917716d16415a14313a12d12a12311c11610f10b1030fc0f80f20ec0e60dd0d60d00ce0c80c20bd0b80b108808708208108006f06e06906806702a02902402302201501400f00e00d } : Fields).get c.val)
theorem record002_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 10) (record002.inverseMaps 10) record002_frame010_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record002) (record002.maps 10)
      (record002.inverseMaps 10) record002_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame010_links_0000 record002_frame010_links_0064)
theorem record002_frame010_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 10 :=
  of_group record002 10 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record002_frame010_indices record002_frame010_graph record002_frame010_links
def record002_frame011_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0999.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0999.count (({ width := 8, code := 0x87868584838281807f7e7d7c7b7a7877767574737271706f6d6c6b6a6968676665646361605f5e5d5c5b5a5958575655545352504f4e4d4c4b4a494847464544434241403f3e3d3c3a393837363534333231302f2e2d2c2a292827262524232221201f1e1d1c181716151411100f0e0d0a090807060403020100 } : Fields).get c.val)
theorem record002_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0999.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0999.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0999.localPairCheck (smallEmbedding record002) (record002.maps 11) (record002.inverseMaps 11) record002_frame011_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0999.localPairCheck (smallEmbedding record002) (record002.maps 11)
      (record002.inverseMaps 11) record002_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame011_links_0000 record002_frame011_links_0064)
theorem record002_frame011_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 11 :=
  of_group record002 11 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0999
    Papers.RationalityTen.SharedFrameCatalogue.group0999_facts record002_frame011_indices record002_frame011_graph record002_frame011_links
def record002_frame012_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0997.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0997.count (({ width := 8, code := 0xd9d1d0cfceccc9c1c0bfbebcb9b2b1b0aeacaba9a8a7a6a5a4a2a19f9d9c9a9997948d8c8b8987867e7d7c7b79777574737271706e6d6b6968666563625a595857555351504f4e4d4c4a4947454442413f3e3c3b3a393837353432302f2d2c2a29282726252422211d1c1b1918141312100f0b0a090706020100 } : Fields).get c.val)
theorem record002_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 12) (record002.inverseMaps 12) record002_frame012_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0997.localPairCheck (smallEmbedding record002) (record002.maps 12)
      (record002.inverseMaps 12) record002_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame012_links_0000 record002_frame012_links_0064)
theorem record002_frame012_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 12 :=
  of_group record002 12 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0997
    Papers.RationalityTen.SharedFrameCatalogue.group0997_facts record002_frame012_indices record002_frame012_graph record002_frame012_links
def record002_frame013_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0996.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0996.count (({ width := 8, code := 0xd9d1d0cfceccc9c1c0bfbebcb9b2b1b0aeacaba9a8a7a6a5a4a2a19f9d9c9a9997948d8c8b8987867e7d7c7b79777574737271706e6d6b6968666563625a595857555351504f4e4d4c4a4947454442413f3e3c3b3a393837353432302f2d2c2a29282726252422211d1c1b1918141312100f0b0a090706020100 } : Fields).get c.val)
theorem record002_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0996.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record002) (record002.maps 13) (record002.inverseMaps 13) record002_frame013_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0996.localPairCheck (smallEmbedding record002) (record002.maps 13)
      (record002.inverseMaps 13) record002_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame013_links_0000 record002_frame013_links_0064)
theorem record002_frame013_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 13 :=
  of_group record002 13 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0996
    Papers.RationalityTen.SharedFrameCatalogue.group0996_facts record002_frame013_indices record002_frame013_graph record002_frame013_links
def record002_frame014_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0552.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0552.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0552.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0552.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0552.localPairCheck (smallEmbedding record002) (record002.maps 14) (record002.inverseMaps 14) record002_frame014_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0552.localPairCheck (smallEmbedding record002) (record002.maps 14)
      (record002.inverseMaps 14) record002_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame014_links_0000 record002_frame014_links_0064)
theorem record002_frame014_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 14 :=
  of_group record002 14 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0552
    Papers.RationalityTen.SharedFrameCatalogue.group0552_facts record002_frame014_indices record002_frame014_graph record002_frame014_links
def record002_frame015_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x21d0b84c1e0b0380bfdfcfd7e3edf4f87b3d1e4f0773add0e57137db2d56a349a0ce64b1584c15f2ed72b75aacd64b1582bd5cad5529d48a14f2652c9549a451e8b44215088341205007f3f1f0f4783b1d0e26f371b0d4683298cc2602f170b4582b150a65228138984a2491c8c43200f47436190c4602f170b4582b150a434190c05c2c110803c1c0d } : Fields).get c.val)
theorem record002_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record002) (record002.maps 15) (record002.inverseMaps 15) record002_frame015_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record002) (record002.maps 15)
      (record002.inverseMaps 15) record002_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame015_links_0000 record002_frame015_links_0064)
theorem record002_frame015_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 15 :=
  of_group record002 15 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record002_frame015_indices record002_frame015_graph record002_frame015_links
def record002_frame016_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x8521183e0d82e097e9ee7b5ec7a5e678dd2739ca719c26fdbc6e1b46c1ac699a26859f6759b6559062d7c5ad6758d5f56d545294751143509414f93a4d9324b9274892147d1d46d164490d3e8dc364d7354d3344cd324c5304be2ecb82d8b32bcac298a12709b260942408c220821f47a1dc751c86e1ac6519060170581504f1204711845110400fc3c0ec3a090230801f078110400f0380d } : Fields).get c.val)
theorem record002_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record002) (record002.maps 16) (record002.inverseMaps 16) record002_frame016_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record002) (record002.maps 16)
      (record002.inverseMaps 16) record002_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame016_links_0000 record002_frame016_links_0064)
theorem record002_frame016_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 16 :=
  of_group record002 16 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record002_frame016_indices record002_frame016_graph record002_frame016_links
def record002_frame017_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0251.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0251.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0251.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0251.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0251.localPairCheck (smallEmbedding record002) (record002.maps 17) (record002.inverseMaps 17) record002_frame017_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0251.localPairCheck (smallEmbedding record002) (record002.maps 17)
      (record002.inverseMaps 17) record002_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame017_links_0000 record002_frame017_links_0064)
theorem record002_frame017_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 17 :=
  of_group record002 17 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0251
    Papers.RationalityTen.SharedFrameCatalogue.group0251_facts record002_frame017_indices record002_frame017_graph record002_frame017_links
def record002_frame018_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0250.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0250.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0250.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0250.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0250.localPairCheck (smallEmbedding record002) (record002.maps 18) (record002.inverseMaps 18) record002_frame018_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0250.localPairCheck (smallEmbedding record002) (record002.maps 18)
      (record002.inverseMaps 18) record002_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame018_links_0000 record002_frame018_links_0064)
theorem record002_frame018_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 18 :=
  of_group record002 18 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0250
    Papers.RationalityTen.SharedFrameCatalogue.group0250_facts record002_frame018_indices record002_frame018_graph record002_frame018_links
def record002_frame019_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0248.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0248.count (({ width := 8, code := 0x797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record002_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0248.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (smallEmbedding record002) (record002.maps 19) (record002.inverseMaps 19) record002_frame019_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0248.localPairCheck (smallEmbedding record002) (record002.maps 19)
      (record002.inverseMaps 19) record002_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame019_links_0000 record002_frame019_links_0064)
theorem record002_frame019_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 19 :=
  of_group record002 19 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0248
    Papers.RationalityTen.SharedFrameCatalogue.group0248_facts record002_frame019_indices record002_frame019_graph record002_frame019_links
def record002_frame020_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0227.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0227.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0227.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0227.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0227.localPairCheck (smallEmbedding record002) (record002.maps 20) (record002.inverseMaps 20) record002_frame020_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0227.localPairCheck (smallEmbedding record002) (record002.maps 20)
      (record002.inverseMaps 20) record002_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame020_links_0000 record002_frame020_links_0064)
theorem record002_frame020_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 20 :=
  of_group record002 20 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0227
    Papers.RationalityTen.SharedFrameCatalogue.group0227_facts record002_frame020_indices record002_frame020_graph record002_frame020_links
def record002_frame021_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0124.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0124.count (({ width := 7, code := 0x3cf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record002_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0124.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0124.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0124.localPairCheck (smallEmbedding record002) (record002.maps 21) (record002.inverseMaps 21) record002_frame021_indices (Fin.ofNat record002.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record002_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0124.localPairCheck (smallEmbedding record002) (record002.maps 21)
      (record002.inverseMaps 21) record002_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record002_frame021_links_0000 record002_frame021_links_0064)
theorem record002_frame021_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 21 :=
  of_group record002 21 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0124
    Papers.RationalityTen.SharedFrameCatalogue.group0124_facts record002_frame021_indices record002_frame021_graph record002_frame021_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (Fin.cases (record002_frame003_supported hcells) (Fin.cases (record002_frame004_supported hcells) (Fin.cases (record002_frame005_supported hcells) (Fin.cases (record002_frame006_supported hcells) (Fin.cases (record002_frame007_supported hcells) (Fin.cases (record002_frame008_supported hcells) (Fin.cases (record002_frame009_supported hcells) (Fin.cases (record002_frame010_supported hcells) (Fin.cases (record002_frame011_supported hcells) (Fin.cases (record002_frame012_supported hcells) (Fin.cases (record002_frame013_supported hcells) (Fin.cases (record002_frame014_supported hcells) (Fin.cases (record002_frame015_supported hcells) (Fin.cases (record002_frame016_supported hcells) (Fin.cases (record002_frame017_supported hcells) (Fin.cases (record002_frame018_supported hcells) (Fin.cases (record002_frame019_supported hcells) (Fin.cases (record002_frame020_supported hcells) (Fin.cases (record002_frame021_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x6abb429a08cfd67ab3b9704ab0550aa3542c94449aa4851de8e8470a3691a68cc463a3011528a244ca24911c7273391978c966393141748a3a50927b13909a64c826092e89664ad253127492c491245120c8fa47523791a480c3191828bc45722a914c8a284f426b12b892043a20e0f0875838c1b60d3865c3101740b284e82560fe07b83c01d20e206e03500d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
def record003_frame002_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabfa55a46a39a28a149819038f68e98957f77e47d379c7937837727637537467326f06de6c36b06aa61959d58c57f57056253e4bd4ab49d4904804764704634554474394204104073f83e93db3c23b33a337a2e72da2ce2a029628627526725a2452352091fa1ca1c21ba1ae1a019118316f16113712b0fb0f10e60d90cc0c20b206906805a05903903803303203102a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record003_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2) (record003.inverseMaps 2) record003_frame002_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record003) (record003.maps 2)
      (record003.inverseMaps 2) record003_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame002_links_0000 record003_frame002_links_0064)
theorem record003_frame002_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 2 :=
  of_group record003 2 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record003_frame002_indices record003_frame002_graph record003_frame002_links
def record003_frame003_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x68066065c65865264b6035ab5a259756450c5064fb4d64d14cc4c64c14bc4b84b249d49748f48948542a3d43c93bc3b23a538733132631e30f3022fa2f52f12ec2e62e12d72d12ce2c72c22bd2b62b22ad28a2132091fc1db1d51cc1c41b91b11a019617c17315214b14613e13412c1211121080ed0e50c20bb0b70b20ab0a509e06806705a05903803703203103002a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record003_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3) (record003.inverseMaps 3) record003_frame003_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record003) (record003.maps 3)
      (record003.inverseMaps 3) record003_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame003_links_0000 record003_frame003_links_0064)
theorem record003_frame003_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 3 :=
  of_group record003 3 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record003_frame003_indices record003_frame003_graph record003_frame003_links
def record003_frame004_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x63e2fc17d2bd35dd2e915d2a5f528a8ed3b692c48ea41518a8b3450a2410fc87243621550187f73ec9f0cf766f13301948c8062f30f17a8aca5572a214d8a5051c28593f09da4de26992fc9584a524b921c8e845c22690f48083621a98cf860c2f41718b4c5842b81520a404b624910687f43dc1e00e8870c3721a70ca05982a211e08783fc1e40e506c831c0d606a02e016c07203801980c806202a0148090046022007803801800b005002400e0060028010006001 } : Fields).get c.val)
theorem record003_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 4) (record003.inverseMaps 4) record003_frame004_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record003) (record003.maps 4)
      (record003.inverseMaps 4) record003_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame004_links_0000 record003_frame004_links_0064)
theorem record003_frame004_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 4 :=
  of_group record003 4 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record003_frame004_indices record003_frame004_graph record003_frame004_links
def record003_frame005_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7ad77276e7677607596da67166965861f5b65ae59d57c57556e56756055b55755053953252852151e47b40f4023f13e63db3ae34233532431930e3073002f92f22eb2e62de2d72d22cb2c52be2b52af2aa2802041f61eb1cb1c31bc1b51ae1a819d19317c17015514b14313c13512e12811d1130fc0f00d50ce0c90c30c00be0b706b06a05c05b03903803303203102a02902402302200f00e00c00b00a009007006005004003001 } : Fields).get c.val)
theorem record003_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 5) (record003.inverseMaps 5) record003_frame005_indices (Fin.ofNat record003.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record003_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record003) (record003.maps 5)
      (record003.inverseMaps 5) record003_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record003_frame005_links_0000 record003_frame005_links_0064)
theorem record003_frame005_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 5 :=
  of_group record003 5 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record003_frame005_indices record003_frame005_graph record003_frame005_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (Fin.cases (record003_frame002_supported hcells) (Fin.cases (record003_frame003_supported hcells) (Fin.cases (record003_frame004_supported hcells) (Fin.cases (record003_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabea5197f9068d98c68947f77e17d079b79078076f7607507377236c66b36a36195a057356453f4bd4ad49f47546d4604524444364214113c53b63aa3792e72d82cc2be2ac2a029628627526725a22821a1e71d91cb1c21ba1ae1a019118317116313712b0fd0bf0b406f06e05a05905705605505403903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
def record004_frame002_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18f4bee571a981448a114ec24b123490246122c113c88d43da1c50b68453ee1f18f666f133098c8c425ed2b29564a8c51928413e49d44db269130095a45f22811108023621a88cf06523171830bd05c62d31610ae050226f11a088841c1fd0f707803a21c30dc86a432c1660a884801ae0c903881c00b805b02c81600ae05601c80e0048023010808003e01e00a805001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record004_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2) (record004.inverseMaps 2) record004_frame002_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record004) (record004.maps 2)
      (record004.inverseMaps 2) record004_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame002_links_0000 record004_frame002_links_0064)
theorem record004_frame002_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 2 :=
  of_group record004 2 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record004_frame002_indices record004_frame002_graph record004_frame002_links
def record004_frame003_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0253.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0253.count (({ width := 9, code := 0x2a952a2d02793a9b4c25f2d94496451f8e46a31158742e12fe7cbd5e6ef74ba1cce16f36db0d569b459cc7623095c9b4ca612e964a2451c8b4421906823d9e0ea74391bcd86933188be5a2c9508e441e0ec6833188c05e2e1409c401f0e870361a088401e0e06830160a048200c050200c0200 } : Fields).get c.val)
theorem record004_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record004) (record004.maps 3) (record004.inverseMaps 3) record004_frame003_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0253.localPairCheck (smallEmbedding record004) (record004.maps 3)
      (record004.inverseMaps 3) record004_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame003_links_0000 record004_frame003_links_0064)
theorem record004_frame003_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 3 :=
  of_group record004 3 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0253
    Papers.RationalityTen.SharedFrameCatalogue.group0253_facts record004_frame003_indices record004_frame003_graph record004_frame003_links
def record004_frame004_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c5ad2b59fa98944ea134dca39d1aa8c244421d90c885242120c10368093da9e94f2e60b29713cc9be4851d98e8471c3541a10cc063c30e17e0b9c5aa281138898c4721ec0f207743ae1d00e487083761b40d6869832218a0b985b02ca1600ac854829614409e84d025a11a08983f41b40d503881c00b805b02c81600ae05601c80e0048023010808003e01e00a805001e00e006803001600a004802000c005002000c002000 } : Fields).get c.val)
theorem record004_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 4) (record004.inverseMaps 4) record004_frame004_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record004) (record004.maps 4)
      (record004.inverseMaps 4) record004_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame004_links_0000 record004_frame004_links_0064)
theorem record004_frame004_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 4 :=
  of_group record004 4 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame004_indices record004_frame004_graph record004_frame004_links
def record004_frame005_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x6d066c5d057955a54f52c4cb4c04b249548f48347846c46545544640e4053fd3973403213162f329228627b25c25324a23d23522c21a20d1d51cc1c41ac17116b16516115d15715414f14914313d12d12911611110e10c10a1051000fb0f60ee0e80da0d40c40ab0a906a06905505405205105004f03903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record004_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 5) (record004.inverseMaps 5) record004_frame005_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record004) (record004.maps 5)
      (record004.inverseMaps 5) record004_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame005_links_0000 record004_frame005_links_0064)
theorem record004_frame005_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 5 :=
  of_group record004 5 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record004_frame005_indices record004_frame005_graph record004_frame005_links
def record004_frame006_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x7186cf6255ce5af5a258052551d5114ee4e84df4d94ce4c94bc4ae47946d4663eb3943723683462eb2e32d72b42ad2a229d29428f28227423c23222c2091b91b51ae1a81a019819018817f17717015f15714013713012d12812211c11611010b1060f30ee0d90b90b406f06e05a05905705605505403903802402302102001f01e01501400f00e00d00c00b00a009008006005004003001000 } : Fields).get c.val)
theorem record004_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6) (record004.inverseMaps 6) record004_frame006_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record004) (record004.maps 6)
      (record004.inverseMaps 6) record004_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame006_links_0000 record004_frame006_links_0064)
theorem record004_frame006_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 6 :=
  of_group record004 6 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record004_frame006_indices record004_frame006_graph record004_frame006_links
def record004_frame007_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0252.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0252.count (({ width := 10, code := 0x856127e9ef7a9e7789d0735c96f5b96d5b16b5aa6a1a465d926397a5a95e56955529485153f4ed374cd2f4b12949118451103e8dc364d7354d3340cc320c4300bd2d4b22a0a32749a25c9323c8b21c831f8741c4661484d1003f0d8350cc320c4300a8290801f0741c06c1a0441003c0e0340c02c0a02408018050100300400 } : Fields).get c.val)
theorem record004_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record004) (record004.maps 7) (record004.inverseMaps 7) record004_frame007_indices (Fin.ofNat record004.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record004_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0252.localPairCheck (smallEmbedding record004) (record004.maps 7)
      (record004.inverseMaps 7) record004_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record004_frame007_links_0000 record004_frame007_links_0064)
theorem record004_frame007_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) : Supported record004 7 :=
  of_group record004 7 (smallEmbedding record004) (small_cells_exact record004 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0252
    Papers.RationalityTen.SharedFrameCatalogue.group0252_facts record004_frame007_indices record004_frame007_graph record004_frame007_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSmall.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (Fin.cases (record004_frame002_supported hcells) (Fin.cases (record004_frame003_supported hcells) (Fin.cases (record004_frame004_supported hcells) (Fin.cases (record004_frame005_supported hcells) (Fin.cases (record004_frame006_supported hcells) (Fin.cases (record004_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
def record005_frame001_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xabda519809068937f77df7ce7bf7a879b79078076f7607507397256c66b361a5a053e4bd4ab49d49048047546d4604524444364234133c53b63792e72d82cc2be2ac2a029628627526725a2472371e71d91c21ba1ae1a019118315614613712b0c00b406005f05a05905805705605505402a02902402302202102001f01e01501400f00e00d00c00b00a009006005004003002001000 } : Fields).get c.val)
theorem record005_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 1) (record005.inverseMaps 1) record005_frame001_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record005) (record005.maps 1)
      (record005.inverseMaps 1) record005_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame001_links_0000 record005_frame001_links_0064)
theorem record005_frame001_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 1 :=
  of_group record005 1 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record005_frame001_indices record005_frame001_graph record005_frame001_links
def record005_frame002_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x63bafb95cca604eaa4b123090047523511848b044f22350f687142ea11cfb87c637a1984bd45652ab9510a6c52828c94209f24ea26d93489844af22f91408023621a88cf06523171830bd05c62d31610ae054c29211a08883fa1ee0f007443861b90c305d82cc15106c03240c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2) (record005.inverseMaps 2) record005_frame002_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record005) (record005.maps 2)
      (record005.inverseMaps 2) record005_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame002_links_0000 record005_frame002_links_0064)
theorem record005_frame002_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 2 :=
  of_group record005 2 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record005_frame002_indices record005_frame002_graph record005_frame002_links
def record005_frame003_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x6b1b2415fca2b4d725852b29524a6251527c93749824a524491b489242d1d08e13bc1a64bc651828213cc9c24d125f12b093448823b919c8a64411f78f7c6e82a914a8a104e426212788f445621910407e03c81d20c005c02ac14f0a4050427413308f045c22010a06b83440c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 3) (record005.inverseMaps 3) record005_frame003_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record005) (record005.maps 3)
      (record005.inverseMaps 3) record005_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame003_links_0000 record005_frame003_links_0064)
theorem record005_frame003_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 3 :=
  of_group record005 3 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record005_frame003_indices record005_frame003_graph record005_frame003_links
def record005_frame004_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x6d46815fc5a956051e51851150a5014fa4f34ec4e64df4da4d34cc4a749f43f3dd38a32b32331930e3042f92f12e92e22da2d42ca2bd28727c24c1ed1e51db1cf1c51bb1b21aa1a519d19618c17f14713d12912211b11510e1090f70f10eb0e50b50ae06005f05a05905805705605505402a02902402302202102001f01e01501400f00e00d00c00b00a009006005004003002001000 } : Fields).get c.val)
theorem record005_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 4) (record005.inverseMaps 4) record005_frame004_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (smallEmbedding record005) (record005.maps 4)
      (record005.inverseMaps 4) record005_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame004_links_0000 record005_frame004_links_0064)
theorem record005_frame004_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 4 :=
  of_group record005 4 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record005_frame004_indices record005_frame004_graph record005_frame004_links
def record005_frame005_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x715b4ad684a624db239d1a68c0456a269110876432214908483040ea02cf6a7a530714b89043b31cf8e306f23661aa0d0866031e1870bf05d22d714089c44721ec0f207743ae1d00e487083761b40d6869833a1960b985b02c01590a9052c28813d094048423411306d83540c406102e016c0b405902c015c0ac02a0148090046022010808003e01e00a805001e00e006803001600a004801800a0040018008002000 } : Fields).get c.val)
theorem record005_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5) (record005.inverseMaps 5) record005_frame005_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record005) (record005.maps 5)
      (record005.inverseMaps 5) record005_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame005_links_0000 record005_frame005_links_0064)
theorem record005_frame005_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 5 :=
  of_group record005 5 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record005_frame005_indices record005_frame005_graph record005_frame005_links
def record005_frame006_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x728d697babd51a9b1342654c69812ea5a4ae95128a4e4929191ba343e26dcc39662c457cae95a2ae550a894e296520a19402624b88f0fd1f23d87a0f11dc3ac740e51c437c6d0d7190314608c017e2f85e8bc1722e05b8b615c2b43005f0b41642c0570ac1542a02a052090118220420800f81e02a0500780e01a0300580a0120180280400600800800 } : Fields).get c.val)
theorem record005_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 6) (record005.inverseMaps 6) record005_frame006_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (smallEmbedding record005) (record005.maps 6)
      (record005.inverseMaps 6) record005_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame006_links_0000 record005_frame006_links_0064)
theorem record005_frame006_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 6 :=
  of_group record005 6 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record005_frame006_indices record005_frame006_graph record005_frame006_links
def record005_frame007_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1004.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1004.count (({ width := 9, code := 0x9dcc24316853f5f6f87bbd1e2ef773b5d8eb74399b6d969b2178af56aa952a651a85409f4f275349846a2d107b3c9d8ea72379b4d86b351a4cc642c95ca85329144a04f2612c94492210c7238198c86230178b85a251207c3c1d0e06c34190a8501e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record005_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 7) (record005.inverseMaps 7) record005_frame007_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1004.localPairCheck (smallEmbedding record005) (record005.maps 7)
      (record005.inverseMaps 7) record005_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame007_links_0000 record005_frame007_links_0064)
theorem record005_frame007_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 7 :=
  of_group record005 7 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1004
    Papers.RationalityTen.SharedFrameCatalogue.group1004_facts record005_frame007_indices record005_frame007_graph record005_frame007_links
def record005_frame008_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1002.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1002.count (({ width := 8, code := 0xd5d1c8c4bbb5b3b1b0afaeacabaaa9a8a7a59e9d9a968d8785838281807e7d7c7b7a7977706f6c66646261605f5d5c5b5a5958564f4e4b4a49484746434241403e3d33322f2e2d2c2b2a2921201d1c1b1a19181713120f0e0d0c0b0a0906050403020100 } : Fields).get c.val)
theorem record005_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 8) (record005.inverseMaps 8) record005_frame008_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1002.localPairCheck (smallEmbedding record005) (record005.maps 8)
      (record005.inverseMaps 8) record005_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame008_links_0000 record005_frame008_links_0064)
theorem record005_frame008_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 8 :=
  of_group record005 8 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1002
    Papers.RationalityTen.SharedFrameCatalogue.group1002_facts record005_frame008_indices record005_frame008_graph record005_frame008_links
def record005_frame009_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0259.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0259.count (({ width := 9, code := 0x87c3205007cbddeaf378bbdd8e97338dc0dd6db5d96c7602f566b258ac15eae55aa14aa24fa71369846a29088341205007f3e9ecf2773a9cce47033190be5d2d964ae552893c9a4b1c0d0502713094482311084401a0c8602e160a8502612088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record005_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record005) (record005.maps 9) (record005.inverseMaps 9) record005_frame009_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0259.localPairCheck (smallEmbedding record005) (record005.maps 9)
      (record005.inverseMaps 9) record005_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame009_links_0000 record005_frame009_links_0064)
theorem record005_frame009_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 9 :=
  of_group record005 9 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0259
    Papers.RationalityTen.SharedFrameCatalogue.group0259_facts record005_frame009_indices record005_frame009_graph record005_frame009_links
def record005_frame010_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0153.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0153.count (({ width := 9, code := 0x85c21fcfc7abcde2ef76badd0e57137db8d96bb4d8ec35eae960af572b558ab54295449f4e26530954521d0481401fcfc7d3d9e4ee75399c4e06e32188bc5c2d160ac5428138984a1c0d0502713094482311084401a0c8602e160a8502612088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record005_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record005) (record005.maps 10) (record005.inverseMaps 10) record005_frame010_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0153.localPairCheck (smallEmbedding record005) (record005.maps 10)
      (record005.inverseMaps 10) record005_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame010_links_0000 record005_frame010_links_0064)
theorem record005_frame010_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 10 :=
  of_group record005 10 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0153
    Papers.RationalityTen.SharedFrameCatalogue.group0153_facts record005_frame010_indices record005_frame010_graph record005_frame010_links
def record005_frame011_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0257.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0257.count (({ width := 9, code := 0x773b1cce46eb6db2d76ab4da2cf66b2d92c762b096eb4582b546a250a813e9e4e26930964a249228f42a0d007f3f1f4f87b3c9dcea73389bcdc6c31180b85a2c158a8522713094481d0dc582b150a4502713094481c0d86832180b8582a14088401e0e06830160a048180a04018080200 } : Fields).get c.val)
theorem record005_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record005) (record005.maps 11) (record005.inverseMaps 11) record005_frame011_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0257.localPairCheck (smallEmbedding record005) (record005.maps 11)
      (record005.inverseMaps 11) record005_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame011_links_0000 record005_frame011_links_0064)
theorem record005_frame011_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 11 :=
  of_group record005 11 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0257
    Papers.RationalityTen.SharedFrameCatalogue.group0257_facts record005_frame011_indices record005_frame011_graph record005_frame011_links
def record005_frame012_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0151.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0151.count (({ width := 8, code := 0x8887868583817f7d7b79777573716f6d6b69676564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a49484746454443413f3d3b393733312f2d242221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record005) (record005.maps 12) (record005.inverseMaps 12) record005_frame012_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0151.localPairCheck (smallEmbedding record005) (record005.maps 12)
      (record005.inverseMaps 12) record005_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame012_links_0000 record005_frame012_links_0064)
theorem record005_frame012_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 12 :=
  of_group record005 12 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0151
    Papers.RationalityTen.SharedFrameCatalogue.group0151_facts record005_frame012_indices record005_frame012_graph record005_frame012_links
def record005_frame013_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0255.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0255.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record005_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0255.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record005) (record005.maps 13) (record005.inverseMaps 13) record005_frame013_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0255.localPairCheck (smallEmbedding record005) (record005.maps 13)
      (record005.inverseMaps 13) record005_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame013_links_0000 record005_frame013_links_0064)
theorem record005_frame013_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 13 :=
  of_group record005 13 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0255
    Papers.RationalityTen.SharedFrameCatalogue.group0255_facts record005_frame013_indices record005_frame013_graph record005_frame013_links
def record005_frame014_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0256.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0256.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record005_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0256.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record005) (record005.maps 14) (record005.inverseMaps 14) record005_frame014_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0256.localPairCheck (smallEmbedding record005) (record005.maps 14)
      (record005.inverseMaps 14) record005_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame014_links_0000 record005_frame014_links_0064)
theorem record005_frame014_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 14 :=
  of_group record005 14 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0256
    Papers.RationalityTen.SharedFrameCatalogue.group0256_facts record005_frame014_indices record005_frame014_graph record005_frame014_links
def record005_frame015_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0150.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0150.count (({ width := 8, code := 0x636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record005_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0150.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (smallEmbedding record005) (record005.maps 15) (record005.inverseMaps 15) record005_frame015_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0150.localPairCheck (smallEmbedding record005) (record005.maps 15)
      (record005.inverseMaps 15) record005_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame015_links_0000 record005_frame015_links_0064)
theorem record005_frame015_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 15 :=
  of_group record005 15 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0150
    Papers.RationalityTen.SharedFrameCatalogue.group0150_facts record005_frame015_indices record005_frame015_graph record005_frame015_links
def record005_frame016_indices (c : Fin record005.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0254.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0254.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record005_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0254.graphBitCheck record005.data.requiredEdges q = true := by decide +kernel
theorem record005_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0254.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record005_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0254.localPairCheck (smallEmbedding record005) (record005.maps 16) (record005.inverseMaps 16) record005_frame016_indices (Fin.ofNat record005.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record005_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0254.localPairCheck (smallEmbedding record005) (record005.maps 16)
      (record005.inverseMaps 16) record005_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record005_frame016_links_0000 record005_frame016_links_0064)
theorem record005_frame016_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) : Supported record005 16 :=
  of_group record005 16 (smallEmbedding record005) (small_cells_exact record005 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0254
    Papers.RationalityTen.SharedFrameCatalogue.group0254_facts record005_frame016_indices record005_frame016_graph record005_frame016_links
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (Fin.cases (record005_frame001_supported hcells) (Fin.cases (record005_frame002_supported hcells) (Fin.cases (record005_frame003_supported hcells) (Fin.cases (record005_frame004_supported hcells) (Fin.cases (record005_frame005_supported hcells) (Fin.cases (record005_frame006_supported hcells) (Fin.cases (record005_frame007_supported hcells) (Fin.cases (record005_frame008_supported hcells) (Fin.cases (record005_frame009_supported hcells) (Fin.cases (record005_frame010_supported hcells) (Fin.cases (record005_frame011_supported hcells) (Fin.cases (record005_frame012_supported hcells) (Fin.cases (record005_frame013_supported hcells) (Fin.cases (record005_frame014_supported hcells) (Fin.cases (record005_frame015_supported hcells) (Fin.cases (record005_frame016_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x18f8bf0571a97d3aa92c462a2cd14289043f21c90b484441ba0890187f73ec9f0cf686f133017a8aca51c28593f09da4de26992fc9584a524b921c8e845c22691148023621830bd05c62d31610ae050226f12d89244201fd0f707803a21c30dc86182ec1660a8848421e0ff07903941ac0c703881c00d606a03101840b805b01c80e006603201500a404802300a805001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
def record006_frame002_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1aaed0a5be2ac1420944477a3a11c28da469a3311868bc45ba2c11528a244ca24911a7273391748a3a4c826092e89664ad253127492c491245120c8fa47523791ac80631915c8aa453228a13d09ac47822d10e88383c81d60e306d834e1970c4056429413a09584041ee0f007483881b60d403881c00d606a03101840b805b01c80e006603201500a404802300a805001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record006_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 2) (record006.inverseMaps 2) record006_frame002_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record006) (record006.maps 2)
      (record006.inverseMaps 2) record006_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame002_links_0000 record006_frame002_links_0064)
theorem record006_frame002_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 2 :=
  of_group record006 2 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame002_indices record006_frame002_graph record006_frame002_links
def record006_frame003_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1c60d3159fa97d36c8e7445a1e50ce855422a0cd0348083ff1fb0fb87cb3d91e88f3060b29592087663571a28ccc64231117f8b985a82ca15c0aa052e27e13709904721ec0e487083761b40d6869832218a0c185f02ce1600ac854829614409e84a024211a08983f81ea0ee07383801b20d303881c00d606a03101840b805b01c80e006603201500a404802300a805001e00e006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record006_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 3) (record006.inverseMaps 3) record006_frame003_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record006) (record006.maps 3)
      (record006.inverseMaps 3) record006_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame003_links_0000 record006_frame003_links_0064)
theorem record006_frame003_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 3 :=
  of_group record006 3 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record006_frame003_indices record006_frame003_graph record006_frame003_links
def record006_frame004_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x71a6d16255cd57d5254f14ea4e24db4d14ca4bb4ad4aa49d49248847646a4673eb3933432eb2b72af2a529f29729028127326d26225824e23922f22d2091b919819018817f17717015f15714f14a13212d12812211c1161101010f90f30ee0da0d30ce0c70bf0b80b206f06e06906806005f05a05903903803303202a02902402301501400f00e00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record006_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record006) (record006.maps 4) (record006.inverseMaps 4) record006_frame004_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record006) (record006.maps 4)
      (record006.inverseMaps 4) record006_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame004_links_0000 record006_frame004_links_0064)
theorem record006_frame004_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 4 :=
  of_group record006 4 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record006_frame004_indices record006_frame004_graph record006_frame004_links
def record006_frame005_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x86682375d6e466e5e659858f58757f57756f56555d55654d54553d53352b5264743ec36f2f62b52ac2a429c29428c28227a27326a26225a2502482432201d81b71b01a81a119919017917116916214c14513e13612f12711e1070ff0f70f00da0d40d00cc0c80c40c007107006b06a06206105c05b03903803303202a02902402301501400f00e00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record006_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 5) (record006.inverseMaps 5) record006_frame005_indices (Fin.ofNat record006.n i)) 64 102 :=
  interval_of_check _ 64 38 (by decide +kernel)
theorem record006_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record006) (record006.maps 5)
      (record006.inverseMaps 5) record006_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 102 record006_frame005_links_0000 record006_frame005_links_0064)
theorem record006_frame005_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 5 :=
  of_group record006 5 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record006_frame005_indices record006_frame005_graph record006_frame005_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (Fin.cases (record006_frame002_supported hcells) (Fin.cases (record006_frame003_supported hcells) (Fin.cases (record006_frame004_supported hcells) (Fin.cases (record006_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x696b499a3ed18688b4299fecfc67ab3b962ab03578ab79594ab654b2a3d4fca6c4d4a65d30a9724af252925492348924011de8e8470a3691a68cc461a2f916e8b0455a29113a8964479a8cd0267232c9930c726282a714b0a3a50427b93909a64ba2569298940498248922890847b23a91bc8d235a1978c7061c2f316e8b2853227a135895849823c11688884141fc0f7078036c1970c405cc2d21590a504fc24e11908583f41f20f007483881b60d505902780e206201a00cc064031012809004602200580280120080028010006002 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
def record007_frame002_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0xaf15d2b7569acb586ab553a9d52268ccd98f30a5f4ba95f2b253ca18c91762ac4f89310e1cc3585b09a0fc1882102a023fe7e8fc1f43e17b8f61ea3d0798d4da4b44678ce198b2a592af95daae552a894da834ec9c53625e4a892921a384668b9141c93786dcd91a4334640bb16b2d056cab14f29050c9c13325c4a08a9092043e87a8ee1ce38c6c8d219c320628bb1682c0550a7132224340590680cc1903104a090118220160280480800a01001802 } : Fields).get c.val)
theorem record007_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2) (record007.inverseMaps 2) record007_frame002_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record007) (record007.maps 2)
      (record007.inverseMaps 2) record007_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame002_links_0000 record007_frame002_links_0064)
theorem record007_frame002_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 2 :=
  of_group record007 2 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record007_frame002_indices record007_frame002_graph record007_frame002_links
def record007_frame003_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0xbd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record007_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3) (record007.inverseMaps 3) record007_frame003_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record007) (record007.maps 3)
      (record007.inverseMaps 3) record007_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame003_links_0000 record007_frame003_links_0064)
theorem record007_frame003_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 3 :=
  of_group record007 3 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record007_frame003_indices record007_frame003_graph record007_frame003_links
def record007_frame004_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0xb1d86bd5bacd5ea551a7d3287419f4ee7337994c65f2c93492431e8e46a2b148943e190a83c1205007dbe9f0f5793c5e0ef77399c8e37037dbcdc6b351a6d067b3998c660af978b95b2cd60ae562ad54a24ea6930954923d12874320d04813f9f8f87a3c9e0e872389b8da6c351a4ce653218cc4602f174b85b2b9448c3b1309448230f074381b058281208028100602 } : Fields).get c.val)
theorem record007_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4) (record007.inverseMaps 4) record007_frame004_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record007) (record007.maps 4)
      (record007.inverseMaps 4) record007_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame004_links_0000 record007_frame004_links_0064)
theorem record007_frame004_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 4 :=
  of_group record007 4 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record007_frame004_indices record007_frame004_graph record007_frame004_links
def record007_frame005_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1086.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1086.count (({ width := 9, code := 0xd6eaf51a5d1e87399bcce5b0d84c0dfaf97abadd2e56fb3592c35eae56aab54a953e994aa3d1285409dcea7135994c6612f97476371a8bc5a291180bf5f6f87abc9dee77137dbad96ab459ccc6532590bb5b2cd62ad54a9534964a2451c8b44219088240a00f6793c1d4e872379b4d6693419ccc6431184c05f2d14c903c1309448230f074381b058281208028100602 } : Fields).get c.val)
theorem record007_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5) (record007.inverseMaps 5) record007_frame005_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1086.localPairCheck (smallEmbedding record007) (record007.maps 5)
      (record007.inverseMaps 5) record007_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame005_links_0000 record007_frame005_links_0064)
theorem record007_frame005_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 5 :=
  of_group record007 5 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1086
    Papers.RationalityTen.SharedFrameCatalogue.group1086_facts record007_frame005_indices record007_frame005_graph record007_frame005_links
def record007_frame006_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1083.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1083.count (({ width := 9, code := 0xbd5e2ed74b95c6dd6db5da6ad54a95429d4da55268f459dce66f3599cca5f2e964aa51269248a411f8e46e33178ac52271288bf1f0f77a3cde0ed6fb6db4d76b34da0c962b0d84be5dae16cb358ac15ca04e26932954923d128542205007d3d1e0ea73391c0d6673318cc45f2e168ae552a148a24e2612c9248200d858230c05c2c150803c1c0d0401c0c05018080200 } : Fields).get c.val)
theorem record007_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6) (record007.inverseMaps 6) record007_frame006_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1083.localPairCheck (smallEmbedding record007) (record007.maps 6)
      (record007.inverseMaps 6) record007_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame006_links_0000 record007_frame006_links_0064)
theorem record007_frame006_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 6 :=
  of_group record007 6 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1083
    Papers.RationalityTen.SharedFrameCatalogue.group1083_facts record007_frame006_indices record007_frame006_graph record007_frame006_links
def record007_frame007_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x6183081828c065fd2fc17aebd05dd2e9153ca8d54129d94d6a61522a8f544ca134c125c12bc94d49da4b9222907477a36518a8b3450a2410fc87242d213106e82240a9ffcfd47d43df1a14cd06603269904c5e61e2c515b8aca5522a294d8a504fc26f134c99c4b4252925c91846c22e113487a38e1b70d8c6b63401960c685c62c215c0a8c528281137898848a23211008303c01c30dc86943301860bb05ac29a13e097047422a0ff07903941ac0ca05602780e206201a00cc064031012809004602200580280120080028010006002 } : Fields).get c.val)
theorem record007_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7) (record007.inverseMaps 7) record007_frame007_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record007) (record007.maps 7)
      (record007.inverseMaps 7) record007_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame007_links_0000 record007_frame007_links_0064)
theorem record007_frame007_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 7 :=
  of_group record007 7 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record007_frame007_indices record007_frame007_graph record007_frame007_links
def record007_frame008_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x9b335a684c99893025bcb495f29e24c458810f61bc3084f0920e4177c8f79eb3d079af1ddf3ba76aeb5d2b9f738e5dc7b886fededbab6f6ced8db035a6a6b856a2cf590b115f2b94ec9ad3425e4b09552723d45e8a912a17422825009f63e47b0f319f326634c417a2e65a8ab9502985089e1362664bc9211d234450820f81e43b0748e31ba364688cd190310600b81662c0558a712c21c3585e0640c41802f04808c110210160280480800a01001802 } : Fields).get c.val)
theorem record007_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8) (record007.inverseMaps 8) record007_frame008_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record007) (record007.maps 8)
      (record007.inverseMaps 8) record007_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame008_links_0000 record007_frame008_links_0064)
theorem record007_frame008_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 8 :=
  of_group record007 8 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record007_frame008_indices record007_frame008_graph record007_frame008_links
def record007_frame009_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xd5351d3b4bd2345ceb37ccb2dbd2f1bbaebba2e5b72dab5ad2ac2acaa2a4a829ca3e8ba127d9e6779d2729be6c9825d9564d91a3f8ea358c5fa7d9f47b5ea795e0701bc6e9af6b1a6681986519263d805e5725b1635815d565314a927491184490c400fb3e4ee3ace6384dc34ccf32cc82f4b62cca92949f2649421c821f4781dc6e1ac681805e16c5a130430ac2a0a428088210801f02c0a024080140400c02 } : Fields).get c.val)
theorem record007_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record007) (record007.maps 9) (record007.inverseMaps 9) record007_frame009_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record007) (record007.maps 9)
      (record007.inverseMaps 9) record007_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame009_links_0000 record007_frame009_links_0064)
theorem record007_frame009_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 9 :=
  of_group record007 9 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record007_frame009_indices record007_frame009_graph record007_frame009_links
def record007_frame010_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0749.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0749.count (({ width := 8, code := 0xa3a2a1a09f9e9c9b9a9998979695949391908f8e8d8c8b8a8988868584838281807f7e7d7b7a79787776757473706e6d6b6a6968656362605f5e5d5a585756545352514f4e4d4c494746454342413e3c3b3938373635333231302d2b2a28272625242221201f1e1c1b1a1918171615141211100f0d0c0b0a0807060503020100 } : Fields).get c.val)
theorem record007_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0749.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record007) (record007.maps 10) (record007.inverseMaps 10) record007_frame010_indices (Fin.ofNat record007.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record007_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record007) (record007.maps 10)
      (record007.inverseMaps 10) record007_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record007_frame010_links_0000 record007_frame010_links_0064)
theorem record007_frame010_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 10 :=
  of_group record007 10 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0749
    Papers.RationalityTen.SharedFrameCatalogue.group0749_facts record007_frame010_indices record007_frame010_graph record007_frame010_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (Fin.cases (record007_frame002_supported hcells) (Fin.cases (record007_frame003_supported hcells) (Fin.cases (record007_frame004_supported hcells) (Fin.cases (record007_frame005_supported hcells) (Fin.cases (record007_frame006_supported hcells) (Fin.cases (record007_frame007_supported hcells) (Fin.cases (record007_frame008_supported hcells) (Fin.cases (record007_frame009_supported hcells) (Fin.cases (record007_frame010_supported hcells) (fun j => Fin.elim0 j))))))))))))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5772b1d566aa754629ed4d29824ada51d276920487a3f51c08d2465a30917a8b64579b1cd6e6a634a1a10cea65a32798f0c565722b11544a7e52f29014149f44e726b131c9804b925912b094a49724812246ae32c18c8c045e02da1638a644f426b12c093047822d10f88303fc1f00f106d832e1880ba85a42b214a09e04a423610d07f83d812805802b81580aa04301c80a804202000f807803a010007803801a00b0050024010005002000c004000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9c19a399496f9609518c68b48a989b88987985f84e83a8277f77d47c07ab79678176e6135fe5f35d75cb5bc54353352851f5115044ec4e44d64c749b48247746845944a43d36b35834d34133131f2fa2ea2d82ad2932862742652552462232132011f01e21d51cd1c41b51a818717816b15514313312311310407b06205805705605504302a02001f01e01d01501101000f00e00d00b00a009008006005004003002000 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
def record009_frame002_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xa7f5342981474a24508a5fd2dc95c4a5a4e525a91448223b51ae89e43da1c50bc84941a207cd1066b3309910c646212d49668b1a57e2b89598aa654829c94ac9f24db269130c9624a224a0eb473638c1bd8db06c433d1948c5c5c62c215c0a9c528281137891c46822210707f43dc1e00e8870c3721980c305d82c814f0a004c023e11103d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record009_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2) (record009.inverseMaps 2) record009_frame002_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record009) (record009.maps 2)
      (record009.inverseMaps 2) record009_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame002_links_0000 record009_frame002_links_0064)
theorem record009_frame002_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 2 :=
  of_group record009 2 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record009_frame002_indices record009_frame002_graph record009_frame002_links
def record009_frame003_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x2edb9ee4b66d5b46afaaea7a8e9fa6e90a2a839f2739ba6b98a5c9524c7edf77d5eb799e1715c3705bf6f5bb6c1ad69da165d93645875fd785c5384d1304b529499174450b400fb3e4f23ace6384d4340cc324c5304bd2e8b62cca527c9923c8820c7e1e474140430e4380dc360d0270741c06c1a054110400f0380d02c0a02408018050100300800 } : Fields).get c.val)
theorem record009_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3) (record009.inverseMaps 3) record009_frame003_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record009) (record009.maps 3)
      (record009.inverseMaps 3) record009_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame003_links_0000 record009_frame003_links_0064)
theorem record009_frame003_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 3 :=
  of_group record009 3 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record009_frame003_indices record009_frame003_graph record009_frame003_links
def record009_frame004_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xaa053ba989476a27509a52526a921487a3f51d48cf46222c113a86442120c103c80d3fd9fa4ad8543297141c9e64df20a90047da3db1e48ed87363901be0da466030e17e0ba85b22c715a883c4102010fd07cc3d81de0eb87403761ad0d306783301910c505e82e616c0b285802b21520a5851027a12f0940484230111085040c1f80f703d81880b005702b015408602a010007c03c01d00a804402000f007003401600a004802000c005002000c004000 } : Fields).get c.val)
theorem record009_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 4) (record009.inverseMaps 4) record009_frame004_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record009) (record009.maps 4)
      (record009.inverseMaps 4) record009_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame004_links_0000 record009_frame004_links_0064)
theorem record009_frame004_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 4 :=
  of_group record009 4 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record009_frame004_indices record009_frame004_graph record009_frame004_links
def record009_frame005_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x5e45d35ce5ba5af5a255054754053452d5265175135084fb4df4ce4c94bf4b24a749a3a839b39438037236831630b3042fc2f52ec2dd2d92cb2c22a229428f28527826a25f1e11d91d01c81bf1b91af1a81a018817717016b16615f15714814013713012d12812211c1161101081010f90f10ec0e60df0d80d507906005605505405304302a02001f01e01d01501101000f00e00d00b00a009008006005004003002000 } : Fields).get c.val)
theorem record009_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 5) (record009.inverseMaps 5) record009_frame005_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record009) (record009.maps 5)
      (record009.inverseMaps 5) record009_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame005_links_0000 record009_frame005_links_0064)
theorem record009_frame005_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 5 :=
  of_group record009 5 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record009_frame005_indices record009_frame005_graph record009_frame005_links
def record009_frame006_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0x1168a44e1f0d85bf9f8fa7c3d9e8ee763a5cce27037db8da6c3596eb55a2c15cac4fa7536994ba551e8d4521d0681401f4f6793b9a4ce6532188c25e2e970ae5429944a04f27130964a249208c4421904803d1e0ec72381b8d86a34170b04a2411888421f0c05c2c15088401e0e0683014090401c0c050200c0400 } : Fields).get c.val)
theorem record009_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record009) (record009.maps 6) (record009.inverseMaps 6) record009_frame006_indices (Fin.ofNat record009.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record009_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record009) (record009.maps 6)
      (record009.inverseMaps 6) record009_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record009_frame006_links_0000 record009_frame006_links_0064)
theorem record009_frame006_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 6 :=
  of_group record009 6 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record009_frame006_indices record009_frame006_graph record009_frame006_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (Fin.cases (record009_frame002_supported hcells) (Fin.cases (record009_frame003_supported hcells) (Fin.cases (record009_frame004_supported hcells) (Fin.cases (record009_frame005_supported hcells) (Fin.cases (record009_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb22b0baffaf4adbaccabc9c29a59969729639548aa88c87c85183d82a8138037f87ed7d77c37a879978477074f7387217096125fb5f05e15d45c85b952750e5014f04e14d34c44b64a749c49348547a46445c44d44042e41840a3f93eb34e3343222fd2ed2db2c72b72ad2a12932862652552462212111ff1ee1e21d51cd1c41b51a818717816b1411311211111020f50e80da0cb0c007106203903403303203102a02502402302201500c00b00a009008006005004003002 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x30517f4bf05f4af41774ba454129ad4c2a3d513284d2bc93b497241d1de8d9462a2cd14289043f21c90b484c41ba088ffe7ea3ea1ef8d0a6683301948c8262f30f1628adc5652ab9514a6c52828e142c9f84ed26f134c97e4b4252925c90e46c22e113487a38e1b70d8c68032c18d0c185e82e31698b0857029414089bc48a23211008303fa1ee0f007443861b90cc06182ec14d09f04b823a10f07f83c81ca0d606501c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0x34ed2345d0337ccb2dbbae8b96dab5ad2aa2a0a728ba127d9e6779d2729be6c9825d9564d8fe3a8d6317e9f67d1ef7a9e5781c06f1ba6c9ac699a06719a661966519260d805e5725a9635815d565314a927461124310640d003f8fb3e4eb398e134ccf32cc8314c12f4ba2d8b32949f264872087d1e0721b86b1a0601784c10c300ac2a0a42809c220842007c150300b02809020060140400c02 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0725.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0725.count (({ width := 9, code := 0x5a6cf65b1d82bb5aa551a873f9ecee632d95492431e8e46a31168a44a1d0c84c1a04ff7e3e5bedc6d365acd36831584c05faf172b659ac55ead55aa54aa450271309549a451c8541200fa7a3b9d0e672389c0de6d359a4c86230178ba5c2d968b2582a94ca24b2491c8a4321104803e1e8e46a271188842200f86c34190c048180b050241006028100602 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0725.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0725
    Papers.RationalityTen.SharedFrameCatalogue.group0725_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
def record010_frame005_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x347da22d0a68233f19eacee578ab2956ca8f53f29b130a95e4a5248d224900477a3a11c28da469a3311868be45ba2c114889d44b223cd466813391978c986393141538a5851d28493dc9c84d326413049744b3256929893a498248922890647b23a91bc8d235a1978c705e62dd1650ae455229914509e84d624c11e08b44141fc0f707803ac1c60db069c32e1880b4856429412708c842c1fa0f707803a41c40db06a81c40c403901a00cc0640310150094048023011005401800b00500240100060028010006002 } : Fields).get c.val)
theorem record010_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 5) (record010.inverseMaps 5) record010_frame005_indices (Fin.ofNat record010.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record010_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record010) (record010.maps 5)
      (record010.inverseMaps 5) record010_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record010_frame005_links_0000 record010_frame005_links_0064)
theorem record010_frame005_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 5 :=
  of_group record010 5 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame005_indices record010_frame005_graph record010_frame005_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (Fin.cases (record010_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a0393f93792e9239169098f88eb8dc8bc84783c82f82180e7fc7e67d57c47a079c79378377276375373e72a7166fb6f66e46d26bf6ab5da5d45cb5c25b45a359258557655a4fc4f44e94df4d14c34b24a44954784764704634554474394284184073f03ec3de3d03bf3af2a029628627526725a2492392281c21ba1ae1a01911831731651560f10e60d90cc0be09f09506c05d03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
def record011_frame002_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb33b29b22b19b0baffaf1adbaccaab9da9cb9c29b89a59969889729639468c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476976374f73872170962d61f61460e6005f55e75d85cc5b25455355295225135064f74e54d74bc4b64a749c49348547a46c45c44d4384344234154073f62c72b72ad2a12932862752652551e21d51cd1c41b51a81981871781020f50e80da0cb0a809906e05f03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record011_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2) (record011.inverseMaps 2) record011_frame002_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record011) (record011.maps 2)
      (record011.inverseMaps 2) record011_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame002_links_0000 record011_frame002_links_0064)
theorem record011_frame002_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 2 :=
  of_group record011 2 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record011_frame002_indices record011_frame002_graph record011_frame002_links
def record011_frame003_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xe5792e3f8ce2786e0b7edeb72cfb3bce335ccb2fcaf26c8718beaf6bcaeeba6e4b76d4b2ebeaeeb7aceafaaea7a8a9ba528ca22819ea739be3e8ee388d6328be2b8961f859ff7f1f97d9f27b9e977dd5719c5709bf6edb76cdae69da065d94635865fd7b491214791a4591243908408df36cd734ccf32cc72fcb721c821f4781c46a1a05011c3309c120300b02809020060140400c02 } : Fields).get c.val)
theorem record011_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3) (record011.inverseMaps 3) record011_frame003_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record011) (record011.maps 3)
      (record011.inverseMaps 3) record011_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame003_links_0000 record011_frame003_links_0064)
theorem record011_frame003_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 3 :=
  of_group record011 3 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record011_frame003_indices record011_frame003_graph record011_frame003_links
def record011_frame004_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x5f6af6d788bb45d22e45700b705aead2d4a0a3d51228514089f34f227513869b249aa47920a8f147023311748a944aa20d0f0860424a0d50468124009fbcfbc7d13e69edcf407883bb1928c6a6203081804be25e32ea1710b665412969460a0e4f9276137099c4c125812a092c48423a119c8b444c21f90c884a42320910047dc3e21588a7451427813689804a424711d075838c1b50d406703201850bc85b420e0f907483781a80ab04d81b80be036013804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record011_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4) (record011.inverseMaps 4) record011_frame004_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record011) (record011.maps 4)
      (record011.inverseMaps 4) record011_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame004_links_0000 record011_frame004_links_0064)
theorem record011_frame004_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 4 :=
  of_group record011 4 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record011_frame004_indices record011_frame004_graph record011_frame004_links
def record011_frame005_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xb4967acd597b19612c157caeb5a29151ba2b44283cfd9f53d276cdf93f24a444818ed1ae32c5e8ab11a1ec2f84f0820a409806fedf9be57c6f65e53bb75ad59a7347684cf19932d650c8d8a2e45aeb2d63abf56cac955aa6532a55452814f69cd342634b495d2524947c8c91321b332638c31802f85d0b71682ca49c8d91321e41c808fd1ec3c85b8ad1482784c0870fa1802983404e0480600b0140240400600a01001802 } : Fields).get c.val)
theorem record011_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 5) (record011.inverseMaps 5) record011_frame005_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record011) (record011.maps 5)
      (record011.inverseMaps 5) record011_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame005_links_0000 record011_frame005_links_0064)
theorem record011_frame005_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 5 :=
  of_group record011 5 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record011_frame005_indices record011_frame005_graph record011_frame005_links
def record011_frame006_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0xd86bb59aad469b49a2d066f1789c3e170781bfdf6f776b95bed969b2d86bb59aad36994aa451a87409ecea6f3298cba572893456250f864260d03803f5eef3783b5d4e671379b4d667b3998ca6431584bf5e2e568b357aad4ea43f1f4f87b3c9dcea7338990c6623097cba5b2c95c8842200f878391c0d4682811044160a048200e06028100602 } : Fields).get c.val)
theorem record011_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 6) (record011.inverseMaps 6) record011_frame006_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record011) (record011.maps 6)
      (record011.inverseMaps 6) record011_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame006_links_0000 record011_frame006_links_0064)
theorem record011_frame006_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 6 :=
  of_group record011 6 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record011_frame006_indices record011_frame006_graph record011_frame006_links
def record011_frame007_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x696b499a3ed18688b429a06cfc67ab3a962ab03578ab79594ab6551aa3d4fca5e4d4a65d30a9724af252926e92348923c91de8e8470a3691a68cc462a2f916e8ae455a29113a8964479b28d746a934b9a1ccf066532918fcc405752b29550a8453229194409fa4ea26593209824ba25992b494c49f24c124491048523f91e48e646d15c8aa453228a13d09ac4b624c11e075838c1b60d3865c3101780b485641ee0f007483881b60af04d81b80be036013804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record011_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 7) (record011.inverseMaps 7) record011_frame007_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record011) (record011.maps 7)
      (record011.inverseMaps 7) record011_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame007_links_0000 record011_frame007_links_0064)
theorem record011_frame007_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 7 :=
  of_group record011 7 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame007_indices record011_frame007_graph record011_frame007_links
def record011_frame008_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6d2b641af2d616a4b4c5a32d026753305596ab7551aa3d4f4a65529a8f9454a084a624e124891248023b51b48c7459a249116879433a15508a8334112040ffc7e43f09f44f827af3cf165cb0656f2ad9518a6251f28513d89a84182020fc07bc3cc1dc8e9872637f1af0d5c68a3331908c445fe2ee16e0b285602ad14e8a344f626a0e487083761b40d6869833e1980c885802b21520a5851027a13609784a01ea0ee07383801b20af04d81b80be036013804801800b00500240100060028010006002 } : Fields).get c.val)
theorem record011_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 8) (record011.inverseMaps 8) record011_frame008_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record011) (record011.maps 8)
      (record011.inverseMaps 8) record011_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame008_links_0000 record011_frame008_links_0064)
theorem record011_frame008_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 8 :=
  of_group record011 8 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame008_indices record011_frame008_graph record011_frame008_links
def record011_frame009_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x84083a83482f82a82381c81681080571d71470a6fd6f36e86d96cd6c26a762561c6116035f75ea5d85ca5bc59d59858f58757f57756f56755f55654b54854053853052942b4224174093fd3f03de3d03c23a332f32631c30f3052fa2eb2df2d42b92b52ac2a429c29428c28427c27326826525d25524d2461b71b01a81a119919018818117914513e13612f12711e11610f1070d40d00cc0c80c40a909b06e05f03602701200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record011_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 9) (record011.inverseMaps 9) record011_frame009_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record011) (record011.maps 9)
      (record011.inverseMaps 9) record011_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame009_links_0000 record011_frame009_links_0064)
theorem record011_frame009_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 9 :=
  of_group record011 9 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record011_frame009_indices record011_frame009_graph record011_frame009_links
def record011_frame010_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x93d2724d49692523a45c858fd1d618c2a84f0860d41381d019ff3f179af29e0bbb768eb5d439e72ce19c137d6f2dc5b5b656c0d6daa34e696d119eb3565eb896dad559eb1d612bc566aa14d2794ee9c1352624ba95d272474748dd1922e44c87d0da1541e82501a003f27c4f51e42e05a8b295f2b0544a6147280444861062003e0790ed1ce3845a0ae14e28c4f88f10e18c2b03404e0480600b0140240400600a01001802 } : Fields).get c.val)
theorem record011_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record011) (record011.maps 10) (record011.inverseMaps 10) record011_frame010_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record011) (record011.maps 10)
      (record011.inverseMaps 10) record011_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame010_links_0000 record011_frame010_links_0064)
theorem record011_frame010_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 10 :=
  of_group record011 10 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record011_frame010_indices record011_frame010_graph record011_frame010_links
def record011_frame011_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0376.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0376.count (({ width := 9, code := 0x8f476391b8d46631178b456230f86c2e130782c09fefa7b3d1e4f0773b1d4e77237dbcdc6d361acd4693419ccb653218cc461afd7abb5cadd6ab3582b550a4512813c9c4d2612a9246a3114884321104803f1f0f2783b1d0e4713017cbc5d2e16cb4582b1289248239188a44211006833190c4602f170a8501f0e848180b050241006028100602 } : Fields).get c.val)
theorem record011_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record011) (record011.maps 11) (record011.inverseMaps 11) record011_frame011_indices (Fin.ofNat record011.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record011_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record011) (record011.maps 11)
      (record011.inverseMaps 11) record011_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record011_frame011_links_0000 record011_frame011_links_0064)
theorem record011_frame011_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 11 :=
  of_group record011 11 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0376
    Papers.RationalityTen.SharedFrameCatalogue.group0376_facts record011_frame011_indices record011_frame011_graph record011_frame011_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (Fin.cases (record011_frame002_supported hcells) (Fin.cases (record011_frame003_supported hcells) (Fin.cases (record011_frame004_supported hcells) (Fin.cases (record011_frame005_supported hcells) (Fin.cases (record011_frame006_supported hcells) (Fin.cases (record011_frame007_supported hcells) (Fin.cases (record011_frame008_supported hcells) (Fin.cases (record011_frame009_supported hcells) (Fin.cases (record011_frame010_supported hcells) (Fin.cases (record011_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x84783c82f82180e7fc7e67d57c47a079c79378377276375373e72a7166fb5d95d25c95bf5b15a059058357355d4fa4ef4e44da4cc4bd4ac49e4904764704634554474394284184073f032e3233163082f82ea2dc2d02c12a72a029628627526725a2492392281c21ba1ae1a01911831731651561331271181070fa0f10e60d90cc0be09506c05d04003602702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x8c88b68aa89e88c87c86a85183d81c8138037f87ed7d77c37af79978476962b61d61360b5fe5f35e55d75cb5b454053052751c50e5014f14e14d34b64a749c49348547a46c45c44d43836e35b34e34433432230f2fd2ed2d32c72b72ad2a12932862752652551e21d51cd1c41b51a81981871781531411311211111020f50e80da0cb09906e05f04003602702602502402302201200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0x2fabdaf2bbae9b92ddb52cbafabbadeb3abeaba9ea2a6e94a323d8ea378d2318ba2a8921e85dfd7e9f77cdef7ade576dd1715c26fdbb6ddb36b9a768197561555494f52d4750d3b4cd27491214791a4591243908408df36cd734ccf32cc72fcb72989f2609322c872087d1e0711a05011c370cc270982509023088120300b02809020060140400c02 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x127924863d1b8c456250f8441e0b0380bfdfafb7cbdde6dc6d361acd4693419ccc643017cbc5d2e16cb4592c158aa5429948a250279389843a1506813f9f4f6793b9cce471381bcdc6d361a8d05a2c960ae562a950a450259248e452190882401f8f876351a0984a1f0f074381b0d044160a048200e06028100602 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x49f92522240c768d71962f45588d0f617c2784105204c037f6fcdf2b5569ad19a033b662cad93b2262ab7d692c9586af159aae550a8d4aa8a5029ed39a684c69692ba4a3c675ce61c83846e4da9af356680cc98e30c600be1742dc5a0b292723644c879072023f47b0f21c6364678c81802dc568a413c2603e8600a60f01a02704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x4648bb15627c498870f21ac2d84907e0c410815011ff3f77e0fa1efb5e6b2d51a7b4a68acfd9cb32652b61682c9586af95dab3552a894928b5069ed3b2714d29792a2463b0744e49c13786dcd79a4334630c297d2ec5c0b59682c0558a7923238454879092043f07a8ee1c0364690ce1903085d8b41602a8430650ac0fc1b02704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x45989f1222143c86d0c21441e82903a043fe7f0fc5f6be67baf5de533d66eccd97329648c7d8cb13618afd5bab455aaa95129b52ca353f2754de9993025a4a091d1fa2d3846e8da1ab34c67cca98c3045c8b59672c6570ab1542945049f11021240c7f8f91e83b8740e11a6338640c417a2d8580ab14e280410690ba1001b02704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame007_links_0000 record012_frame007_links_0064)
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
def record012_frame008_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0373.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0373.count (({ width := 9, code := 0xdf6eb6db2d76ab4da2cf6632d92c762b0d82bf5eaed70ad55aa54ea551a853e9d4d26530974b2552893492451e8d45a250e8541a04fe7c389bcda6b3499cca6330978ba5c2d968b2582b958aa492411c8c452210c84411f8f87a3c1d8e872381b8d8642f1708c441c0d86832180b844160a048200e06028100602 } : Fields).get c.val)
theorem record012_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record012) (record012.maps 8) (record012.inverseMaps 8) record012_frame008_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record012) (record012.maps 8)
      (record012.inverseMaps 8) record012_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame008_links_0000 record012_frame008_links_0064)
theorem record012_frame008_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 8 :=
  of_group record012 8 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0373
    Papers.RationalityTen.SharedFrameCatalogue.group0373_facts record012_frame008_indices record012_frame008_graph record012_frame008_links
def record012_frame009_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x3b5760ea1d139a726e25c1b7d6e4dbdb53626b4d51a7348680ce5962bc572ad958aac54ca854e2965209752ca534a0931242404768d116a2844486909a0c40c7fcfc1ed33c664c998b3085f4bb16f2d0578ad9572a2528a293e2784e09a10f2144187f8f91e43ac728de1a4334630c217a2dc590ab14c288420670b00f81b02704c094120230440480600b0140240400600a01001802 } : Fields).get c.val)
theorem record012_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record012) (record012.maps 9) (record012.inverseMaps 9) record012_frame009_indices (Fin.ofNat record012.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record012_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (smallEmbedding record012) (record012.maps 9)
      (record012.inverseMaps 9) record012_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record012_frame009_links_0000 record012_frame009_links_0064)
theorem record012_frame009_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 9 :=
  of_group record012 9 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record012_frame009_indices record012_frame009_graph record012_frame009_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (Fin.cases (record012_frame002_supported hcells) (Fin.cases (record012_frame003_supported hcells) (Fin.cases (record012_frame004_supported hcells) (Fin.cases (record012_frame005_supported hcells) (Fin.cases (record012_frame006_supported hcells) (Fin.cases (record012_frame007_supported hcells) (Fin.cases (record012_frame008_supported hcells) (Fin.cases (record012_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x56dab5559cac75602ae5564aab5522a6d35a99b4c4a5e52ce9564a1a4c123c90547d23a11ac8c645a228d12087d435a148cf867533799a0cc265a3299930c8a63d2be15bcac45542a314e0a5251b28693dc9de4e226a931c9724ab24e123890046a1b68d7c69e33f1980c7c61c2fe1770b3057c2ae14f0a3c4fc26d12e893446222a111887042a2060f907803981b70d106382f816a0a304e825e12308b04241fa0f207303640f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
def record013_frame002_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5892c015dcadb563aacd540a8c53da98534c9944c125bd2b694749a248121e8f5477a3a11c28da469a33118a8be45ba2b8d8e6b73531a50d08675331193cc786232b91588aa253f2979480a1a4fa27393389904c125d12cc95a4a624f92609224881bf8da86ae3411960c646082f016d0ae455229914509e84d625b12608f043620c0ff07c03c41d60e306d834e1970c405e02d215909c04a423610d07f83dc1e00e9071036c0f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record013_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 2) (record013.inverseMaps 2) record013_frame002_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record013) (record013.maps 2)
      (record013.inverseMaps 2) record013_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame002_links_0000 record013_frame002_links_0064)
theorem record013_frame002_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 2 :=
  of_group record013 2 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record013_frame002_indices record013_frame002_graph record013_frame002_links
def record013_frame003_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x9063d8ea378d2308b229896208420c8260680dff7edf87d1ef7b5e9799e3781dc761d5745cc699a46819d6699764990635885d9745c16d5a96758960575585555353d4c525465053f4f13749120471164490d42104400f83d0f03a8e6384dc360d4328c630cc02ecb82d0b02a8a62849c260942288620c801ec761c86f1b06715451120350b822048110400f0380d0300b02809020060140400c02 } : Fields).get c.val)
theorem record013_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record013) (record013.maps 3) (record013.inverseMaps 3) record013_frame003_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (smallEmbedding record013) (record013.maps 3)
      (record013.inverseMaps 3) record013_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame003_links_0000 record013_frame003_links_0064)
theorem record013_frame003_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 3 :=
  of_group record013 3 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record013_frame003_indices record013_frame003_graph record013_frame003_links
def record013_frame004_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1094.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1094.count (({ width := 9, code := 0xadd66b156aad52a34fa6d2a813e9ecee75399b4d2652f974b257299449e49229047611078341207027fbf9f8f977bb9daeb753a5cce571b81bcdd6e369b2d86ab51a4cf623017cba5bad162ae55295429f4da612a9247a2d0a83409f8f4783a1c8dc6b34194c45e2c158a851269289046218fc6c3317094421b09044200f07034180b050241006028100602 } : Fields).get c.val)
theorem record013_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record013) (record013.maps 4) (record013.inverseMaps 4) record013_frame004_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1094.localPairCheck (smallEmbedding record013) (record013.maps 4)
      (record013.inverseMaps 4) record013_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame004_links_0000 record013_frame004_links_0064)
theorem record013_frame004_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 4 :=
  of_group record013 4 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1094
    Papers.RationalityTen.SharedFrameCatalogue.group1094_facts record013_frame004_indices record013_frame004_graph record013_frame004_links
def record013_frame005_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98bf84683a82d81f80c7f97e37d27c27a379c79378377276375373e72a7166fb5d95d25c95bf5b15a059058357355d4fb4f24e74dd4cf4c04af4a149347b4764704634554474394284184073f032d3203133052f52e72d92cd2be2a029628627526725a2492392282071f81e71d91cb1c21ba1ae1a019118317316515613512911a1090fc0f10e60d90cc0be07606c05d04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record013_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record013) (record013.maps 5) (record013.inverseMaps 5) record013_frame005_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record013) (record013.maps 5)
      (record013.inverseMaps 5) record013_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame005_links_0000 record013_frame005_links_0064)
theorem record013_frame005_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 5 :=
  of_group record013 5 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record013_frame005_indices record013_frame005_graph record013_frame005_links
def record013_frame006_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9d79c89c19b59a399498596f9609498c68b48a989b88987986784e83a81f8138037f87ed7d77c37af79978476962b61d61360b5fe5f35e55d75cb5b454353352851f5115044f44e44d64bf4b64a749c49348547a46c45c44d43836b35834d34133131f30c2fa2ea2c72b72ad2a12932862752652552322232132011f01e21d51cd1c41b51a81981871781551431331231131020f50e80da0cb07806e05f04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record013_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 6) (record013.inverseMaps 6) record013_frame006_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record013) (record013.maps 6)
      (record013.inverseMaps 6) record013_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame006_links_0000 record013_frame006_links_0064)
theorem record013_frame006_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 6 :=
  of_group record013 6 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record013_frame006_indices record013_frame006_graph record013_frame006_links
def record013_frame007_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x61260e60b6055ff5fb5f65f05eb5e458157556e56455754d54353352651450e5054fa4f04e64dc4cf4c04b54a03ee3ea3e73e13dc3d83d43cf3ca3c236635e35935334a34133933032531631230b3042fe2f52ef2e42da2d22c124523e23923022621b2122091fd1ea1e41de1d51c91c41b71ab1a518f18a18618117a17216715f15514613a12e11f1130fa0f20e90e20d60cc0c30bd0b40a806f06805b03e03602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record013_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record013) (record013.maps 7) (record013.inverseMaps 7) record013_frame007_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record013) (record013.maps 7)
      (record013.inverseMaps 7) record013_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame007_links_0000 record013_frame007_links_0064)
theorem record013_frame007_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 7 :=
  of_group record013 7 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record013_frame007_indices record013_frame007_graph record013_frame007_links
def record013_frame008_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xcf73acdf34cc72ecab25c8319be6f5bc6edba2e3b6ed2b26bfaeeb7aceafaaea7a8a9ba528c8f63a8de348c62e8aa2487a177f9fb7e1f57c5ed7a1de751c7715c26fdbb6ddb36b9a76819755d545454e52946505394c5244851e469164490e421023d4f03ace8390df36cd734ccf32cc72fcb729ca026494234872087d1e07115c5011c370cc27048110400f0380d0300b02809020060140400c02 } : Fields).get c.val)
theorem record013_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record013) (record013.maps 8) (record013.inverseMaps 8) record013_frame008_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record013) (record013.maps 8)
      (record013.inverseMaps 8) record013_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame008_links_0000 record013_frame008_links_0064)
theorem record013_frame008_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 8 :=
  of_group record013 8 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record013_frame008_indices record013_frame008_graph record013_frame008_links
def record013_frame009_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0374.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0374.count (({ width := 9, code := 0xa95429d4ca55228d44a14fa6d33984b65527924863d1a8c456250f864260d03803f1cce471381bcdc6d361acd265b258ec561b057ebc5cad166b157ab556a953a91429c4823d1c8d4622d14884320902803f9f8fa7c3d1e0e873391c4e06e361a8d0663218cc25f2d964ae55291449e4d259207c3d1b8ac542109044200f07034180b050241006028100602 } : Fields).get c.val)
theorem record013_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record013) (record013.maps 9) (record013.inverseMaps 9) record013_frame009_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0374.localPairCheck (smallEmbedding record013) (record013.maps 9)
      (record013.inverseMaps 9) record013_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame009_links_0000 record013_frame009_links_0064)
theorem record013_frame009_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 9 :=
  of_group record013 9 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0374
    Papers.RationalityTen.SharedFrameCatalogue.group0374_facts record013_frame009_indices record013_frame009_graph record013_frame009_links
def record013_frame010_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0xa0cfe7b3b9ccde6b3398cba4d239047635178a4461d0983c1607017fbf5f6f97bbcdb8da6c359a8d26833998c860afd7abb5cadd6ab358ab558aa5429948a25027938984321104803f1f0f4783b1c8e270379b8da6c351a0c86230178b85a2c960ae562a950a4502612890462210882401f8f86c351a0984a1f088401e0e06830160a048200e06028100602 } : Fields).get c.val)
theorem record013_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record013) (record013.maps 10) (record013.inverseMaps 10) record013_frame010_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record013) (record013.maps 10)
      (record013.inverseMaps 10) record013_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame010_links_0000 record013_frame010_links_0064)
theorem record013_frame010_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 10 :=
  of_group record013 10 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record013_frame010_indices record013_frame010_graph record013_frame010_links
def record013_frame011_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xa414668a50ea0b3f27c4f39d73824e48f90f1fe3a46a8c717629c4787b0be13c2082902601bfb7e6f95aab4d68cd019db31656c9d913155c4b55652c557cad5582aa54aa694aa8a5029ed39a684c69692ba4a3c0750e59c63806e0d99ae352664c71863005f0ba16e2d0594ab94b2804e09812723644c879072023f47b0f21ca36c688c91822dc568a413c260340600a60f01a0270240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record013_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record013) (record013.maps 11) (record013.inverseMaps 11) record013_frame011_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record013) (record013.maps 11)
      (record013.inverseMaps 11) record013_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame011_links_0000 record013_frame011_links_0064)
theorem record013_frame011_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 11 :=
  of_group record013 11 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record013_frame011_indices record013_frame011_graph record013_frame011_links
def record013_frame012_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x5642ad1540a8c53ba9894a0a3b513a82d292935490a43d1fa8ea46ba311160895445a1e50ce855422a0cd0448103ff1f90b285802b61560a8652e28e141c9e64d720a90047da3db1e48ed87463901be0d846ae3451998c846222ff1770b705942b010788204021fa0f987b03ca1de0eb87243841bb0da06b434c19f0cc064430217a0b985b02ca1600ac854829614409e84d825e12808c044421410307e03d41dc0e707003640f006e02f810006c027009004402000f007003401800b00500240100060028010006002 } : Fields).get c.val)
theorem record013_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 12) (record013.inverseMaps 12) record013_frame012_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record013) (record013.maps 12)
      (record013.inverseMaps 12) record013_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame012_links_0000 record013_frame012_links_0064)
theorem record013_frame012_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 12 :=
  of_group record013 12 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record013_frame012_indices record013_frame012_graph record013_frame012_links
def record013_frame013_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0xb8b702dd5b4b5f6aad1d9cb2b63693d1fa2d42e814fb9df39a6eccc98f2fe5b4aa941266464838f319dcb391716e15c037b6e8db5b335e5f0bc173adb5a2b295eab4554a614928a5029d936a664b4945242373b8754e71c63806e0d81a9344648c59842f85d8b71662be560a51462844f89d13525e4ac9291e230448861071f03c0748e11b4344648c21742cc3a86c0ba0fc1b0270240440800f01c0340600b0140240400600a01001802 } : Fields).get c.val)
theorem record013_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record013) (record013.maps 13) (record013.inverseMaps 13) record013_frame013_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record013) (record013.maps 13)
      (record013.inverseMaps 13) record013_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame013_links_0000 record013_frame013_links_0064)
theorem record013_frame013_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 13 :=
  of_group record013 13 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record013_frame013_indices record013_frame013_graph record013_frame013_links
def record013_frame014_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6aa62261960e6005f45e85d55c75b95a059858f58757f57756f56755f55654b42841f4144063fa3ee3db3cd3bf3a632c32331930c3022f82e82dc2d12bc2b52ac2a429c29428c28427c2732681fa1f31ec1e61df1d81d11ca1c31b71b01a81a119919018818117916716015915114a14513e13612f12711e11610f1070f50ee0e70df0d80d40d00cc0c80c407806e05f04003602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record013_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record013) (record013.maps 14) (record013.inverseMaps 14) record013_frame014_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record013) (record013.maps 14)
      (record013.inverseMaps 14) record013_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame014_links_0000 record013_frame014_links_0064)
theorem record013_frame014_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 14 :=
  of_group record013 14 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record013_frame014_indices record013_frame014_graph record013_frame014_links
def record013_frame015_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1090.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1090.count (({ width := 8, code := 0x88878684838281807f7e7d7c7b797877767574737271706e6d6c6b6a6968676665636261605f5e5d5c5b5a5857565554535251504f4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1b19171513110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1090.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1090.localPairCheck (smallEmbedding record013) (record013.maps 15) (record013.inverseMaps 15) record013_frame015_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1090.localPairCheck (smallEmbedding record013) (record013.maps 15) (record013.inverseMaps 15) record013_frame015_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1090.localPairCheck (smallEmbedding record013) (record013.maps 15)
      (record013.inverseMaps 15) record013_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame015_links_0000 record013_frame015_links_0064)
theorem record013_frame015_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 15 :=
  of_group record013 15 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1090
    Papers.RationalityTen.SharedFrameCatalogue.group1090_facts record013_frame015_indices record013_frame015_graph record013_frame015_links
def record013_frame016_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1093.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1093.count (({ width := 8, code := 0xb5b4b3b1b0afaeadacabaaa9a8a6a5a4a3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a79787776757472706f6c6a686664625f5d5c59575553514f4c4a48464442403f3c3a383634322f2d2b29272523211f1d1b19171513110f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record013_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record013) (record013.maps 16) (record013.inverseMaps 16) record013_frame016_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record013) (record013.maps 16) (record013.inverseMaps 16) record013_frame016_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1093.localPairCheck (smallEmbedding record013) (record013.maps 16)
      (record013.inverseMaps 16) record013_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame016_links_0000 record013_frame016_links_0064)
theorem record013_frame016_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 16 :=
  of_group record013 16 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1093
    Papers.RationalityTen.SharedFrameCatalogue.group1093_facts record013_frame016_indices record013_frame016_graph record013_frame016_links
def record013_frame017_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5a159c59158b57e57956f56155a5474f34ef4e54e14d54ce4c24b44ad49949649248647b46f46845c44d43f42b36836135c35034a34033332b32130e2ba2b42af2a529f29528827d27426025d25624d24023822f2212142061f218b18718117c17717116c16616115715414f14914313d13813212d12311d11611110e10c10a1051000fb0f60f00ea0e50d80d20cd0c70c30be0b80b30af0aa07006705803f03602701201101000f00e00d00c00b00a009008006005004003002 } : Fields).get c.val)
theorem record013_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record013) (record013.maps 17) (record013.inverseMaps 17) record013_frame017_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record013) (record013.maps 17) (record013.inverseMaps 17) record013_frame017_indices (Fin.ofNat record013.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record013_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record013) (record013.maps 17)
      (record013.inverseMaps 17) record013_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record013_frame017_links_0000 record013_frame017_links_0064)
theorem record013_frame017_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) : Supported record013 17 :=
  of_group record013 17 (smallEmbedding record013) (small_cells_exact record013 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record013_frame017_indices record013_frame017_graph record013_frame017_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSmall.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (Fin.cases (record013_frame002_supported hcells) (Fin.cases (record013_frame003_supported hcells) (Fin.cases (record013_frame004_supported hcells) (Fin.cases (record013_frame005_supported hcells) (Fin.cases (record013_frame006_supported hcells) (Fin.cases (record013_frame007_supported hcells) (Fin.cases (record013_frame008_supported hcells) (Fin.cases (record013_frame009_supported hcells) (Fin.cases (record013_frame010_supported hcells) (Fin.cases (record013_frame011_supported hcells) (Fin.cases (record013_frame012_supported hcells) (Fin.cases (record013_frame013_supported hcells) (Fin.cases (record013_frame014_supported hcells) (Fin.cases (record013_frame015_supported hcells) (Fin.cases (record013_frame016_supported hcells) (Fin.cases (record013_frame017_supported hcells) (fun j => Fin.elim0 j)))))))))))))))))))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xa89a82a7aa70a63a55a43a36a28a1493f93792e9239169098f88eb8dc8c984783c82f82180e7fc7e67d57c47ad79c79378377276375373e72a7167036f66e46d26bf6ab5d85cf5c65bc5ae59d58d5805705624fa4ef4e44da4cc4bd4ac49e4904804764704634554474394284184073f83e13d33c23b33a332e3233163082f82ea2dc2d02c12af2a029628627526725a24923922821a2051f61e51d71c91c21ba1ae1a01911831731651561461331271181070fa0f10e60d90cc0be0b503503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame001_links_0000 (interval_append _ 64 128 146 record014_frame001_links_0064 record014_frame001_links_0128))
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xb33b29b22b19b0baffaf1adbaccabc9da9cb9c29b89a59969889729639548c88b68aa89e88c87c86a85183d82a8138037f87ed7d77c37af79978477076374f73872170962861a6126085fb5f05e25d45c85b954053052751c50e5014f14e14d34c44b64a749c49348547a46c45c44d44042641840a3f93eb36e35b34e34433432230f2fd2ed2db2c72b72ad2a12932862752652552462302212111ff1ee1e21d51cd1c41b51a819818717816b1531411311211111020f50e80da0cb0c003503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame002_links_0000 (interval_append _ 64 128 146 record014_frame002_links_0064 record014_frame002_links_0128))
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
def record014_frame003_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xe5792e3f8ce2786e0b7edeb76cfb3bce335ccb2fcaf26c871cbeaf6bcaeeba6e4b76d4b2ec2aeeb7aceafaaea7a8a9ba528ea22819ea739be3c8e6368ce308b62888a1c861fd7e9f77cdef7ade576dd1729c5709bf6edb76cdae69da06698e61d805f579561555494f52d4750d3b4cd2b491214791a4591243908408fd3d0ef3a8e738cdf36cd734ccf32cc72fcb72c0a627c9824c8b21c821f4781c46e0c8310c02f0b8260942408c220300b02809020060140400c02 } : Fields).get c.val)
theorem record014_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record014) (record014.maps 3) (record014.inverseMaps 3) record014_frame003_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record014) (record014.maps 3)
      (record014.inverseMaps 3) record014_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame003_links_0000 (interval_append _ 64 128 146 record014_frame003_links_0064 record014_frame003_links_0128))
theorem record014_frame003_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 3 :=
  of_group record014 3 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record014_frame003_indices record014_frame003_graph record014_frame003_links
def record014_frame004_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x2c761afd76b759abd56a751a15027d3c9d4e26d34994c24f2490c7a37188ac4a1f0c83c1607017fbf5f6f97bbd5e4f0773b1d4db6cb5daad368b3d9acb64b017cbc5d2e16cb4592c15cac552a14ca4512813c9c4d2592892482390e8541a04fe7d3d9e4ee75391c4e06f371b4d86a34198c6612f974b65a2c960ae562a950a4502712c92472290c8441200fc7c3d1208c4421100783a1c0d868160a048200e06028100602 } : Fields).get c.val)
theorem record014_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record014) (record014.maps 4) (record014.inverseMaps 4) record014_frame004_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record014) (record014.maps 4)
      (record014.inverseMaps 4) record014_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame004_links_0000 (interval_append _ 64 128 146 record014_frame004_links_0064 record014_frame004_links_0128))
theorem record014_frame004_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 4 :=
  of_group record014 4 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record014_frame004_indices record014_frame004_graph record014_frame004_links
def record014_frame005_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1860c2060a30197f4bf05f3af41774ba454f2a35504a76535a9854a6a3d513284d3049704af253527692e48fa41d1de8d9462a2cd14289043f21c90c484c41ba08902a7ff3f51f50f7c6a434b1a14cf2668330194cc8262f30f1698b2e58a2bd95b8aca5582a294d8a5051c28593f09da4de269931c9684a524b91fc8d845c22690f476039e1c70df86dc3631aa8d0065831a1830bd05c62d31610ae055029414089bc4ae24511908804181fd0f707803a21c30dc86ac3301860bb058829a13e097047421e0ff07903941ac0ca01a80d0066032018809804a024011808801800b00500240100060028010006002 } : Fields).get c.val)
theorem record014_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 5) (record014.inverseMaps 5) record014_frame005_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record014) (record014.maps 5)
      (record014.inverseMaps 5) record014_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame005_links_0000 (interval_append _ 64 128 146 record014_frame005_links_0064 record014_frame005_links_0128))
theorem record014_frame005_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 5 :=
  of_group record014 5 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record014_frame005_indices record014_frame005_graph record014_frame005_links
def record014_frame006_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xd5351d3b4bd2345cfb37ccb2dbd2f1bbaebba2e5b86dab5ad2ac2acaa2a4a829ca5a8ba127d9e6779d2729be6c99a5d9564d91a3f8ea358c5fe7f1fa7e1f67d1f07a9e5781c4709c06f9bc6e9b36b1a66819c66998659946498b601795c96658d60575594e5354c52e4a927489184490c41903400fe3ecf93cceb398e135cd333ccb320c5304bd2e8b62ccad2949f2648d21c821f4781c86e1ac681805e0b02b0a8290a023088210801f0300b02809020060140400c02 } : Fields).get c.val)
theorem record014_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 6) (record014.inverseMaps 6) record014_frame006_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record014) (record014.maps 6)
      (record014.inverseMaps 6) record014_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame006_links_0000 (interval_append _ 64 128 146 record014_frame006_links_0064 record014_frame006_links_0128))
theorem record014_frame006_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 6 :=
  of_group record014 6 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record014_frame006_indices record014_frame006_graph record014_frame006_links
def record014_frame007_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x8a62688e208761a85a1283a0a7a5e678de0775da75dd4745ce6e5b66cdb06b5aa695a066d9664d9163d8d62d8961d846057e5ed795dd755cd5855954549505394b521455092e4b12a4a1264912247d1c46517455134450f4350a419023f8fa3e0f63d0f2360d5348cf330c9318c12f0b72c8b02b8ac2a8a8298a22789a2549223c8c2288821884208801f87c1dc721b467190611785b1685815854144500a42809c260942007c1e0741c0300b02809020060140400c02 } : Fields).get c.val)
theorem record014_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record014) (record014.maps 7) (record014.inverseMaps 7) record014_frame007_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record014) (record014.maps 7)
      (record014.inverseMaps 7) record014_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame007_links_0000 (interval_append _ 64 128 146 record014_frame007_links_0064 record014_frame007_links_0128))
theorem record014_frame007_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 7 :=
  of_group record014 7 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record014_frame007_indices record014_frame007_graph record014_frame007_links
def record014_frame008_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x17dabdb5e22ed1748b915c02dc16bab5152828f5448a1450227cd3c89d44e1a6d926a91e482a3c51c08cc45d22a512a88743c2181092835411a0490027ef3ef1f4cf9a7b73d01e20eec6443179868c165fc2f61778b9e5bf2da94eca4e51228113d09ce4d726492f09644a824b12108e846722d113087e43221390508083f21f28f646a633d1938c5c6102f91750b6c5982c01588a7451427813689804a424711d08c444020f0fe87c43c81d60e306d435019c0c806142f216d0b2054c28012d090845420e0f907483781a80c901a80d0066032018809804a024011808801800b00500240100060028010006002 } : Fields).get c.val)
theorem record014_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 8) (record014.inverseMaps 8) record014_frame008_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record014) (record014.maps 8)
      (record014.inverseMaps 8) record014_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame008_links_0000 (interval_append _ 64 128 146 record014_frame008_links_0064 record014_frame008_links_0128))
theorem record014_frame008_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 8 :=
  of_group record014 8 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record014_frame008_indices record014_frame008_graph record014_frame008_links
def record014_frame009_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x2d259eb3565ec6584b055f2bad6da4546e8ad10a0f3f67d4f49db38e4fc929112063b46b8cb17a2ac4a87b0be13c2082902601bfb7e6f9df1bd9794eedd6b52694d159f33865eca592b1f62cb7d692c9586af159aae550a8d4da95514a053da734d098d2d25749890519a2743c84cf19d7398720e11b936a6bcd59a2332638c31802f85d0b71682ca574aa94927c4dc9792723644c879072023f47b0f21d838c6c8cf1903005b8ad1482784c0920660c81883005e098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record014_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record014) (record014.maps 9) (record014.inverseMaps 9) record014_frame009_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record014) (record014.maps 9)
      (record014.inverseMaps 9) record014_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame009_links_0000 (interval_append _ 64 128 146 record014_frame009_links_0064 record014_frame009_links_0128))
theorem record014_frame009_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 9 :=
  of_group record014 9 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record014_frame009_indices record014_frame009_graph record014_frame009_links
def record014_frame010_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x361aed66ab51a6d268b419ec5e270f85c1e06ff7dbdde6e56fb65a6cb61aed66ab51a652a9146a1d027b3a9bcd2632e95ca24d1388436150782405fcfb7cbc5dceb73b8dbedb6bb4da2ce6632990c5612fd78b95b2c158a852a8930964a2491e8c44a1906803f1f4f87b3c9dcea73389bcda6b3499cca6431988c25f2e96cb2572a9489e4c249188842200f8783b138984a2411884401f0f074160a048200e06028100602 } : Fields).get c.val)
theorem record014_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record014) (record014.maps 10) (record014.inverseMaps 10) record014_frame010_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record014) (record014.maps 10)
      (record014.inverseMaps 10) record014_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame010_links_0000 (interval_append _ 64 128 146 record014_frame010_links_0064 record014_frame010_links_0128))
theorem record014_frame010_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 10 :=
  of_group record014 10 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record014_frame010_indices record014_frame010_graph record014_frame010_links
def record014_frame011_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1a5ad2668fb461a22d0a681b3f19eacee58aac0d5e2ade5652ad9546a8f53f29b13529974c2a5c92bc94a49ba48d224900477a3a11c28da469a33118a8be45ba2c11568a444ea25911e6c435a1a8cd22681339197cc9863931415bcabe54e29e14b0a3a50a27b93909a64c826092e89664ad253127c93049124512048f647523791a470436d1ad0d1065e31c1838bcc5ba2ca15c8aa453228a13d09ac4b624c11e08b443220a0fe07b83c01d60e306d834e1970c405e02d21590a504d824e11908583f41ee0f007483881b60d501a80d0066032018809804a024011808801800b00500240100060028010006002 } : Fields).get c.val)
theorem record014_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 11) (record014.inverseMaps 11) record014_frame011_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 11)
      (record014.inverseMaps 11) record014_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame011_links_0000 (interval_append _ 64 128 146 record014_frame011_links_0064 record014_frame011_links_0128))
theorem record014_frame011_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 11 :=
  of_group record014 11 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame011_indices record014_frame011_graph record014_frame011_links
def record014_frame012_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x78d78778177c77677276d7667607596a469968d68267a67366b65a64f6425e95de5d65ce5c25b85b059f59358957c57556e56756055b55554e54754053b53452d52651f44343842e42141640f4033f23e63db37636c36135734d34233632531930e3073002f92f22eb2e62e02d92d22cb2c32bc2b52af2aa23f23422621c20e2051f81ed1e01d61cb1c31bc1b51ae1a81a119718f18617816c16615d15414b14313c13512e12812111710d1070f80ec0e40df0d40ce0c90c30c00bd0b803503403303203102602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record014_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame012_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 12) (record014.inverseMaps 12) record014_frame012_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record014) (record014.maps 12)
      (record014.inverseMaps 12) record014_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame012_links_0000 (interval_append _ 64 128 146 record014_frame012_links_0064 record014_frame012_links_0128))
theorem record014_frame012_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 12 :=
  of_group record014 12 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record014_frame012_indices record014_frame012_graph record014_frame012_links
def record014_frame013_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0754.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0754.count (({ width := 9, code := 0x30f86c2e130782bfdf6f779b65aad165b1d82bb5bacd5e9347a2d0a813d9d4e26d34994c25d2c954a24b218ec662d14894421cfd7dbe5eef579bc5dceb74365aed569b459ecd6531d88c2602f978ba5c2d562ad54a9548a351281269147a35168943a1506813f9f8fa7c3d9e8f276399c0d66933994c66230980be5e2e970b25629938984a241188a44219087e3e12890462210870361a0c860180b050241006028100602 } : Fields).get c.val)
theorem record014_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame013_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record014) (record014.maps 13) (record014.inverseMaps 13) record014_frame013_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record014) (record014.maps 13)
      (record014.inverseMaps 13) record014_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame013_links_0000 (interval_append _ 64 128 146 record014_frame013_links_0064 record014_frame013_links_0128))
theorem record014_frame013_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 13 :=
  of_group record014 13 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0754
    Papers.RationalityTen.SharedFrameCatalogue.group0754_facts record014_frame013_indices record014_frame013_graph record014_frame013_links
def record014_frame014_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0195.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0195.count (({ width := 9, code := 0x2592b954a6512792c8e431f8c45a29128843a190a84419fcfc7d3e1ecf4793c1dcec753a1cce471381bcdb6c355a4d16833d9cc66230980be5e2e970b65a2b154a85329144a04f27134994ba55269147a31128641a05007f3f1f4ec74391c0dc6c351a0cc6431184c05f2f174b85a2c158a65127934964a249208e462291084401f0ec72371a8cc6431180bc5a2c0f074381b0d06430170b05414090401c0c050200c0401 } : Fields).get c.val)
theorem record014_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0195.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame014_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record014) (record014.maps 14) (record014.inverseMaps 14) record014_frame014_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record014) (record014.maps 14)
      (record014.inverseMaps 14) record014_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame014_links_0000 (interval_append _ 64 128 146 record014_frame014_links_0064 record014_frame014_links_0128))
theorem record014_frame014_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 14 :=
  of_group record014 14 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0195
    Papers.RationalityTen.SharedFrameCatalogue.group0195_facts record014_frame014_indices record014_frame014_graph record014_frame014_links
def record014_frame015_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0723.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0723.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0723.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0723.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0723.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame015_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0723.localPairCheck (smallEmbedding record014) (record014.maps 15) (record014.inverseMaps 15) record014_frame015_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0723.localPairCheck (smallEmbedding record014) (record014.maps 15)
      (record014.inverseMaps 15) record014_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame015_links_0000 (interval_append _ 64 128 146 record014_frame015_links_0064 record014_frame015_links_0128))
theorem record014_frame015_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 15 :=
  of_group record014 15 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0723
    Papers.RationalityTen.SharedFrameCatalogue.group0723_facts record014_frame015_indices record014_frame015_graph record014_frame015_links
def record014_frame016_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0181.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0181.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0181.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0181.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0181.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame016_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0181.localPairCheck (smallEmbedding record014) (record014.maps 16) (record014.inverseMaps 16) record014_frame016_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0181.localPairCheck (smallEmbedding record014) (record014.maps 16)
      (record014.inverseMaps 16) record014_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame016_links_0000 (interval_append _ 64 128 146 record014_frame016_links_0064 record014_frame016_links_0128))
theorem record014_frame016_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 16 :=
  of_group record014 16 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0181
    Papers.RationalityTen.SharedFrameCatalogue.group0181_facts record014_frame016_indices record014_frame016_graph record014_frame016_links
def record014_frame017_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x68167c67566f66866065965264a6445b45ad5a059558c58057656b55f55751250b4fe4f34e84dc4d44cb4bf4b54ad4a74a149b49448d48748047947447046a46345c4563a239738b37d37436a35d35434c3432f32e82dc2cd2c42bc2af2a629c29428e28828227b27526e26826225b25724f24924323b2351ea1df1d51ca1c21b81af1a719d19618f18717c17617216e16816315d15815014613c13813112d12511a11210d1071020fe0fa0f60ee0e40da0d30d00cc0c70c20be0bc0bb03403303203103002602502402302200c00b00a009008006005004003002 } : Fields).get c.val)
theorem record014_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame017_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record014) (record014.maps 17) (record014.inverseMaps 17) record014_frame017_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (smallEmbedding record014) (record014.maps 17)
      (record014.inverseMaps 17) record014_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame017_links_0000 (interval_append _ 64 128 146 record014_frame017_links_0064 record014_frame017_links_0128))
theorem record014_frame017_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 17 :=
  of_group record014 17 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record014_frame017_indices record014_frame017_graph record014_frame017_links
def record014_frame018_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0934.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0934.count (({ width := 9, code := 0x2a953a9546a14fa6d3297499acd26530974b255289349233188b4522510874321508834160702803fdfafb7d3e1ecf479bc5ded86b351a4d067b3596ca64afd7abb5cadd6cb4592c560af572b156a95429948a350a793a9b4ca5d14884320d027e3e1e8ee75399c4de6d359a4d0663218cc05e2e168b0572a94ca24f2693094482391084401f0f0763a1c8e06e36138984a241188842200f878180b050241006028100602 } : Fields).get c.val)
theorem record014_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0934.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame018_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record014) (record014.maps 18) (record014.inverseMaps 18) record014_frame018_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0934.localPairCheck (smallEmbedding record014) (record014.maps 18)
      (record014.inverseMaps 18) record014_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame018_links_0000 (interval_append _ 64 128 146 record014_frame018_links_0064 record014_frame018_links_0128))
theorem record014_frame018_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 18 :=
  of_group record014 18 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0934
    Papers.RationalityTen.SharedFrameCatalogue.group0934_facts record014_frame018_indices record014_frame018_graph record014_frame018_links
def record014_frame019_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0696.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0696.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0696.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0696.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0696.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame019_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0696.localPairCheck (smallEmbedding record014) (record014.maps 19) (record014.inverseMaps 19) record014_frame019_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0696.localPairCheck (smallEmbedding record014) (record014.maps 19)
      (record014.inverseMaps 19) record014_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame019_links_0000 (interval_append _ 64 128 146 record014_frame019_links_0064 record014_frame019_links_0128))
theorem record014_frame019_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 19 :=
  of_group record014 19 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0696
    Papers.RationalityTen.SharedFrameCatalogue.group0696_facts record014_frame019_indices record014_frame019_graph record014_frame019_links
def record014_frame020_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0085.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0085.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0085.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0085.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0085.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame020_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0085.localPairCheck (smallEmbedding record014) (record014.maps 20) (record014.inverseMaps 20) record014_frame020_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0085.localPairCheck (smallEmbedding record014) (record014.maps 20)
      (record014.inverseMaps 20) record014_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame020_links_0000 (interval_append _ 64 128 146 record014_frame020_links_0064 record014_frame020_links_0128))
theorem record014_frame020_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 20 :=
  of_group record014 20 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0085
    Papers.RationalityTen.SharedFrameCatalogue.group0085_facts record014_frame020_indices record014_frame020_graph record014_frame020_links
def record014_frame021_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x2bc574add5a6b2d61ab554ea75489a333663cc297d2ea59cac94f2863245d8ab13e24c438790d616c2683f0620840a808ff9fbbf07d0f85ee3d87a8f41e635d6b0d4da7349688cf99c331654b61682c9586af95dab3552a894da92516a0d3da764e29a52f2544948f91c23345c8a0ec1d1392704de1b735e690cd19030a5f4bb1702d65a0b015629e5209f1382664b894123238454879092043f07a8ee1ce3806c8d219c320610bb1682c0550a706a0d019832062098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record014_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame021_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record014) (record014.maps 21) (record014.inverseMaps 21) record014_frame021_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (smallEmbedding record014) (record014.maps 21)
      (record014.inverseMaps 21) record014_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame021_links_0000 (interval_append _ 64 128 146 record014_frame021_links_0064 record014_frame021_links_0128))
theorem record014_frame021_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 21 :=
  of_group record014 21 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record014_frame021_indices record014_frame021_graph record014_frame021_links
def record014_frame022_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x2bdd73adf5a2b155daaf546a5d4698d30e5e4b595f2ae5249d93324e2cc4f89110a1e4368610a20f41881d021ff3f87e2fb5f33dd7aef39e3bc3778ed5d8b3c66ccc596b28646c798c31261aafd5bab455aaa95129b52ca3543a7e4ea9bd332604b494123a3f46889510a1b42e840e11ba3686acd319f32a630c11792d659cb195c2ac550a514127c4d8951232404708a91021240c7f8f91e83b8740e11b434c670c81882f45b0b015629c5009c06a0d019832062098128240460880600b0140240400600a01001802 } : Fields).get c.val)
theorem record014_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame022_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record014) (record014.maps 22) (record014.inverseMaps 22) record014_frame022_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record014) (record014.maps 22)
      (record014.inverseMaps 22) record014_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame022_links_0000 (interval_append _ 64 128 146 record014_frame022_links_0064 record014_frame022_links_0128))
theorem record014_frame022_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 22 :=
  of_group record014 22 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record014_frame022_indices record014_frame022_graph record014_frame022_links
def record014_frame023_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0373.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0373.count (({ width := 9, code := 0x2130782c0e02ff7ebedf2f77a3c9e0ee763a9d0e672389bedd6db65aed569b459ecd65b258ec561b057ebd5dae56eb559ac55eac552a14ca4512813c9c4da6530974b255289349245208f46a2d128742a0d027f3e9e8f0763a1c8e26f369acd2673298cc25f2e970b65a2c960ae562a950a4502713094492411c8c452210c8441200fc7c3d1e0ec74391c0dc6c35108803e1e0e86c34190c05c160a048200e06028100602 } : Fields).get c.val)
theorem record014_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame023_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record014) (record014.maps 23) (record014.inverseMaps 23) record014_frame023_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0373.localPairCheck (smallEmbedding record014) (record014.maps 23)
      (record014.inverseMaps 23) record014_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame023_links_0000 (interval_append _ 64 128 146 record014_frame023_links_0064 record014_frame023_links_0128))
theorem record014_frame023_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 23 :=
  of_group record014 23 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0373
    Papers.RationalityTen.SharedFrameCatalogue.group0373_facts record014_frame023_indices record014_frame023_graph record014_frame023_links
def record014_frame024_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x26ccd69a1326624c09772d257ca78931162043d86f0c215c2483905df23de7acf41e6bc7784ee9dabad74ae7dce39771ee21c1b7b6eadbdb3b636c0d69a9aed5d0b856dad459eb29622be5729f13d2764de9ad342604b0955272484868f51aa2f4548850ba114127f0fb1f23d8798d59a533e664c998d3085e8b996a2c056cab9542a0530a213c26c4cc9512423a4688a1102124107e8f81e43b4748e31ba358688cd1903105e8b81662c0558a70660c81883005e094120230440840600b0140240400600a01001802 } : Fields).get c.val)
theorem record014_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame024_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record014) (record014.maps 24) (record014.inverseMaps 24) record014_frame024_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (smallEmbedding record014) (record014.maps 24)
      (record014.inverseMaps 24) record014_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame024_links_0000 (interval_append _ 64 128 146 record014_frame024_links_0064 record014_frame024_links_0128))
theorem record014_frame024_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 24 :=
  of_group record014 24 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record014_frame024_indices record014_frame024_graph record014_frame024_links
def record014_frame025_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0749.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0749.count (({ width := 8, code := 0xa3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a797877767574737271706f6e6d6c6a6968676665646362615f5e5d5c5b5a59585755545352504f4e4d4c4b4a4948474644434241403f3e3d3c3b3a38373634333231302f2e2d2c2b2a29272625232221201f1d1c1b1a1918131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0749.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame025_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record014) (record014.maps 25) (record014.inverseMaps 25) record014_frame025_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0749.localPairCheck (smallEmbedding record014) (record014.maps 25)
      (record014.inverseMaps 25) record014_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame025_links_0000 (interval_append _ 64 128 146 record014_frame025_links_0064 record014_frame025_links_0128))
theorem record014_frame025_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 25 :=
  of_group record014 25 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0749
    Papers.RationalityTen.SharedFrameCatalogue.group0749_facts record014_frame025_indices record014_frame025_graph record014_frame025_links
def record014_frame026_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0192.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0192.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0192.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0192.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0192.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame026_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0192.localPairCheck (smallEmbedding record014) (record014.maps 26) (record014.inverseMaps 26) record014_frame026_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0192.localPairCheck (smallEmbedding record014) (record014.maps 26)
      (record014.inverseMaps 26) record014_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame026_links_0000 (interval_append _ 64 128 146 record014_frame026_links_0064 record014_frame026_links_0128))
theorem record014_frame026_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 26 :=
  of_group record014 26 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0192
    Papers.RationalityTen.SharedFrameCatalogue.group0192_facts record014_frame026_indices record014_frame026_graph record014_frame026_links
def record014_frame027_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1092.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1092.count (({ width := 9, code := 0x2f578bb5d2e571b7db6d769ab552a550a75369749a3d1677399bcd66732984ba592a9449a49229047e3b1b8cc5e2b1489c4a23007f3f1f4f87bbd5e6f076b8dc2df6eb6db4d86b34da0cd65b258cc561b057cbb5c2d566b1582b948a250275389a4c255248f46a2d128742a1104803e9e8ee75399c8e06f369acd26733190c45f2e164ae552a148a04e2612c92480c8602e160a844200f070341208038180a04018080200 } : Fields).get c.val)
theorem record014_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame027_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record014) (record014.maps 27) (record014.inverseMaps 27) record014_frame027_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1092.localPairCheck (smallEmbedding record014) (record014.maps 27)
      (record014.inverseMaps 27) record014_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame027_links_0000 (interval_append _ 64 128 146 record014_frame027_links_0064 record014_frame027_links_0128))
theorem record014_frame027_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 27 :=
  of_group record014 27 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1092
    Papers.RationalityTen.SharedFrameCatalogue.group1092_facts record014_frame027_indices record014_frame027_graph record014_frame027_links
def record014_frame028_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0989.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0989.count (({ width := 8, code := 0xa3a2a1a09f9e9d9b9a9998979695949392908f8e8d8c8b8a8988878584838281807f7e7d7c7a797877767574737271706f6e6d6c6a6968676665646362615f5e5d5c5b5a59585755545352504f4e4d4c4b4a4948474644434241403f3e3d3c3b3a38373634333231302f2e2d2c2b2a29272625232221201f1d1c1b1a1918131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record014) (record014.maps 28) (record014.inverseMaps 28) record014_frame028_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record014) (record014.maps 28) (record014.inverseMaps 28) record014_frame028_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame028_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record014) (record014.maps 28) (record014.inverseMaps 28) record014_frame028_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0989.localPairCheck (smallEmbedding record014) (record014.maps 28)
      (record014.inverseMaps 28) record014_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame028_links_0000 (interval_append _ 64 128 146 record014_frame028_links_0064 record014_frame028_links_0128))
theorem record014_frame028_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 28 :=
  of_group record014 28 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0989
    Papers.RationalityTen.SharedFrameCatalogue.group0989_facts record014_frame028_indices record014_frame028_graph record014_frame028_links
def record014_frame029_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0745.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0745.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0745.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0745.localPairCheck (smallEmbedding record014) (record014.maps 29) (record014.inverseMaps 29) record014_frame029_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0745.localPairCheck (smallEmbedding record014) (record014.maps 29) (record014.inverseMaps 29) record014_frame029_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame029_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0745.localPairCheck (smallEmbedding record014) (record014.maps 29) (record014.inverseMaps 29) record014_frame029_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0745.localPairCheck (smallEmbedding record014) (record014.maps 29)
      (record014.inverseMaps 29) record014_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame029_links_0000 (interval_append _ 64 128 146 record014_frame029_links_0064 record014_frame029_links_0128))
theorem record014_frame029_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 29 :=
  of_group record014 29 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0745
    Papers.RationalityTen.SharedFrameCatalogue.group0745_facts record014_frame029_indices record014_frame029_graph record014_frame029_links
def record014_frame030_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0191.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0191.count (({ width := 8, code := 0x91908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record014_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0191.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0191.localPairCheck (smallEmbedding record014) (record014.maps 30) (record014.inverseMaps 30) record014_frame030_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0191.localPairCheck (smallEmbedding record014) (record014.maps 30) (record014.inverseMaps 30) record014_frame030_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame030_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0191.localPairCheck (smallEmbedding record014) (record014.maps 30) (record014.inverseMaps 30) record014_frame030_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0191.localPairCheck (smallEmbedding record014) (record014.maps 30)
      (record014.inverseMaps 30) record014_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame030_links_0000 (interval_append _ 64 128 146 record014_frame030_links_0064 record014_frame030_links_0128))
theorem record014_frame030_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 30 :=
  of_group record014 30 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0191
    Papers.RationalityTen.SharedFrameCatalogue.group0191_facts record014_frame030_indices record014_frame030_graph record014_frame030_links
def record014_frame031_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1089.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1089.count (({ width := 9, code := 0x2c761af56eb357aa5469f4ca1d067d3b9ccde693197cb24d2490c7a391a8bc52250f8642a0f0481401fafa7c3d5e4f1783bddce974399cae471b85bede6e365b0d66ab51a6d167b3998cb6431986c15f2ed72b659abd5cac55aa94ea45127d3a9a4ba55248f4622d128843a190882409fcfa7c3d1e4f0773b1d0e672389bcda6c351a0ce653218cc2602f174b85b138984a241187c3c1d0e06c180b050241006028100602 } : Fields).get c.val)
theorem record014_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record014) (record014.maps 31) (record014.inverseMaps 31) record014_frame031_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record014) (record014.maps 31) (record014.inverseMaps 31) record014_frame031_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame031_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record014) (record014.maps 31) (record014.inverseMaps 31) record014_frame031_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1089.localPairCheck (smallEmbedding record014) (record014.maps 31)
      (record014.inverseMaps 31) record014_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame031_links_0000 (interval_append _ 64 128 146 record014_frame031_links_0064 record014_frame031_links_0128))
theorem record014_frame031_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 31 :=
  of_group record014 31 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1089
    Papers.RationalityTen.SharedFrameCatalogue.group1089_facts record014_frame031_indices record014_frame031_graph record014_frame031_links
def record014_frame032_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0984.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0984.count (({ width := 8, code := 0xf0eeeceae8e6e4e2e0dedcdad8d6d4d2d0cecccac8c6c4c2c0bebcbab8b6b4b2b0aeacaaa8a6a4a2a09f9e9d9c9b9a999897969594939291908f8e8d8c8b8a8988878583817f7d7b797775737271706f6e6c6a68666462605e5c5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a39383721201f1e1d1c1b1a19180c0b0a09080605040302 } : Fields).get c.val)
theorem record014_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record014) (record014.maps 32) (record014.inverseMaps 32) record014_frame032_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record014) (record014.maps 32) (record014.inverseMaps 32) record014_frame032_indices (Fin.ofNat record014.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record014_frame032_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record014) (record014.maps 32) (record014.inverseMaps 32) record014_frame032_indices (Fin.ofNat record014.n i)) 128 146 :=
  interval_of_check _ 128 18 (by decide +kernel)
theorem record014_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0984.localPairCheck (smallEmbedding record014) (record014.maps 32)
      (record014.inverseMaps 32) record014_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 146 record014_frame032_links_0000 (interval_append _ 64 128 146 record014_frame032_links_0064 record014_frame032_links_0128))
theorem record014_frame032_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 32 :=
  of_group record014 32 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0984
    Papers.RationalityTen.SharedFrameCatalogue.group0984_facts record014_frame032_indices record014_frame032_graph record014_frame032_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (Fin.cases (record014_frame003_supported hcells) (Fin.cases (record014_frame004_supported hcells) (Fin.cases (record014_frame005_supported hcells) (Fin.cases (record014_frame006_supported hcells) (Fin.cases (record014_frame007_supported hcells) (Fin.cases (record014_frame008_supported hcells) (Fin.cases (record014_frame009_supported hcells) (Fin.cases (record014_frame010_supported hcells) (Fin.cases (record014_frame011_supported hcells) (Fin.cases (record014_frame012_supported hcells) (Fin.cases (record014_frame013_supported hcells) (Fin.cases (record014_frame014_supported hcells) (Fin.cases (record014_frame015_supported hcells) (Fin.cases (record014_frame016_supported hcells) (Fin.cases (record014_frame017_supported hcells) (Fin.cases (record014_frame018_supported hcells) (Fin.cases (record014_frame019_supported hcells) (Fin.cases (record014_frame020_supported hcells) (Fin.cases (record014_frame021_supported hcells) (Fin.cases (record014_frame022_supported hcells) (Fin.cases (record014_frame023_supported hcells) (Fin.cases (record014_frame024_supported hcells) (Fin.cases (record014_frame025_supported hcells) (Fin.cases (record014_frame026_supported hcells) (Fin.cases (record014_frame027_supported hcells) (Fin.cases (record014_frame028_supported hcells) (Fin.cases (record014_frame029_supported hcells) (Fin.cases (record014_frame030_supported hcells) (Fin.cases (record014_frame031_supported hcells) (Fin.cases (record014_frame032_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x93e93592c9209139068f58e88d98c684683a82d81f80c7f97e37d27c27aa79b79078076f76075073b7277137005d95d25c95bf5b15a05905835735644fb4f24e74dd4cf4c04af4a149348347546d4604524444364254154043f532d3203133052f52e72d92cd2be2ac2a029628627526725a24923922821a2071f81e71d91cb1c21ba1ae1a019118317316515614613512911a1090fc05705605505405302102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
def record015_frame002_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0x9d79c89c19b59a399498596f9609518c68b48a989b88987986784e83a8278108007f77ea7d47c07ac79678176e62b61d61360b5fe5f35e55d75cb5bc54353352851f5115044f44e44d64c74b34a449b49048247746945944a43d36b35834d34133131f30c2fa2ea2d82c72b72ad2a12932862752652552462322232132011f01e21d51cd1c41b51a819818717816b15514313312311305905805705605502102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record015) (record015.maps 2) (record015.inverseMaps 2) record015_frame002_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (smallEmbedding record015) (record015.maps 2)
      (record015.inverseMaps 2) record015_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame002_links_0000 record015_frame002_links_0064)
theorem record015_frame002_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 2 :=
  of_group record015 2 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record015_frame002_indices record015_frame002_graph record015_frame002_links
def record015_frame003_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0382.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0382.count (({ width := 10, code := 0xcf73acdf34cc72ecab25c831bbe6f5bc6edba2e3b6ed2b26c1aeab6acaadaa6a5a8299a4a8d8f63a8de348c62e8aa2487a197f9fb7e1f57c5ed7a1de751cb711c16f9b96d5b16b1a56799955d545454e52946505394c52a491214791a4591243908408fd3d4f03ace8390df36cd734ccf32cc72fcb72c0a7280992508d104400fc3e0f4210801f0781d0441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record015_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record015) (record015.maps 3) (record015.inverseMaps 3) record015_frame003_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0382.localPairCheck (smallEmbedding record015) (record015.maps 3)
      (record015.inverseMaps 3) record015_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame003_links_0000 record015_frame003_links_0064)
theorem record015_frame003_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 3 :=
  of_group record015 3 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0382
    Papers.RationalityTen.SharedFrameCatalogue.group0382_facts record015_frame003_indices record015_frame003_graph record015_frame003_links
def record015_frame004_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0452.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0452.count (({ width := 9, code := 0x2833f9ecee73379acce632f9348e411d8d45e29118742e0d0481401fcfc7d3e1ecf46e369b0d66a349a0ce6632982bf5eaed72b75aacd62af55aa54ea551a853e9d4da650c8441200fc7c3d1e0ec74391c4e06f371b4d86a34198c86230178b85a2c960ae562a950a450271309448231105c2d160ac54190c05c2c150803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record015_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record015) (record015.maps 4) (record015.inverseMaps 4) record015_frame004_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0452.localPairCheck (smallEmbedding record015) (record015.maps 4)
      (record015.inverseMaps 4) record015_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame004_links_0000 record015_frame004_links_0064)
theorem record015_frame004_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 4 :=
  of_group record015 4 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0452
    Papers.RationalityTen.SharedFrameCatalogue.group0452_facts record015_frame004_indices record015_frame004_graph record015_frame004_links
def record015_frame005_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1536a8b53fa9d14d0a6052828e9448a114bfa5b92b894b49ca4b5238904476a35d1848b044f22350f687142fa12506881f3539a64d1067c3359984cac6443191884b5259a2c695f8ae25662ad9520a7252b28c94209f24ea26d93489884b1251125075a39b1c60dec6d83621a90cf46523171830bd05c62d31610ae055029414089bc4b224711a088841c1fd0f707803a21c30dc86ac3301860bb059029e140098047c0b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record015_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 5) (record015.inverseMaps 5) record015_frame005_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record015) (record015.maps 5)
      (record015.inverseMaps 5) record015_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame005_links_0000 record015_frame005_links_0064)
theorem record015_frame005_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 5 :=
  of_group record015 5 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame005_indices record015_frame005_graph record015_frame005_links
def record015_frame006_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0759.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0759.count (({ width := 10, code := 0xbcef0bb6eab9ee4b82d9b56d1abeaba9ea3a7e9ba568aa0e7c9e2769ce719ba6b98e5c9524c7fdfd7edf97ddf57c5eb799e1715c3705bf6f5bb6d9ad69da166d9965d9564d916217f5e1714e1344c12d4a52647d174450b41903400fe3ecf93cceb398e1360d4340cc324c5304bd2e8b62ccad2949f2648f220831f8790e8390e0370d81e0741c06c1a0441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record015_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record015) (record015.maps 6) (record015.inverseMaps 6) record015_frame006_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0759.localPairCheck (smallEmbedding record015) (record015.maps 6)
      (record015.inverseMaps 6) record015_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame006_links_0000 record015_frame006_links_0064)
theorem record015_frame006_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 6 :=
  of_group record015 6 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0759
    Papers.RationalityTen.SharedFrameCatalogue.group0759_facts record015_frame006_indices record015_frame006_graph record015_frame006_links
def record015_frame007_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0200.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0200.count (({ width := 10, code := 0x7a1e5789df771d9759d3741cd6e1b56c9af6b1a96919f66995649906398c62988619836017d56557555535454f53149519434bd2d4ad2949d2548d204751a45914449104390c42505404fd35cd4344ce32cc8314c02ecb62c8b02b8ac2a8a8298a22789a258932408d22c8821884208801f87c1dc721b4681946217c5c0cc320c4300bc1b06819060170441003c0e0340c02c0a02408018050100300800 } : Fields).get c.val)
theorem record015_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record015) (record015.maps 7) (record015.inverseMaps 7) record015_frame007_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0200.localPairCheck (smallEmbedding record015) (record015.maps 7)
      (record015.inverseMaps 7) record015_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame007_links_0000 record015_frame007_links_0064)
theorem record015_frame007_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 7 :=
  of_group record015 7 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0200
    Papers.RationalityTen.SharedFrameCatalogue.group0200_facts record015_frame007_indices record015_frame007_graph record015_frame007_links
def record015_frame008_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x149aa3a510a8494049f14f127493829b5499246d2048ef46f23291708a7449a2190ea85d42320c904080f3ff1fb0fb67d232398c8c3a60e2ff97bcbc25d22e116d8a7c52a28a94149ee4ea26d133097e4b3252924c902471232115c89243c21790986a033a1920c5460c2f71740b645942bf1588a7451427813689804a424711d08c44442110ff87c83ca1d60e306d435019c0c806142f216d0b2055428412f09104580b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record015_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 8) (record015.inverseMaps 8) record015_frame008_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record015) (record015.maps 8)
      (record015.inverseMaps 8) record015_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame008_links_0000 record015_frame008_links_0064)
theorem record015_frame008_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 8 :=
  of_group record015 8 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record015_frame008_indices record015_frame008_graph record015_frame008_links
def record015_frame009_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0x290519a2943a82cfc9f13ce75ce293923e43c7f8e91aa31c5d8a71261d42c84d07608c07800fe5f83e66aad35a3340676cc595b27644c5d712d5594b155f2b5560aa952a9c524a1d402784e0999302584a892cf01d4396718e01b83666b8d49a1332638c31802f85d0b71682ca574ab94b2804e09812723644c879072023f47b0f21d83946d8d11923042684c0961282482104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record015_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record015) (record015.maps 9) (record015.inverseMaps 9) record015_frame009_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record015) (record015.maps 9)
      (record015.inverseMaps 9) record015_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame009_links_0000 record015_frame009_links_0064)
theorem record015_frame009_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 9 :=
  of_group record015 9 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record015_frame009_indices record015_frame009_graph record015_frame009_links
def record015_frame010_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0351.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0351.count (({ width := 9, code := 0x31588c36130580bf5f2f578b8dbad768b2582b958aa5429749a3d12833e9dce26b338a4461d0b8441604ff7e3e9e4ef763a5cae16eb65aad266b2d92c661b017aba5bad52e9549a451c8b44215047f3f1f4f87b3c9dcea73389bcdc6c351a0cc6431988c25f2e96cb2572a94ca04d2511c5c2d160ac541c0d86832180803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record015_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record015) (record015.maps 10) (record015.inverseMaps 10) record015_frame010_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0351.localPairCheck (smallEmbedding record015) (record015.maps 10)
      (record015.inverseMaps 10) record015_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame010_links_0000 record015_frame010_links_0064)
theorem record015_frame010_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 10 :=
  of_group record015 10 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0351
    Papers.RationalityTen.SharedFrameCatalogue.group0351_facts record015_frame010_indices record015_frame010_graph record015_frame010_links
def record015_frame011_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0699.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0699.count (({ width := 8, code := 0xd5d4d3d2d1d0cfcecdccc5c3c1bfbdbbb9b7b5b3b1b0afaeadacabaaa9a8969594939291908f8e8d868482807e7c7a7876747271706f6e6d6c6b6a695d5b59585655545251504f4d4b4a48474644434241403f3e3d3c3a383735343331302f2e2d2c2b2a232221201f1918171615100f0e0d0c0b0a090807060504030200 } : Fields).get c.val)
theorem record015_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record015) (record015.maps 11) (record015.inverseMaps 11) record015_frame011_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0699.localPairCheck (smallEmbedding record015) (record015.maps 11)
      (record015.inverseMaps 11) record015_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame011_links_0000 record015_frame011_links_0064)
theorem record015_frame011_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 11 :=
  of_group record015 11 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0699
    Papers.RationalityTen.SharedFrameCatalogue.group0699_facts record015_frame011_indices record015_frame011_graph record015_frame011_links
def record015_frame012_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1590ab45502a314eea6252828ed44ea134a4a4d524290f47ea3a91ae8c44582275110876432214908483040fa034ff67e92ca1600ad85582a194b8a38507279937c82a4011f68f6c7923b61d18e406f83691aa0d0866031e1870bf05d62d91638ad441e20810087e83e61ec0f287783ae1d00e487083761b40d6869833e1980c8862830217a0b985b02ca1600ac854829614409e84d825e128090846022210a08183f00b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record015_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 12) (record015.inverseMaps 12) record015_frame012_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record015) (record015.maps 12)
      (record015.inverseMaps 12) record015_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame012_links_0000 record015_frame012_links_0064)
theorem record015_frame012_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 12 :=
  of_group record015 12 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record015_frame012_indices record015_frame012_graph record015_frame012_links
def record015_frame013_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x5a159c59158b57e57956f56155a54f4f34ef4e54e14d54ce4c24b44ad4a149548f48347846c46545944a43c43036836135c35034a34033332b3213162ba2b42af2a529f29528827d27426825c25324a23d23522c21e2112031f718b18718117c17717116c16616115d15715414f14914313d13813212d12912311d11611110e10c10a1051000fb0f60f00ea0e50e00d80d20cd0c70c305205105004f04e02102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 13) (record015.inverseMaps 13) record015_frame013_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record015) (record015.maps 13)
      (record015.inverseMaps 13) record015_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame013_links_0000 record015_frame013_links_0064)
theorem record015_frame013_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 13 :=
  of_group record015 13 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record015_frame013_indices record015_frame013_graph record015_frame013_links
def record015_frame014_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0870.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0870.count (({ width := 12, code := 0x59058858257b57356655f5555485404f04e84e04d94d04c54ba4ae4a349a48c48548047847046645c45544843e38938137a37336836235734a3413382e92e02d82d12c62be2b22a429a29228427d27827026625f25424a2402361cb1c51bf1bc1b71b01aa1a419d19618f18918418017a17316c16615e15715114b14313d13913312c12712311d11610f1070ff0f90f10e90e10dc0d705305205105004f02102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record015) (record015.maps 14) (record015.inverseMaps 14) record015_frame014_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0870.localPairCheck (smallEmbedding record015) (record015.maps 14)
      (record015.inverseMaps 14) record015_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame014_links_0000 record015_frame014_links_0064)
theorem record015_frame014_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 14 :=
  of_group record015 14 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0870
    Papers.RationalityTen.SharedFrameCatalogue.group0870_facts record015_frame014_indices record015_frame014_graph record015_frame014_links
def record015_frame015_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0381.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0381.count (({ width := 9, code := 0x2271288c421f0e86c32170a81401fcfc7d3e1ecf4793c1daec75ba9d2e873b99cae469345a0cf6733598cb6532582bf5eaed72b75aacd62af562ad54a95429d4ca55228d208e46229108642a0d027f3e1e8f0763a1c8e06d3519cc86230178ba5b2c95caa532893c98492310c823f1e8f05228138984a190c05c2c150803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record015_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record015) (record015.maps 15) (record015.inverseMaps 15) record015_frame015_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0381.localPairCheck (smallEmbedding record015) (record015.maps 15)
      (record015.inverseMaps 15) record015_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame015_links_0000 record015_frame015_links_0064)
theorem record015_frame015_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 15 :=
  of_group record015 15 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0381
    Papers.RationalityTen.SharedFrameCatalogue.group0381_facts record015_frame015_indices record015_frame015_graph record015_frame015_links
def record015_frame016_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x5f45eb5e45db5d35ce5c65ba5af5a255054754053452d52651f5135084fb4ee4e84df4d94ce4c94c04b24a749a3ba3b03a83a239b39438c38037236831630b3042fc2f52ec2e52d92cb2c22b42ad2a229d29428f28627826a25f1e11d91d01c81bf1b91b61af1a81a019819018817f17717016c16615f15714d14814013713012d12812211c11611010d1081010f90f10ec0e60df0d805705605505405302102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record015) (record015.maps 16) (record015.inverseMaps 16) record015_frame016_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record015) (record015.maps 16)
      (record015.inverseMaps 16) record015_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame016_links_0000 record015_frame016_links_0064)
theorem record015_frame016_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 16 :=
  of_group record015 16 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record015_frame016_indices record015_frame016_graph record015_frame016_links
def record015_frame017_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0758.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0758.count (({ width := 9, code := 0x231178b45629138943e1b0b7f3f1f4f87b3d1e2ec74b99c8e371385c0df6eb69b0d65cae16eb65aad166b0572b13e9d4da652e9549235148742a11068240a00fc7b3c9dcd26732990c46130178ba5c2d964ae562a14ca450279389a4c259289248231108641200fc7a3c1d8e470371b0d44c251208c44190c05c2c150803c1c0d0602c14090401c0c050200c0400 } : Fields).get c.val)
theorem record015_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record015) (record015.maps 17) (record015.inverseMaps 17) record015_frame017_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0758.localPairCheck (smallEmbedding record015) (record015.maps 17)
      (record015.inverseMaps 17) record015_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame017_links_0000 record015_frame017_links_0064)
theorem record015_frame017_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 17 :=
  of_group record015 17 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0758
    Papers.RationalityTen.SharedFrameCatalogue.group0758_facts record015_frame017_indices record015_frame017_graph record015_frame017_links
def record015_frame018_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0199.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0199.count (({ width := 8, code := 0xa7a6a5a4a3a2a1a09f9e9d9b99979593918f8d8b898887868584838281807a797877767574737271706e6c6a68666462605e5c5b5a595857565554534d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827261f1e1d1c1b1514131211100f0e0d0c0b0a090807060504030200 } : Fields).get c.val)
theorem record015_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0199.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record015) (record015.maps 18) (record015.inverseMaps 18) record015_frame018_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0199.localPairCheck (smallEmbedding record015) (record015.maps 18)
      (record015.inverseMaps 18) record015_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame018_links_0000 record015_frame018_links_0064)
theorem record015_frame018_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 18 :=
  of_group record015 18 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0199
    Papers.RationalityTen.SharedFrameCatalogue.group0199_facts record015_frame018_indices record015_frame018_graph record015_frame018_links
def record015_frame019_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x5d25ce5c45bb5b25a859d59258657d52e52351650a4ff4f54e84db4ce4c44bc4b34aa49f49949248847f47546e39639238837e37336735d35434a3412f22e72da2cc2bf2b22a729c29228828027726e26225924f2462402392321c11bb1b41ae1a619e19618e18617f17d17917216b16515d15514f14714013c13813312e12712311e11a11410d1071000f90f30ed0e90e40de0d90d305805705605505402102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame019_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame019_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame019_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 19) (record015.inverseMaps 19) record015_frame019_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame019_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record015) (record015.maps 19)
      (record015.inverseMaps 19) record015_frame019_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame019_links_0000 record015_frame019_links_0064)
theorem record015_frame019_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 19 :=
  of_group record015 19 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record015_frame019_indices record015_frame019_graph record015_frame019_links
def record015_frame020_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0938.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0938.count (({ width := 9, code := 0x2d96bb4d9ecb63b0d7ebb5ba6d268d429fcee7336994c25d2b954a24f259248e43207ebf1f4f87b3d1e4f0773b1bcda6bb4da0cc6531d86c15faf176b95c2d96ab4592c534984b24d228e46a2d10874320d027f3e9ecf4783b1d4e470371b0d46933190c4602f174b6592c154a450271306833190c4601e0e870361a088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record015_frame020_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame020_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame020_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 20) (record015.inverseMaps 20) record015_frame020_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame020_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0938.localPairCheck (smallEmbedding record015) (record015.maps 20)
      (record015.inverseMaps 20) record015_frame020_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame020_links_0000 record015_frame020_links_0064)
theorem record015_frame020_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 20 :=
  of_group record015 20 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0938
    Papers.RationalityTen.SharedFrameCatalogue.group0938_facts record015_frame020_indices record015_frame020_graph record015_frame020_links
def record015_frame021_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0698.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0698.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record015_frame021_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0698.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame021_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0698.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame021_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0698.localPairCheck (smallEmbedding record015) (record015.maps 21) (record015.inverseMaps 21) record015_frame021_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame021_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0698.localPairCheck (smallEmbedding record015) (record015.maps 21)
      (record015.inverseMaps 21) record015_frame021_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame021_links_0000 record015_frame021_links_0064)
theorem record015_frame021_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 21 :=
  of_group record015 21 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0698
    Papers.RationalityTen.SharedFrameCatalogue.group0698_facts record015_frame021_indices record015_frame021_graph record015_frame021_links
def record015_frame022_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0087.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0087.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record015_frame022_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0087.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame022_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0087.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame022_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0087.localPairCheck (smallEmbedding record015) (record015.maps 22) (record015.inverseMaps 22) record015_frame022_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame022_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0087.localPairCheck (smallEmbedding record015) (record015.maps 22)
      (record015.inverseMaps 22) record015_frame022_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame022_links_0000 record015_frame022_links_0064)
theorem record015_frame022_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 22 :=
  of_group record015 22 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0087
    Papers.RationalityTen.SharedFrameCatalogue.group0087_facts record015_frame022_indices record015_frame022_graph record015_frame022_links
def record015_frame023_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1624b005772b6d58eab35502a314f6a694d3265130496f4ada51d268920487a3f51dc8e747023651a48cb46222f516c8af3639adcd4c69434219d4cc464f31e18acae45622a894fca5e52028693e89ce4d626393009724b2256129493c49724812246fe36a1ab8d046583191820bc05b42c715c8aa453228a13d09ac4b624c11e08b443620c0ff07c03c41d60e306d834e1970c405e02d21590a504e025211b08683fc0b205802b81580aa021010007c03c01d008804001e00e006803001600a004802000c005002000c004000 } : Fields).get c.val)
theorem record015_frame023_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame023_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame023_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 23) (record015.inverseMaps 23) record015_frame023_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame023_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record015) (record015.maps 23)
      (record015.inverseMaps 23) record015_frame023_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame023_links_0000 record015_frame023_links_0064)
theorem record015_frame023_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 23 :=
  of_group record015 23 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record015_frame023_indices record015_frame023_graph record015_frame023_links
def record015_frame024_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x6a169768b68167867266865764d6415e65dd5d45cc5c05b75ad59c59258757b57456d56655f55955454d54653f44643a4304244194104063f53e83dd37936f36435934f34333932831b3103062ff2f82f12ea2e42df2d82d12ca23c23222421a20c2041f51ea1de1d41cb1c31bc1b51ae1a81a119718f18617a16e16715e15614b14313c13512e12812111710d1070fa0ee0e50e00d605905805705605502102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame024_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame024_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame024_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 24) (record015.inverseMaps 24) record015_frame024_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame024_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record015) (record015.maps 24)
      (record015.inverseMaps 24) record015_frame024_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame024_links_0000 record015_frame024_links_0064)
theorem record015_frame024_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 24 :=
  of_group record015 24 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record015_frame024_indices record015_frame024_graph record015_frame024_links
def record015_frame025_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0754.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0754.count (({ width := 9, code := 0x2d769b3d92c55fae56ab156a451a89419fcf273379acce632f96cae53279248239187f3f1f4f87b3d1e4ef763a5b4d86b351a4d06732d90c560afd7abb5cadd68b0562a124904723114884321104803f9f8fa7c3d9e8f276399c0d86a34198c86230980be5e2e970b2562993c9a4b2491c5c2d160ac54170b0542813088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record015_frame025_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame025_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record015) (record015.maps 25) (record015.inverseMaps 25) record015_frame025_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame025_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record015) (record015.maps 25) (record015.inverseMaps 25) record015_frame025_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame025_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0754.localPairCheck (smallEmbedding record015) (record015.maps 25)
      (record015.inverseMaps 25) record015_frame025_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame025_links_0000 record015_frame025_links_0064)
theorem record015_frame025_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 25 :=
  of_group record015 25 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0754
    Papers.RationalityTen.SharedFrameCatalogue.group0754_facts record015_frame025_indices record015_frame025_graph record015_frame025_links
def record015_frame026_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0195.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0195.count (({ width := 9, code := 0x22f1589c461f0d85c260f057ebedf2f77abcde2ef76badd2e772b8dc2df6eb69aed463b1586c15faf576b95bad55aab54a9d4aa350a7d3a9b4c259289248239168842a08ea73389bcda6b3499cca6331184c05f2f174b85a2c158a85228138984a249208e462291084401f0f074381b0d04622108803e14098482210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record015_frame026_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0195.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame026_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record015) (record015.maps 26) (record015.inverseMaps 26) record015_frame026_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame026_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record015) (record015.maps 26) (record015.inverseMaps 26) record015_frame026_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame026_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0195.localPairCheck (smallEmbedding record015) (record015.maps 26)
      (record015.inverseMaps 26) record015_frame026_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame026_links_0000 record015_frame026_links_0064)
theorem record015_frame026_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 26 :=
  of_group record015 26 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0195
    Papers.RationalityTen.SharedFrameCatalogue.group0195_facts record015_frame026_indices record015_frame026_graph record015_frame026_links
def record015_frame027_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1109.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1109.count (({ width := 12, code := 0x71a7117076fa6f06e66d66ca6bf6b262261960e6005f45e85d55c75b95a859758e58657e57656e56655e55554c42841f4144063fa3ee3db3cd3bf3ae32c32331930c3022f82e82dc2d12c42b42ab2a329b29328b28327b2722691fa1f31ec1e61df1d81d11ca1c31bd1b71b01a81a119919018818117917116716015915114a14513e13612f12711e11610f1070ff0f50ee0e70df0d805905805705605502102001f01e01d01101000f00e00d00c00b00a009008006005004003002000 } : Fields).get c.val)
theorem record015_frame027_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame027_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 27) (record015.inverseMaps 27) record015_frame027_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame027_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 27) (record015.inverseMaps 27) record015_frame027_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame027_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1109.localPairCheck (smallEmbedding record015) (record015.maps 27)
      (record015.inverseMaps 27) record015_frame027_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame027_links_0000 record015_frame027_links_0064)
theorem record015_frame027_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 27 :=
  of_group record015 27 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1109
    Papers.RationalityTen.SharedFrameCatalogue.group1109_facts record015_frame027_indices record015_frame027_graph record015_frame027_links
def record015_frame028_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0864.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0864.count (({ width := 11, code := 0x217c2984d07e0cc11819015fe3f6798f21e03b9766eadd339d728e2dc0b7c6eedc1b53646bed69a9b4f5c0b696a2cd58ab055d2b154ea7d3c2754de9a13025c4aa9312323f46c8c51622543c8690a20e410810d61a533e670cb191318610be1762e05a8b295f2b0544a61472804ec9992e2484748b911218418800f81e43b4738e11b8350668c617c2e02804f09c1342602104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record015_frame028_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame028_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record015) (record015.maps 28) (record015.inverseMaps 28) record015_frame028_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame028_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record015) (record015.maps 28) (record015.inverseMaps 28) record015_frame028_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame028_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0864.localPairCheck (smallEmbedding record015) (record015.maps 28)
      (record015.inverseMaps 28) record015_frame028_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame028_links_0000 record015_frame028_links_0064)
theorem record015_frame028_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 28 :=
  of_group record015 28 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0864
    Papers.RationalityTen.SharedFrameCatalogue.group0864_facts record015_frame028_indices record015_frame028_graph record015_frame028_links
def record015_frame029_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0376.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0376.count (({ width := 9, code := 0x2210e8642a110682405fcfc7abcde2ef76badd2e671b85badb6cb5daad368b3d9acc5f2f174b85b2d164af562a946a14fa7536994ba51228f45a250e8541a04fe7d3d9e8da6c359a8d26833994c6613017cbc5d2e16cb4582b150a45027134964a249208e462291084401f0f074381b8d44c251208c441b0d0643017088401e0e06830160a048200c050200c0400 } : Fields).get c.val)
theorem record015_frame029_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame029_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record015) (record015.maps 29) (record015.inverseMaps 29) record015_frame029_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame029_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record015) (record015.maps 29) (record015.inverseMaps 29) record015_frame029_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame029_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0376.localPairCheck (smallEmbedding record015) (record015.maps 29)
      (record015.inverseMaps 29) record015_frame029_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame029_links_0000 record015_frame029_links_0064)
theorem record015_frame029_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 29 :=
  of_group record015 29 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0376
    Papers.RationalityTen.SharedFrameCatalogue.group0376_facts record015_frame029_indices record015_frame029_graph record015_frame029_links
def record015_frame030_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x21542684306e0ac1281b015ffbf8778ee5d9bad74ce81cd391712df9bb36f6d2d91af3596a6d2da233c56aac5552a6540a6549a8a5009e12123e4708d51822a44a8750aa0f410804fd9f73e27acf29dd3aa738c197e2f05c8b61662c8584ae9582a6534a414327e4e89b1302544888d11622442c821001f63dc790ed1ce38c6e8d619e31c618bd1722c42704d09812c2502104007c0f01d0220400780e01a0300580a0120200300500800c01000 } : Fields).get c.val)
theorem record015_frame030_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame030_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 30) (record015.inverseMaps 30) record015_frame030_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame030_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 30) (record015.inverseMaps 30) record015_frame030_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame030_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record015) (record015.maps 30)
      (record015.inverseMaps 30) record015_frame030_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame030_links_0000 record015_frame030_links_0064)
theorem record015_frame030_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 30 :=
  of_group record015 30 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record015_frame030_indices record015_frame030_graph record015_frame030_links
def record015_frame031_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0753.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0753.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record015_frame031_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0753.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame031_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0753.localPairCheck (smallEmbedding record015) (record015.maps 31) (record015.inverseMaps 31) record015_frame031_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame031_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0753.localPairCheck (smallEmbedding record015) (record015.maps 31) (record015.inverseMaps 31) record015_frame031_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame031_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0753.localPairCheck (smallEmbedding record015) (record015.maps 31)
      (record015.inverseMaps 31) record015_frame031_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame031_links_0000 record015_frame031_links_0064)
theorem record015_frame031_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 31 :=
  of_group record015 31 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0753
    Papers.RationalityTen.SharedFrameCatalogue.group0753_facts record015_frame031_indices record015_frame031_graph record015_frame031_links
def record015_frame032_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0194.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0194.count (({ width := 7, code := 0x3efcf7ebcf8efdbaf4e7cb8f0dfbb6ecd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record015_frame032_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0194.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame032_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0194.localPairCheck (smallEmbedding record015) (record015.maps 32) (record015.inverseMaps 32) record015_frame032_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame032_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0194.localPairCheck (smallEmbedding record015) (record015.maps 32) (record015.inverseMaps 32) record015_frame032_indices (Fin.ofNat record015.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record015_frame032_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0194.localPairCheck (smallEmbedding record015) (record015.maps 32)
      (record015.inverseMaps 32) record015_frame032_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record015_frame032_links_0000 record015_frame032_links_0064)
theorem record015_frame032_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) : Supported record015 32 :=
  of_group record015 32 (smallEmbedding record015) (small_cells_exact record015 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0194
    Papers.RationalityTen.SharedFrameCatalogue.group0194_facts record015_frame032_indices record015_frame032_graph record015_frame032_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSmall.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (Fin.cases (record015_frame002_supported hcells) (Fin.cases (record015_frame003_supported hcells) (Fin.cases (record015_frame004_supported hcells) (Fin.cases (record015_frame005_supported hcells) (Fin.cases (record015_frame006_supported hcells) (Fin.cases (record015_frame007_supported hcells) (Fin.cases (record015_frame008_supported hcells) (Fin.cases (record015_frame009_supported hcells) (Fin.cases (record015_frame010_supported hcells) (Fin.cases (record015_frame011_supported hcells) (Fin.cases (record015_frame012_supported hcells) (Fin.cases (record015_frame013_supported hcells) (Fin.cases (record015_frame014_supported hcells) (Fin.cases (record015_frame015_supported hcells) (Fin.cases (record015_frame016_supported hcells) (Fin.cases (record015_frame017_supported hcells) (Fin.cases (record015_frame018_supported hcells) (Fin.cases (record015_frame019_supported hcells) (Fin.cases (record015_frame020_supported hcells) (Fin.cases (record015_frame021_supported hcells) (Fin.cases (record015_frame022_supported hcells) (Fin.cases (record015_frame023_supported hcells) (Fin.cases (record015_frame024_supported hcells) (Fin.cases (record015_frame025_supported hcells) (Fin.cases (record015_frame026_supported hcells) (Fin.cases (record015_frame027_supported hcells) (Fin.cases (record015_frame028_supported hcells) (Fin.cases (record015_frame029_supported hcells) (Fin.cases (record015_frame030_supported hcells) (Fin.cases (record015_frame031_supported hcells) (Fin.cases (record015_frame032_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))))))))))))))))
#print axioms record015_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086

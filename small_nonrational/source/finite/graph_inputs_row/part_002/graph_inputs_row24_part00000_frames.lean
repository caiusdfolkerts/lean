module
prelude
public import GraphInputsRow24Part00000Data
public import RawFrameSupport
public import SharedFrameGroups002Checked
public import SharedFrameGroups003Checked
public import SharedFrameGroups004Checked
public import SharedFrameGroups005Checked
public import SharedFrameGroups007Checked
public import SharedFrameGroups010Checked
public import SharedFrameGroups013Checked
public import SharedFrameGroups018Checked
public import SharedFrameGroups020Checked
public import SharedFrameGroups022Checked
public import SharedFrameGroups023Checked
public import SharedFrameGroups026Checked
public import SharedFrameGroups027Checked
public import SharedFrameGroups028Checked
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups044Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups050Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups064Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups076Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups085Checked
public import SharedFrameGroups090Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x342d95eb945c0ad11594a474e2a19908877b3301934c2059628992446643100dc86ac33017c0a8850c25012108604141de0e9071034416408c04401a40c605a02a81500a0031015808803a01c00c805c02c00d005802000e0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 59 :=
  interval_of_check _ 0 59 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ record000_frame001_links_0000
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (smallEmbedding record000) (small_cells_exact record000 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSmall.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
def record001_frame001_indices (c : Fin record001.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7b274e6f36e46cb6966626346296005cb5a756f56155a5144863b92f72e92e52d82bd2a529a28c28627525e23521d1f11ba1af1a718f16913d12c1271070e20c80c40c10b308a08707b06905a05505405003d03102c02202001d01c01600d00a008007003002001000 } : Fields).get c.val)
theorem record001_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record001.data.requiredEdges q = true := by decide +kernel
theorem record001_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record001_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1) (record001.inverseMaps 1) record001_frame001_indices (Fin.ofNat record001.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record001_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record001) (record001.maps 1)
      (record001.inverseMaps 1) record001_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record001_frame001_links_0000 record001_frame001_links_0064)
theorem record001_frame001_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) : Supported record001 1 :=
  of_group record001 1 (smallEmbedding record001) (small_cells_exact record001 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record001_frame001_indices record001_frame001_graph record001_frame001_links
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSmall.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (Fin.cases (record001_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0869.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0869.count (({ width := 11, code := 0xc1750e5d454891109d5397722e15b0355658c0d7e2f65bab19582914cc9652ba4444e800fe9f03bc704d89922ce578aa93d2444107c0f31ba31c5b0b215e2843e0620b41542a0530a41442804307a0c4160220400740e01601a0280400700600800800 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0869.localPairCheck (smallEmbedding record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0869
    Papers.RationalityTen.SharedFrameCatalogue.group0869_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
def record002_frame002_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0779.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0779.count (({ width := 8, code := 0xcfbdb0a19f9e908f8e8d8b8a878281807f7d7c797371706e6a65646362605f5c565453504c474544403c39383736302a242221201f1e1d1c1b1615100f0e0d0c0706050403020100 } : Fields).get c.val)
theorem record002_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record002) (record002.maps 2) (record002.inverseMaps 2) record002_frame002_indices (Fin.ofNat record002.n i)) 64 72 :=
  interval_of_check _ 64 8 (by decide +kernel)
theorem record002_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0779.localPairCheck (smallEmbedding record002) (record002.maps 2)
      (record002.inverseMaps 2) record002_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 72 record002_frame002_links_0000 record002_frame002_links_0064)
theorem record002_frame002_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) : Supported record002 2 :=
  of_group record002 2 (smallEmbedding record002) (small_cells_exact record002 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0779
    Papers.RationalityTen.SharedFrameCatalogue.group0779_facts record002_frame002_indices record002_frame002_graph record002_frame002_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (Fin.cases (record002_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3e01a1ccaf502a7d13aa9c54d3a60d26e911467219908877b2689300942491239913c8063dd1cd0cc86201b90d586602f81510a184a024210c08283bc1d20e206882b013c08c04401a40c605a02a81500a0031015808803a01c00c805c02c00d005802000e0040018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 67 :=
  interval_of_check _ 64 3 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 67 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (smallEmbedding record003) (small_cells_exact record003 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSmall.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x1dd28313db9e90ee66f834019b0c0a5f42ea16b8aa252d25712709144792290ffc72c3851b28cfc5c42be11f88b443620a0f1864023c11708203f41c60dd06702300d206302d01540a805302901440a003f01c80d006202b0110074038016006802000e0040018008002000 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 66 :=
  interval_of_check _ 64 2 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 66 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (smallEmbedding record006) (small_cells_exact record006 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
def record007_frame001_indices (c : Fin record007.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x730344195eb925b72cbd53e9f44f1260d1f887d42ba0c903277b32f18e8bf656b26012b889e3c81a48c8c5fc2e50ff87c43bc1ba0d206442f61750a184f024211208283a01c40d104a023011006902d01540a8050018808803a01c00c805c02c01000680280100070018008002000 } : Fields).get c.val)
theorem record007_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record007.data.requiredEdges q = true := by decide +kernel
theorem record007_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record007_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1) (record007.inverseMaps 1) record007_frame001_indices (Fin.ofNat record007.n i)) 64 68 :=
  interval_of_check _ 64 4 (by decide +kernel)
theorem record007_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record007) (record007.maps 1)
      (record007.inverseMaps 1) record007_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 68 record007_frame001_links_0000 record007_frame001_links_0064)
theorem record007_frame001_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) : Supported record007 1 :=
  of_group record007 1 (smallEmbedding record007) (small_cells_exact record007 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record007_frame001_indices record007_frame001_graph record007_frame001_links
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSmall.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (Fin.cases (record007_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7677006f169f67966a6476055a058757d51d4c44b749b4553f03a338c35a33d2fb2d62cc2be2b62a929225d2492041f31db1d21c419816514f14611a1050f50d20ca0b508608307206e06605705205104e03002c02502201d01c01600d00a008007003002001000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 69 :=
  interval_of_check _ 64 5 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 69 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (smallEmbedding record008) (small_cells_exact record008 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
def record009_frame001_indices (c : Fin record009.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x133660c61844f85bb353690ce5903125ecb7d6aad357ea4d412754d899d2ea5847885907a043e6730dd9812ec598af95526a450810fc1ba334610a9144250420670b41542a0530a41442803e0720c4160250440740e01601a0280400700600800800 } : Fields).get c.val)
theorem record009_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record009.data.requiredEdges q = true := by decide +kernel
theorem record009_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record009_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record009) (record009.maps 1) (record009.inverseMaps 1) record009_frame001_indices (Fin.ofNat record009.n i)) 64 71 :=
  interval_of_check _ 64 7 (by decide +kernel)
theorem record009_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record009) (record009.maps 1)
      (record009.inverseMaps 1) record009_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 71 record009_frame001_links_0000 record009_frame001_links_0064)
theorem record009_frame001_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) : Supported record009 1 :=
  of_group record009 1 (smallEmbedding record009) (small_cells_exact record009 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record009_frame001_indices record009_frame001_graph record009_frame001_links
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSmall.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (Fin.cases (record009_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x52ba3b2ce35c17821026043f17c8f31ddba1710e01a0acd54aa794ea9051c9f52aa43454858f41d239c718df9b5352630bf946268464859092083e87a0f01d0358630bb1502904c08f0f81e43005c0b21482684c0900c0158250440740e01601a0280400700600800800 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
def record010_frame002_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x5f0ba34f672c8b90b2063fc6a8b10ee174077d8f91d5b32612bf17d2f25e0b69542964dc96511a0e40c7ecfb9ef3be6ccd295227c4888910b2083f47c0f31d8368678c51582a04c88b0f21dc328610c0160298520a00c4160250440740e01601a0280400700600800800 } : Fields).get c.val)
theorem record010_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record010) (record010.maps 2) (record010.inverseMaps 2) record010_frame002_indices (Fin.ofNat record010.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record010_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (smallEmbedding record010) (record010.maps 2)
      (record010.inverseMaps 2) record010_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record010_frame002_links_0000 record010_frame002_links_0064)
theorem record010_frame002_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 2 :=
  of_group record010 2 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record010_frame002_indices record010_frame002_graph record010_frame002_links
def record010_frame003_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0354.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0354.count (({ width := 7, code := 0x62c382fdebb72dd9b15eb55a94e951a13e74d992e4c88f1a2c4870a0c07ef9ebb74e5c376cd5a3364c582f5cb562a4c950a03e70d1930509911e3460b101c2840608080 } : Fields).get c.val)
theorem record010_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0354.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0354.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0354.localPairCheck (smallEmbedding record010) (record010.maps 3) (record010.inverseMaps 3) record010_frame003_indices (Fin.ofNat record010.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record010_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0354.localPairCheck (smallEmbedding record010) (record010.maps 3)
      (record010.inverseMaps 3) record010_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record010_frame003_links_0000 record010_frame003_links_0064)
theorem record010_frame003_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 3 :=
  of_group record010 3 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0354
    Papers.RationalityTen.SharedFrameCatalogue.group0354_facts record010_frame003_indices record010_frame003_graph record010_frame003_links
def record010_frame004_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0436.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0436.count (({ width := 7, code := 0x4c972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record010_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0436.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0436.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0436.localPairCheck (smallEmbedding record010) (record010.maps 4) (record010.inverseMaps 4) record010_frame004_indices (Fin.ofNat record010.n i)) 64 77 :=
  interval_of_check _ 64 13 (by decide +kernel)
theorem record010_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0436.localPairCheck (smallEmbedding record010) (record010.maps 4)
      (record010.inverseMaps 4) record010_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 77 record010_frame004_links_0000 record010_frame004_links_0064)
theorem record010_frame004_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) : Supported record010 4 :=
  of_group record010 4 (smallEmbedding record010) (small_cells_exact record010 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0436
    Papers.RationalityTen.SharedFrameCatalogue.group0436_facts record010_frame004_indices record010_frame004_graph record010_frame004_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSmall.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (Fin.cases (record010_frame002_supported hcells) (Fin.cases (record010_frame003_supported hcells) (Fin.cases (record010_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x6ad60a5d85cf5a85564db45a4173e63b33ab38236534933530a2ee2e02a329a29228727b2672382242091dd1c21a518b18717316815214513912b1070f30e40be0b609f08007c06305605105004f04e04d04c03102d02a02201d01c01901701601000d00a008007003002001000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 73 :=
  interval_of_check _ 64 9 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 73 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (smallEmbedding record011) (small_cells_exact record011 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSmall.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0634.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0634.count (({ width := 11, code := 0x2f2db7b1d4ae794907f6f1dceb43632b352d25348c8b10fa103fc7e0ef1d33666a8cc97b2e44e4971222323fc768db16a2a44a07e0fa1f03d87a0c61582885009e1382684c0620880e81c0360680c81802e0580a81001a0280400700600800800 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0634.localPairCheck (smallEmbedding record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0634
    Papers.RationalityTen.SharedFrameCatalogue.group0634_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
def record012_frame002_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x68763e60a5a75564db45a4173e63853492ee2842782642442382242112091e31dd1c21b61a518b18715414513912d1070f30e40be0b609f08007f07e07d07c06305605105004f04e04d04c03102201d01c01b01a01901801701601501000d00a008007003002001000 } : Fields).get c.val)
theorem record012_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 2) (record012.inverseMaps 2) record012_frame002_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (smallEmbedding record012) (record012.maps 2)
      (record012.inverseMaps 2) record012_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame002_links_0000 record012_frame002_links_0064)
theorem record012_frame002_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 2 :=
  of_group record012 2 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record012_frame002_indices record012_frame002_graph record012_frame002_links
def record012_frame003_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x7226cb68a6005bf55a4d547042f39434e2e527b27025923b22220a1f41ea1c21bb1a71a018f16f16913412d1271201070ef0e20c40c10b308a08908808708606905a05505405305205105003102201d01c01b01a01901801701601501000d00a008007003002001000 } : Fields).get c.val)
theorem record012_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3) (record012.inverseMaps 3) record012_frame003_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record012) (record012.maps 3)
      (record012.inverseMaps 3) record012_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame003_links_0000 record012_frame003_links_0064)
theorem record012_frame003_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 3 :=
  of_group record012 3 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record012_frame003_indices record012_frame003_graph record012_frame003_links
def record012_frame004_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0063.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0063.count (({ width := 7, code := 0x22c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0063.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0063.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0063.localPairCheck (smallEmbedding record012) (record012.maps 4) (record012.inverseMaps 4) record012_frame004_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0063.localPairCheck (smallEmbedding record012) (record012.maps 4)
      (record012.inverseMaps 4) record012_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame004_links_0000 record012_frame004_links_0064)
theorem record012_frame004_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 4 :=
  of_group record012 4 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0063
    Papers.RationalityTen.SharedFrameCatalogue.group0063_facts record012_frame004_indices record012_frame004_graph record012_frame004_links
def record012_frame005_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1812b2c54fa6011f883236a97e0ad644c1e40bf846e23011108383fe1f10f207783821ba0d2067832217b0ba852828613c09a848422410507403881a208c045822811208803481680aa05402981480a2050018808803a01c00d806803201800b805802a01000680280100070018008002000 } : Fields).get c.val)
theorem record012_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 5) (record012.inverseMaps 5) record012_frame005_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record012) (record012.maps 5)
      (record012.inverseMaps 5) record012_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame005_links_0000 record012_frame005_links_0064)
theorem record012_frame005_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 5 :=
  of_group record012 5 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record012_frame005_indices record012_frame005_graph record012_frame005_links
def record012_frame006_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x24c46b882fcde5b8864cbd966a7c4ae858dc9b234e654c497d2e45acae15628c5049a11f2323f07b0f01d2358638bb1502904c07c0f61e83c8780c01482684c096128248480600880e81c0360680c81802e0580a81001a0280400700600800800 } : Fields).get c.val)
theorem record012_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 6) (record012.inverseMaps 6) record012_frame006_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record012) (record012.maps 6)
      (record012.inverseMaps 6) record012_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame006_links_0000 record012_frame006_links_0064)
theorem record012_frame006_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 6 :=
  of_group record012 6 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record012_frame006_indices record012_frame006_graph record012_frame006_links
def record012_frame007_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0356.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0356.count (({ width := 7, code := 0x22c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record012_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0356.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0356.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0356.localPairCheck (smallEmbedding record012) (record012.maps 7) (record012.inverseMaps 7) record012_frame007_indices (Fin.ofNat record012.n i)) 64 70 :=
  interval_of_check _ 64 6 (by decide +kernel)
theorem record012_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0356.localPairCheck (smallEmbedding record012) (record012.maps 7)
      (record012.inverseMaps 7) record012_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 70 record012_frame007_links_0000 record012_frame007_links_0064)
theorem record012_frame007_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) : Supported record012 7 :=
  of_group record012 7 (smallEmbedding record012) (small_cells_exact record012 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0356
    Papers.RationalityTen.SharedFrameCatalogue.group0356_facts record012_frame007_indices record012_frame007_graph record012_frame007_links
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
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x19b8bd15e4aee56d4ad952ea9353fc96d475a3111508783be1dd0eca708341187cc205b3296931492e47c23111308504171c88c605b22c715f0ab453628e13e08ec3e21db0e506e03561990ac04381ea0ef068826811808903481680b205502a01400620220100074038016009803801a0080038008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
def record014_frame002_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x62c5ec5e45df5ca5895455405234df4934594263f33b33ab3a638b34830c3072e229d25a2111e11bc1ba1b41af18f17016015d15815515014a14412c11210d10b1061010fc0e40c80bd0b70a508a07e07c06205305204e04d04b03102202001d01c01601300e00d008007002001000 } : Fields).get c.val)
theorem record014_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 2) (record014.inverseMaps 2) record014_frame002_indices (Fin.ofNat record014.n i)) 64 74 :=
  interval_of_check _ 64 10 (by decide +kernel)
theorem record014_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record014) (record014.maps 2)
      (record014.inverseMaps 2) record014_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 74 record014_frame002_links_0000 record014_frame002_links_0064)
theorem record014_frame002_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) : Supported record014 2 :=
  of_group record014 2 (smallEmbedding record014) (small_cells_exact record014 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record014_frame002_indices record014_frame002_graph record014_frame002_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSmall.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (Fin.cases (record014_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x21ec2e83cf15ab2d0596b1d602be578ab15429150c9f93da644b08b511a1641e7fcf89cc388704d99ad32663cc59802f65ccb796b2cc4e89091c21a418730e21ae338600ba14a268468890b613c2484808e118218360680bc158280460740e00f01c0280400700600800800 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x71162e62b6286145cb54553c52950d5084ed4dd49045840d4063fb3f53f23ef3d938c30c3032f02d92cb2ad29b24b2101d41cd1c21bc1ba1b81b31ad1a91a319d19717112d11211010d10b1060fd0f80ed0e70e00ce0c50b40b109509406405e05b05404e04d03302c02902301d01c00f00e00a008007003002001000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x6fe65f65664d6225d057d57155a5495445275124d04a547747146c46945e45341a3c037a36b35033e33731a30b2d62b429a29729429028527826c26125424823f2371f318616616215d15214713812f1191101010e60dc0c00ba09d09b06906306005905305203302c02902301d01c00f00e00a008007003002001000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0590.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0590.count (({ width := 11, code := 0x10cdefbdc7b2f35d4b646c2d61a6b4a678cd589af95b6b55682cd594b1d592954a49392323e46a8910c1f63c2724e11be3746d8d89aa34c680ce99531e5b4911041fa3e07a0ee1c83806c0d11942f0580a01342104185e0b415c2804a0920c4160290460740e00f01c0280400700600800800 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0590.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0590
    Papers.RationalityTen.SharedFrameCatalogue.group0590_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x70265d65464c6195c757856154b54347747146c46045545042641a3cc3c036c35133c3383243132e02bc29a29729428b27d27726825925324423e23620b1fb1f31b318e18616616215a15013a13111b1121010e60dc0c00ba06905905305205105004d03302d02a02301d01c01901701400f00e00a008007003002001000 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0x9ff9fa9f59dd9d797696c86e85f6c56b46a269769268e67466d6126095215143c43b73a838837d36b35e35034331f3123042f42e72952852482382281da1cd19f19017216414611b0fe0da0ce08508408306905905305205105004f03302301d01c01b01a01901801701501400f00e00a008007003002001000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
def record019_frame002_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x65864f6496226195d05c754a54347747146c46045545042641a3cc3c033d33829a29729427326824f24423d23621820b2021fb1f31c01b319518e18616616213c13111d1121010e60dc0c00ba08508408106905905305205105004d03302301d01c01b01a01901801701501400f00e00a008007003002001000 } : Fields).get c.val)
theorem record019_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record019) (record019.maps 2) (record019.inverseMaps 2) record019_frame002_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (smallEmbedding record019) (record019.maps 2)
      (record019.inverseMaps 2) record019_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame002_links_0000 record019_frame002_links_0064)
theorem record019_frame002_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 2 :=
  of_group record019 2 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record019_frame002_indices record019_frame002_graph record019_frame002_links
def record019_frame003_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0x74f74a74673172a6cb6c16005f652952251c51550c5054e54df47046739438b2b62b02ab28e28727026325924c23122321920b2041c21bb1a019618f15f15813412d1201161070e60d80c40c108908808506b05b05505405305204f03302301d01c01b01a01901801701501400f00e00a008007003002001000 } : Fields).get c.val)
theorem record019_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record019) (record019.maps 3) (record019.inverseMaps 3) record019_frame003_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (smallEmbedding record019) (record019.maps 3)
      (record019.inverseMaps 3) record019_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame003_links_0000 record019_frame003_links_0064)
theorem record019_frame003_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 3 :=
  of_group record019 3 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record019_frame003_indices record019_frame003_graph record019_frame003_links
def record019_frame004_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0927.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0927.count (({ width := 9, code := 0x133984b6552791c82250f7c3ddecf4793c1daea7338daad25d2e570b0572a54ea551a71329649a490e843f9f0f672381a8ce622f970ac5327130803f1e8d4622e168b056291087434190c05c2c150a048220c058200e06018080200 } : Fields).get c.val)
theorem record019_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record019) (record019.maps 4) (record019.inverseMaps 4) record019_frame004_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0927.localPairCheck (smallEmbedding record019) (record019.maps 4)
      (record019.inverseMaps 4) record019_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame004_links_0000 record019_frame004_links_0064)
theorem record019_frame004_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 4 :=
  of_group record019 4 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0927
    Papers.RationalityTen.SharedFrameCatalogue.group0927_facts record019_frame004_indices record019_frame004_graph record019_frame004_links
def record019_frame005_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcb064e322d86ac1e5962c5930096d3da1e98f2a77c3b41d5ce026ea2fc178889843914009c84c224511f08c045222210d881c4001f90f907b03821ba0cf065c32216d0b3852828613509704842160fe074038811608a04381ac0b605502a014c0a404f019808c03a01c00d806803201800b805402800f00700280100070018008002000 } : Fields).get c.val)
theorem record019_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5) (record019.inverseMaps 5) record019_frame005_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record019) (record019.maps 5)
      (record019.inverseMaps 5) record019_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame005_links_0000 record019_frame005_links_0064)
theorem record019_frame005_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 5 :=
  of_group record019 5 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame005_indices record019_frame005_graph record019_frame005_links
def record019_frame006_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1040.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1040.count (({ width := 11, code := 0x3e37bcf6de43c2744e69a4b425aeb51682ca58ab0957aa750a9fd1822937c6e8db9a533c648c59883085d0b71672c65749e1362444788c1021fc3b0720d91a231c5a8ae1362603c8780ea1842904c0961282484606408c0e81c0360680c81802e0540a00f01c0280400700600800800 } : Fields).get c.val)
theorem record019_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record019) (record019.maps 6) (record019.inverseMaps 6) record019_frame006_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1040.localPairCheck (smallEmbedding record019) (record019.maps 6)
      (record019.inverseMaps 6) record019_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame006_links_0000 record019_frame006_links_0064)
theorem record019_frame006_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 6 :=
  of_group record019 6 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1040
    Papers.RationalityTen.SharedFrameCatalogue.group1040_facts record019_frame006_indices record019_frame006_graph record019_frame006_links
def record019_frame007_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1000.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1000.count (({ width := 11, code := 0x4859031f63846b88b0f9e63c6656c958f317626c3d812fd5a6b352924b3786d8d819f338658c898e3125f4bb9712d6598a614726a4bc9510c20c3c4760e21b833c5f0b314e2843a8740e21702804a0921202384406008c0e81c0360680c81802e0540a00f01c0280400700600800800 } : Fields).get c.val)
theorem record019_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record019) (record019.maps 7) (record019.inverseMaps 7) record019_frame007_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1000.localPairCheck (smallEmbedding record019) (record019.maps 7)
      (record019.inverseMaps 7) record019_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame007_links_0000 record019_frame007_links_0064)
theorem record019_frame007_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 7 :=
  of_group record019 7 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1000
    Papers.RationalityTen.SharedFrameCatalogue.group1000_facts record019_frame007_indices record019_frame007_graph record019_frame007_links
def record019_frame008_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0556.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0556.count (({ width := 11, code := 0x3746e2db9b536969ed217daf55049f53d2764e69c13626b49891cf91f03065fcbe16f2d2578ac95429c5109f13a26a4c48c9142043f47c8e21c0334648c11782cc5289f12623c388700da1742704808e1182284205e08c0e81c0360680c81802e0540a00f01c0280400700600800800 } : Fields).get c.val)
theorem record019_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record019) (record019.maps 8) (record019.inverseMaps 8) record019_frame008_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record019) (record019.maps 8) (record019.inverseMaps 8) record019_frame008_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0556.localPairCheck (smallEmbedding record019) (record019.maps 8)
      (record019.inverseMaps 8) record019_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame008_links_0000 record019_frame008_links_0064)
theorem record019_frame008_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 8 :=
  of_group record019 8 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0556
    Papers.RationalityTen.SharedFrameCatalogue.group0556_facts record019_frame008_indices record019_frame008_graph record019_frame008_links
def record019_frame009_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0926.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0926.count (({ width := 9, code := 0x1188b452230e8541df4f771385c0de6e369aed46833580bd5429d4ca14fa7134994ba451c8b4421cfa7a3a9c8e26a3418cc05b2c154a24e25924803f1e8d4622e168b056291087434190c05c2c150a048220c058200e06018080200 } : Fields).get c.val)
theorem record019_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record019) (record019.maps 9) (record019.inverseMaps 9) record019_frame009_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record019) (record019.maps 9) (record019.inverseMaps 9) record019_frame009_indices (Fin.ofNat record019.n i)) 64 81 :=
  interval_of_check _ 64 17 (by decide +kernel)
theorem record019_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0926.localPairCheck (smallEmbedding record019) (record019.maps 9)
      (record019.inverseMaps 9) record019_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 81 record019_frame009_links_0000 record019_frame009_links_0064)
theorem record019_frame009_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) : Supported record019 9 :=
  of_group record019 9 (smallEmbedding record019) (small_cells_exact record019 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0926
    Papers.RationalityTen.SharedFrameCatalogue.group0926_facts record019_frame009_indices record019_frame009_graph record019_frame009_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (Fin.cases (record019_frame002_supported hcells) (Fin.cases (record019_frame003_supported hcells) (Fin.cases (record019_frame004_supported hcells) (Fin.cases (record019_frame005_supported hcells) (Fin.cases (record019_frame006_supported hcells) (Fin.cases (record019_frame007_supported hcells) (Fin.cases (record019_frame008_supported hcells) (Fin.cases (record019_frame009_supported hcells) (fun j => Fin.elim0 j)))))))))))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0977.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0977.count (({ width := 11, code := 0x14fe884d4956e09bc361682cf19bb2d626b91682c7584ac55529951a9bd2f2504948e51522543a7ecf81e13b6724de9b834c680c91892e8594ab93926242c829021e839c698cf1762c4570aa0ce15c2885009e138250440760d8160230400740e01301c0280400700600800800 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 79 :=
  interval_of_check _ 64 15 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0977.localPairCheck (smallEmbedding record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 79 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (smallEmbedding record020) (small_cells_exact record020 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0977
    Papers.RationalityTen.SharedFrameCatalogue.group0977_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSmall.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f16edb736356997cca85fda8153e89df4e52675306937488a33915886641f9e9cf2878a3ba1b1c9a24c025592588d244f2018f747343781990c2c4e626011f08a83ac1b90be05b82cc1510a184f424210c08283bc1d20db05482780e606002d01580a803b014008803c01c00c805c02600d005802400e0040018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 78 :=
  interval_of_check _ 64 14 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 78 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (smallEmbedding record022) (small_cells_exact record022 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x12ee5949f89b102023cb77ce95b7b596a6d39a4b3660ebdd78ae05b8b29592a5536a4946a6d4ca9412323946a8b90f21541280cfb9f13c4754d599d2fc5c0ae9492824f09311e22e4247b0d81a0314600bb16a1382684c0961282303f06c0d01582503c0740e01301e0240400700600800800 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
def record024_frame002_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0x146a84cea9232262bc0a7faf85c8b796e2da5b2b54666ca190b11614be572ad1590af95c2945129c530a474888cd1021340c7f4f39e43b474cd79a430e5ccb014b2844ec9291f22e4087b0de1b2334638c317a1482885009e138260450780e41602503c0740e01301e0240400700600800800 } : Fields).get c.val)
theorem record024_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record024) (record024.maps 2) (record024.inverseMaps 2) record024_frame002_indices (Fin.ofNat record024.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record024_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record024) (record024.maps 2)
      (record024.inverseMaps 2) record024_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record024_frame002_links_0000 record024_frame002_links_0064)
theorem record024_frame002_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 2 :=
  of_group record024 2 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record024_frame002_indices record024_frame002_graph record024_frame002_links
def record024_frame003_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0422.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0422.count (({ width := 7, code := 0x14a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record024_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0422.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0422.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0422.localPairCheck (smallEmbedding record024) (record024.maps 3) (record024.inverseMaps 3) record024_frame003_indices (Fin.ofNat record024.n i)) 64 83 :=
  interval_of_check _ 64 19 (by decide +kernel)
theorem record024_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0422.localPairCheck (smallEmbedding record024) (record024.maps 3)
      (record024.inverseMaps 3) record024_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 83 record024_frame003_links_0000 record024_frame003_links_0064)
theorem record024_frame003_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 3 :=
  of_group record024 3 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0422
    Papers.RationalityTen.SharedFrameCatalogue.group0422_facts record024_frame003_indices record024_frame003_graph record024_frame003_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (Fin.cases (record024_frame002_supported hcells) (Fin.cases (record024_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0xa5549279cd496d29230c2182f041fc3f17c8f81eebcc762e51c036d69ad19a233d588abd52a9e51ca314127d4b69551fa1b3ec7a0ed9d43a4738e51c33626a4c417f2cc4cc96918224434859092083e87a0e81b6358630c01762d8478760b81642704d09810c1582503c0740e01301e0240400700600800800 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0824.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0824.count (({ width := 11, code := 0xa934f2844ea9972f2444578951061842782d03e053fd7c2ef1d2b916f2dc5b63685f2b956dad0592b195f2b9528a2538a4444084d031fd3ec7bcf41e43b2750d79a430e5089d92523e45c881092043e47b0e71bc364668c71862f4458750be174290510a01141602503c0740e01301e0240400700600800800 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0824.localPairCheck (smallEmbedding record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0824
    Papers.RationalityTen.SharedFrameCatalogue.group0824_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
def record025_frame003_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0345.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0345.count (({ width := 7, code := 0xaf5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record025_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0345.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0345.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0345.localPairCheck (smallEmbedding record025) (record025.maps 3) (record025.inverseMaps 3) record025_frame003_indices (Fin.ofNat record025.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record025_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0345.localPairCheck (smallEmbedding record025) (record025.maps 3)
      (record025.inverseMaps 3) record025_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record025_frame003_links_0000 record025_frame003_links_0064)
theorem record025_frame003_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 3 :=
  of_group record025 3 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0345
    Papers.RationalityTen.SharedFrameCatalogue.group0345_facts record025_frame003_indices record025_frame003_graph record025_frame003_links
def record025_frame004_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0423.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0423.count (({ width := 8, code := 0x8d8c8b8a8887868483817f7e7d7c7b79777573716e6d6c6b69686765646361605d5c5b5855545251504f4d4c4a494645433f3e3c3b3a3937353332302e2d2b2a2928242322201c1b1a1917141211100c0a09080703020100 } : Fields).get c.val)
theorem record025_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0423.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (smallEmbedding record025) (record025.maps 4) (record025.inverseMaps 4) record025_frame004_indices (Fin.ofNat record025.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record025_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0423.localPairCheck (smallEmbedding record025) (record025.maps 4)
      (record025.inverseMaps 4) record025_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record025_frame004_links_0000 record025_frame004_links_0064)
theorem record025_frame004_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 4 :=
  of_group record025 4 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0423
    Papers.RationalityTen.SharedFrameCatalogue.group0423_facts record025_frame004_indices record025_frame004_graph record025_frame004_links
def record025_frame005_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0285.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0285.count (({ width := 7, code := 0xaf5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record025_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0285.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0285.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0285.localPairCheck (smallEmbedding record025) (record025.maps 5) (record025.inverseMaps 5) record025_frame005_indices (Fin.ofNat record025.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record025_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0285.localPairCheck (smallEmbedding record025) (record025.maps 5)
      (record025.inverseMaps 5) record025_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record025_frame005_links_0000 record025_frame005_links_0064)
theorem record025_frame005_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 5 :=
  of_group record025 5 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0285
    Papers.RationalityTen.SharedFrameCatalogue.group0285_facts record025_frame005_indices record025_frame005_graph record025_frame005_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (Fin.cases (record025_frame003_supported hcells) (Fin.cases (record025_frame004_supported hcells) (Fin.cases (record025_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0826.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0826.count (({ width := 11, code := 0xb5159eb2d049d53565f4b08e7149f33b574ee7dceb8f6bcce990b065e6bb9702d357aa913ba5f4968890ba0d40c808fe9fb3e47b8f61be34e5ecb215d2985049d132252474861061f43c4760dc1a432c6186b0941242404708c1141f82b0520780e81c03205c0981001e0240400700600800800 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0826.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0826
    Papers.RationalityTen.SharedFrameCatalogue.group0826_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x8b316221c307e0f598aaed5d0b856ead257eae557aa6546a6949a8a4e49c133a614a69211722543e869049fe3d2778ed1c637e6c8d499130a594ad1512944e0969132104086f8ca1722b84c0900ac1442584a0921202304307a0dc198280460740e01301c0200380400600800800 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x76d74d6bf6796475fe5a057d56c5325275235194c44944553d735a3172fb2e62dd2d62cc2c22ba2a429225d2442041f31d219818b18116514f12511a1050eb0d20ca0ab09808107206e06c05805205104403602c02502301d01c01300e00a008007003002001000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 69 :=
  interval_of_check _ 64 5 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 69 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0xb3961eabcfa9d32b62bc4d8650a2093fe7e6ef1c937f6b2d45a6347578a414327e4f09c936a1f3ee794ed9d63a2728e29bf3686b8c617b2424688b1112164147e0f91d43846e0d11882c85709311c1f0368630c01642985208a0dc160250460740e01301c0280400700600800800 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0xa2d3e25e4b68b70b60840579ad99a233e670cd58faee5a4a9d4828a4f89a93224044886503a043fe7d0f79e63c2750e79ca3485989a12d25049490919212404780e11b83345f0a91481d8368590a6148288500981141b82d05408c0e81c03205c0981001c0280400700600800800 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 80 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x9712d24fc748b7011e6b66688cf99c33563ebb96928b4c886503a043d8798ef1cf3926d0d219f2da598a813425a4a09290b2023c8708dc19a2f8548a41022003e0760da164298520a21402604506e08c0e81c0360680c81802e0540981001c0280400700600800800 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0xa154167bcb992711a0d3cd756e99d0399706ce1892bf52493518a2c42e841051f83e076ce49c23065ecb093b26a4ac9290b2083dc720dd19e2ec548a2106208400790da16c2a8540a61482704506e08c0e81c0360680c81802e0540981001c0280400700600800800 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0400.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0400.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0400.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0400.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0400.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0400.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0400
    Papers.RationalityTen.SharedFrameCatalogue.group0400_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
def record031_frame004_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0315.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0315.count (({ width := 8, code := 0x6b6a696867666564636261605f5e5d5c5b5a59585452504d4b49474542403e3b39373533312f2d2b292624221f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record031_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0315.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0315.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0315.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0315.localPairCheck (smallEmbedding record031) (record031.maps 4)
      (record031.inverseMaps 4) record031_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame004_links_0000 record031_frame004_links_0064)
theorem record031_frame004_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 4 :=
  of_group record031 4 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0315
    Papers.RationalityTen.SharedFrameCatalogue.group0315_facts record031_frame004_indices record031_frame004_graph record031_frame004_links
def record031_frame005_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0159.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0159.count (({ width := 8, code := 0x6b6a696867666564636261605f5e5d5c5b5a59585452504d4b49474542403e3b39373533312f2d2b292624221f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record031_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0159.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0159.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0159.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0159.localPairCheck (smallEmbedding record031) (record031.maps 5)
      (record031.inverseMaps 5) record031_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame005_links_0000 record031_frame005_links_0064)
theorem record031_frame005_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 5 :=
  of_group record031 5 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0159
    Papers.RationalityTen.SharedFrameCatalogue.group0159_facts record031_frame005_indices record031_frame005_graph record031_frame005_links
def record031_frame006_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0074.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0074.count (({ width := 8, code := 0x6b6a696867666564636261605f5e5d5c5b5a59585452504d4b49474542403e3b39373533312f2d2b292624221f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record031_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0074.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0074.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0074.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0074.localPairCheck (smallEmbedding record031) (record031.maps 6)
      (record031.inverseMaps 6) record031_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame006_links_0000 record031_frame006_links_0064)
theorem record031_frame006_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 6 :=
  of_group record031 6 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0074
    Papers.RationalityTen.SharedFrameCatalogue.group0074_facts record031_frame006_indices record031_frame006_graph record031_frame006_links
def record031_frame007_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0053.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0053.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0053.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0053.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0053.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0053.localPairCheck (smallEmbedding record031) (record031.maps 7)
      (record031.inverseMaps 7) record031_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame007_links_0000 record031_frame007_links_0064)
theorem record031_frame007_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 7 :=
  of_group record031 7 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0053
    Papers.RationalityTen.SharedFrameCatalogue.group0053_facts record031_frame007_indices record031_frame007_graph record031_frame007_links
def record031_frame008_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0038.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0038.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0038.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0038.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0038.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0038.localPairCheck (smallEmbedding record031) (record031.maps 8)
      (record031.inverseMaps 8) record031_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame008_links_0000 record031_frame008_links_0064)
theorem record031_frame008_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 8 :=
  of_group record031 8 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0038
    Papers.RationalityTen.SharedFrameCatalogue.group0038_facts record031_frame008_indices record031_frame008_graph record031_frame008_links
def record031_frame009_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0031.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0031.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0031.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0031.localPairCheck (smallEmbedding record031) (record031.maps 9) (record031.inverseMaps 9) record031_frame009_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0031.localPairCheck (smallEmbedding record031) (record031.maps 9) (record031.inverseMaps 9) record031_frame009_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0031.localPairCheck (smallEmbedding record031) (record031.maps 9)
      (record031.inverseMaps 9) record031_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame009_links_0000 record031_frame009_links_0064)
theorem record031_frame009_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 9 :=
  of_group record031 9 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0031
    Papers.RationalityTen.SharedFrameCatalogue.group0031_facts record031_frame009_indices record031_frame009_graph record031_frame009_links
def record031_frame010_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x6583275880b2754fa6011ee7f83d31e54ef876938617ccad644c1e18b104e426112288f846e22a11108383fe1f90e086e833c17b0ba85b42ce14a0a184d424e12108903f81d00e2045822810c07d037816c0aa054029814809c04501b808c03a01c00d806803201800b805402601000700280100070018008002000 } : Fields).get c.val)
theorem record031_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 10) (record031.inverseMaps 10) record031_frame010_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 10) (record031.inverseMaps 10) record031_frame010_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 10)
      (record031.inverseMaps 10) record031_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame010_links_0000 record031_frame010_links_0064)
theorem record031_frame010_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 10 :=
  of_group record031 10 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame010_indices record031_frame010_graph record031_frame010_links
def record031_frame011_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x768ec9d037e6c2cbd89ad257cae95b2b45449e531a3141c750df1bc35a698cf1923185dcb59632704c48e0ff1f03cc778e21b6348630c31702a44b8930f21e03a06e0ca1482604b0941242283f06c0880e81c0360680c81802e0540981001c0280400700600800800 } : Fields).get c.val)
theorem record031_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record031) (record031.maps 11) (record031.inverseMaps 11) record031_frame011_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record031) (record031.maps 11) (record031.inverseMaps 11) record031_frame011_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (smallEmbedding record031) (record031.maps 11)
      (record031.inverseMaps 11) record031_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame011_links_0000 record031_frame011_links_0064)
theorem record031_frame011_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 11 :=
  of_group record031 11 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record031_frame011_indices record031_frame011_graph record031_frame011_links
def record031_frame012_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7687617486f06c66475ff56c53252751e5144fe4954553ce3a23172e62dd2bf2b72af29828f27125a24e2061fa1d31a219818b18115915113d12511a1060eb0d20ca08508408107906c05805205105004f04c04403602301d01c01b01a01901801701501301000e00a008007003002001000 } : Fields).get c.val)
theorem record031_frame012_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame012_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 12) (record031.inverseMaps 12) record031_frame012_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame012_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 12) (record031.inverseMaps 12) record031_frame012_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame012_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record031) (record031.maps 12)
      (record031.inverseMaps 12) record031_frame012_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame012_links_0000 record031_frame012_links_0064)
theorem record031_frame012_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 12 :=
  of_group record031 12 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record031_frame012_indices record031_frame012_graph record031_frame012_links
def record031_frame013_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0399.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0399.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame013_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0399.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame013_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0399.localPairCheck (smallEmbedding record031) (record031.maps 13) (record031.inverseMaps 13) record031_frame013_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame013_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0399.localPairCheck (smallEmbedding record031) (record031.maps 13) (record031.inverseMaps 13) record031_frame013_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame013_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0399.localPairCheck (smallEmbedding record031) (record031.maps 13)
      (record031.inverseMaps 13) record031_frame013_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame013_links_0000 record031_frame013_links_0064)
theorem record031_frame013_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 13 :=
  of_group record031 13 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0399
    Papers.RationalityTen.SharedFrameCatalogue.group0399_facts record031_frame013_indices record031_frame013_graph record031_frame013_links
def record031_frame014_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0314.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0314.count (({ width := 7, code := 0xd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8a94a84d97263c58501f3b72ddab362bd6ab52992223e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame014_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0314.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame014_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0314.localPairCheck (smallEmbedding record031) (record031.maps 14) (record031.inverseMaps 14) record031_frame014_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame014_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0314.localPairCheck (smallEmbedding record031) (record031.maps 14) (record031.inverseMaps 14) record031_frame014_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame014_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0314.localPairCheck (smallEmbedding record031) (record031.maps 14)
      (record031.inverseMaps 14) record031_frame014_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame014_links_0000 record031_frame014_links_0064)
theorem record031_frame014_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 14 :=
  of_group record031 14 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0314
    Papers.RationalityTen.SharedFrameCatalogue.group0314_facts record031_frame014_indices record031_frame014_graph record031_frame014_links
def record031_frame015_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0207.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0207.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame015_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0207.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame015_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0207.localPairCheck (smallEmbedding record031) (record031.maps 15) (record031.inverseMaps 15) record031_frame015_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame015_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0207.localPairCheck (smallEmbedding record031) (record031.maps 15) (record031.inverseMaps 15) record031_frame015_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame015_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0207.localPairCheck (smallEmbedding record031) (record031.maps 15)
      (record031.inverseMaps 15) record031_frame015_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame015_links_0000 record031_frame015_links_0064)
theorem record031_frame015_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 15 :=
  of_group record031 15 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0207
    Papers.RationalityTen.SharedFrameCatalogue.group0207_facts record031_frame015_indices record031_frame015_graph record031_frame015_links
def record031_frame016_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0098.count (({ width := 7, code := 0x972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame016_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0098.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame016_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0098.localPairCheck (smallEmbedding record031) (record031.maps 16) (record031.inverseMaps 16) record031_frame016_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame016_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0098.localPairCheck (smallEmbedding record031) (record031.maps 16) (record031.inverseMaps 16) record031_frame016_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame016_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0098.localPairCheck (smallEmbedding record031) (record031.maps 16)
      (record031.inverseMaps 16) record031_frame016_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame016_links_0000 record031_frame016_links_0064)
theorem record031_frame016_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 16 :=
  of_group record031 16 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0098
    Papers.RationalityTen.SharedFrameCatalogue.group0098_facts record031_frame016_indices record031_frame016_graph record031_frame016_links
def record031_frame017_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0060.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0060.count (({ width := 7, code := 0xd7ab4e8cf9b2e4c78b0e0bf7aedcb76acd8a94a84d97263c58501f3b72ddab362bd6ab52992223e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record031_frame017_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0060.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame017_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0060.localPairCheck (smallEmbedding record031) (record031.maps 17) (record031.inverseMaps 17) record031_frame017_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame017_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0060.localPairCheck (smallEmbedding record031) (record031.maps 17) (record031.inverseMaps 17) record031_frame017_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame017_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0060.localPairCheck (smallEmbedding record031) (record031.maps 17)
      (record031.inverseMaps 17) record031_frame017_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame017_links_0000 record031_frame017_links_0064)
theorem record031_frame017_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 17 :=
  of_group record031 17 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0060
    Papers.RationalityTen.SharedFrameCatalogue.group0060_facts record031_frame017_indices record031_frame017_graph record031_frame017_links
def record031_frame018_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0052.count (({ width := 8, code := 0x6b6a696867666564636261605f5e5d5c5b5a59585452504d4b49474542403e3b39373533312f2d2b292624221f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100 } : Fields).get c.val)
theorem record031_frame018_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0052.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame018_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0052.localPairCheck (smallEmbedding record031) (record031.maps 18) (record031.inverseMaps 18) record031_frame018_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame018_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0052.localPairCheck (smallEmbedding record031) (record031.maps 18) (record031.inverseMaps 18) record031_frame018_indices (Fin.ofNat record031.n i)) 64 76 :=
  interval_of_check _ 64 12 (by decide +kernel)
theorem record031_frame018_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0052.localPairCheck (smallEmbedding record031) (record031.maps 18)
      (record031.inverseMaps 18) record031_frame018_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 76 record031_frame018_links_0000 record031_frame018_links_0064)
theorem record031_frame018_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 18 :=
  of_group record031 18 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0052
    Papers.RationalityTen.SharedFrameCatalogue.group0052_facts record031_frame018_indices record031_frame018_graph record031_frame018_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (Fin.cases (record031_frame004_supported hcells) (Fin.cases (record031_frame005_supported hcells) (Fin.cases (record031_frame006_supported hcells) (Fin.cases (record031_frame007_supported hcells) (Fin.cases (record031_frame008_supported hcells) (Fin.cases (record031_frame009_supported hcells) (Fin.cases (record031_frame010_supported hcells) (Fin.cases (record031_frame011_supported hcells) (Fin.cases (record031_frame012_supported hcells) (Fin.cases (record031_frame013_supported hcells) (Fin.cases (record031_frame014_supported hcells) (Fin.cases (record031_frame015_supported hcells) (Fin.cases (record031_frame016_supported hcells) (Fin.cases (record031_frame017_supported hcells) (Fin.cases (record031_frame018_supported hcells) (fun j => Fin.elim0 j))))))))))))))))))))
#print axioms record031_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00000

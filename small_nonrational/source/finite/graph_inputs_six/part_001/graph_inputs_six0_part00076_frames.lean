module
prelude
public import GraphInputsSix0Part00076Data
public import RawFrameSupport
public import SharedFrameGroups062Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups068Checked
public import SharedFrameGroups082Checked
public import SharedFrameGroups083Checked
public import SharedFrameGroups088Checked
public import SharedFrameGroups089Checked
public import SharedFrameGroups091Checked
public import SharedFrameGroups092Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record000_frames_supported
theorem record001_frame000_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    Supported record001 0 :=
  of_identity record001 0 (by decide +kernel)
theorem record001_frames_supported (hcells : ∀ c, record001.data.cells c = FacetUniverses.FullSix0.cells (embedding record001 c)) :
    ∀ f : Fin record001.g, Supported record001 f :=
  (Fin.cases (record001_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record001_frames_supported
theorem record002_frame000_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    Supported record002 0 :=
  of_identity record002 0 (by decide +kernel)
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record002_frames_supported
theorem record003_frame000_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    Supported record003 0 :=
  of_identity record003 0 (by decide +kernel)
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record004_frames_supported
theorem record005_frame000_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    Supported record005 0 :=
  of_identity record005 0 (by decide +kernel)
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSix0.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
def record006_frame001_indices (c : Fin record006.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa7f53ca57129792148a23891967c83df9ec4f53739b939b66d8e6a834619fecf66772fc5722b5359c2b35524a6c512a79d39896149324011988c645aa2c112c88f3ef1ee0e7871c3881a94d2267e32c194cc7a5e72e396ecaa053c294940c9fc4e826092cc94c4a124992048ee46f236106079632717c8a604f226b130093c46c20f0f707a036a1960c405f42d8153096042c20a0f807483881ba0d5059027810a06f030011406a032013008c0320170050024008003 } : Fields).get c.val)
theorem record006_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record006.data.requiredEdges q = true := by decide +kernel
theorem record006_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record006_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record006) (record006.maps 1) (record006.inverseMaps 1) record006_frame001_indices (Fin.ofNat record006.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record006_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record006) (record006.maps 1)
      (record006.inverseMaps 1) record006_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record006_frame001_links_0000 record006_frame001_links_0064)
theorem record006_frame001_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) : Supported record006 1 :=
  of_group record006 1 (embedding record006) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record006_frame001_indices record006_frame001_graph record006_frame001_links
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (Fin.cases (record006_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record006_frames_supported
theorem record007_frame000_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    Supported record007 0 :=
  of_identity record007 0 (by decide +kernel)
theorem record007_frames_supported (hcells : ∀ c, record007.data.cells c = FacetUniverses.FullSix0.cells (embedding record007 c)) :
    ∀ f : Fin record007.g, Supported record007 f :=
  (Fin.cases (record007_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record007_frames_supported
theorem record008_frame000_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    Supported record008 0 :=
  of_identity record008 0 (by decide +kernel)
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x28ff453993cbae5792a8947495249b2138c8c4221a6fea7d6be85f0ef5c7a3bc71c74da4685b2c5948c96648b20d78eb9e592abf158eab0552aa752ec93c491230d11286f425a0fd06c8303cf9d9ce8c6f535e9a70cb465432198fcbf653529694189504a023c919c8b64562290ef07263501978c245fa2eb16e8abc51c26812e0928478233112087042a1e10db06482d8143097045c20c0f106d03480f607102f016c0b2056026810406e024011807c03c01700a003801a009004000c002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (Fin.cases (record008_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record008_frames_supported
theorem record009_frame000_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    Supported record009 0 :=
  of_identity record009 0 (by decide +kernel)
theorem record009_frames_supported (hcells : ∀ c, record009.data.cells c = FacetUniverses.FullSix0.cells (embedding record009 c)) :
    ∀ f : Fin record009.g, Supported record009 f :=
  (Fin.cases (record009_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record009_frames_supported
theorem record010_frame000_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    Supported record010 0 :=
  of_identity record010 0 (by decide +kernel)
def record010_frame001_indices (c : Fin record010.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1456a214c7e6132ef96c4b2e56929393a498649d17a8b1c33a1750787fb3fa1f42f7f7b6b45da00c5059c2a894f49cc49b24391848af4532230fdc7c63749a44cba63b2ca14f0a104e625912248d44181d30d586563191830b604f225812588ec45a21a0ff879032c1750b4056029413708e04041ec094048023410a06a02d81580aa05402680e406a032015009804602100f007403801900b805002600f00700240100070018008002000 } : Fields).get c.val)
theorem record010_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record010.data.requiredEdges q = true := by decide +kernel
theorem record010_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record010_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record010) (record010.maps 1) (record010.inverseMaps 1) record010_frame001_indices (Fin.ofNat record010.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record010_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record010) (record010.maps 1)
      (record010.inverseMaps 1) record010_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record010_frame001_links_0000 record010_frame001_links_0064)
theorem record010_frame001_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) : Supported record010 1 :=
  of_group record010 1 (embedding record010) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record010_frame001_indices record010_frame001_graph record010_frame001_links
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (Fin.cases (record010_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaa3a75a489e09af99095f94093c9349179098f38cc8b68a888387e87a87486b86986686485a85884e84781e8177d17ca7a179672b6f869066e6475c55b358156f56155254553e4de4cd4b84a747344643a42940d3eb3973793593483403133062f72e92dc2d32cc2882492212092041fa1db1d11ba1af1a418b18817e17216715a13d12c12410f1030fe0f20e00da0cd0c80c40c10bb09207907806f05f05504704503d02c02102000f00e00a003000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record013_frames_supported
theorem record014_frame000_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    Supported record014 0 :=
  of_identity record014 0 (by decide +kernel)
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x2337148876425e10b0758233f51f42f2f791bb71d58e7c716b7f5b3cd906a73475a1ed01677b37597ecac651321186eb3658ea921454a174db26652ca94248223d11bc8a243fa17105c8193b39d48e787273809b94d966b434c99f0cc265d31b9898bee5b32c295a4acc53d29793e09b44d2265927091c3ad1c40da069632f18e8b905862a214389d44b223811308543b81bf0d7862c2f614f0a204d024a11008083c41c80d204902440f607102a811c08a02e016007c03c011008003000a000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (Fin.cases (record015_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record015_frames_supported
theorem record016_frame000_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    Supported record016 0 :=
  of_identity record016 0 (by decide +kernel)
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSix0.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaaca7d9fd9fb9c79c09ad9a797796892a9268db8d78197cc76973e6fb6bf6af6456436075f459457f55654e51f4df4cd4b84a747343842d4173fd3e13df39736235734c33031d3093072e22c32be2ad2872492051e31d91ac1a418b18816616115b13a12410f1030e80df0db0cf0c90bf0b80a60a409c09907506f06405f03d03503302c02602301901700b00a005003 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (embedding record018) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa10502667930095b4a8a4eb2348f747721df0ba821c021f64fa671d38bdc44c8d64131ed7e4bd85da2e396a0b365892bb15aaac755caad154ca9f4c3a595274921487a351164887437217109683e41ba0c4fba79f3989bd4d0e65a32a190cc7a5c42cf1580a8852128393e49a64b724a11e88d846722e115c8a24011c08d3865e31f18a0ba85b22ad14709f84e624911c08cc44621c10b077836a1940b5856028613c098049022a10607f83cc1ce0d8069027812805e02c810408003701b008803a01900b803c01c00a0048014002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 128 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x131c969cac23c71cc8ca45f62b313388a43ba1910327f0be4df0ed3e60d301977eb895b1ab8d58ca83533292d478a35486a3f91ec88c42e20c10387f03f39e34e827303921c5cd4068031f987cc065f92f995c8a3a4f827793a492a450210906879a39d1be8dbc67a31d1878c145ec2f015b8a2c4ca25b12608f4456221109080c3f41a30c005ac29e13a09304602120e904a02400be05b02a8150072035015009c04c023010807403801900b804c02400f007002c0100070018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2877420a04cb3e5832bc95448063f11ee8ee449de1ef0777fbbd1b42d086582ec561eac6503a75d31496549f24812188d7459222d0da85941da0d4fba79f39a1bd4d146592e11678abc54429594209fc4d125b92788f647123191547823941a80cbc6242f016d8abc51c27112788e845e2220ee06d431017c0b3855828613c097049023010607f83c41ce0db04802380da06a03101780b205401980c805c028012007c03801700900380120070028008002000 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x50828133229734ac653b25c90dc7de3e91e28b9c5221c50ad82bc071f58fa07b33c99e06ef871736159d8ca3645b1d9534a1e4b424f123891045aa2250d285d41a20b8fba6502fb9630a8452d28593e096a4a023f11ac8c64501df8e586623091768b6852026812608e445e21b0d986482d01590a184f026212208b84181fe0f407283681640af04802340f607103681a40cc05e02c815008003601900c405c02c011807803801900980340100070028010002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1005.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1005.count (({ width := 12, code := 0x9129108f58f28e28d08c48a688187186383883081480f8037f27d07bb79078e77f77977873e6cc69468c5e85c65ad55354752e52150b5024fa4ea4dd4d34c74bf4ae4a94a147945744743742340f3fa3e73dd37e33f33530c3062f12e62df2ca2b22ab29728727f2312081f01d11c31af1a519a18c17516915914a13d11d1100f60f00eb0e30de0d70d10c30bf0ba0b50ae09308a07907106005b05705602a02802402101f01501200e00c009006002001000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1005.localPairCheck (embedding (N := 44310) record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (embedding record023) hcells Papers.RationalityTen.SharedFrameCatalogue.group1005
    Papers.RationalityTen.SharedFrameCatalogue.group1005_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19c1cc764c70b3819c085b86d896adb4d5a16cdd5e7ae7d67eb0955fa79d3aa9c54b8a52526691d473a2dcf8e78d3bb9ccce026eb2ef96a4b1a54328293a46623011738a9c4f2260d156662f2d496a124e325a91f28d644c218d0387fb3f41f58f6e7a63ca9a5ca2e4de24910d878a3a21b20cbc5d02c715a0a8850627213088f844821c0fd07c83c61ce0e106e83221890ba85b42ce13d09a84bc25011908984301fc0f607803880e206d03301900be05b02b81540a803901a80b8058027011807c03a01c00c805c02a012008803801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record026_frame001_links_0000 (interval_append _ 64 128 137 record026_frame001_links_0064 record026_frame001_links_0128))
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x13f79e14e726132c0956c81a3e71c48dbc6922eb1578a3c44a2050c6857429212908383cc1a60c5059827c07e00cfef7e8bee1f42f757b0bd41e64f1e786bb4dd86eb574fba3dd02c1c6032dc1492a354efa62d24c90c47b22d90bc84141820790027f03f39c90c065f32d49588a1a4f927492dc8e245d228110885c42120d0f3471c37d1970c746082f01670ae049a23d109880c3f41920c105dc2d81510a304ec24c11a08503a40e206d03301900be05b02b81540a803901a80b8058027011807c03a01c00c805c02a012008803801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record026_frame002_links_0000 (interval_append _ 64 128 137 record026_frame002_links_0064 record026_frame002_links_0128))
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
def record026_frame003_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x95994894291b9059018d68d28c98c68c18b88ab8a388f88787286786686285d85b85785285084e83e83783182681e8188098007f87ed7e47dc7c87c27bc7b47ae7a86e56d26715cd5bb59456b53452250e4ee4c74ba4b14a649448948142137d36b3443162e12d22be29e27626425924e2412382312151f61ed1c51bc1af1a319819016415a14113713111310b1060ff0f10ec0e50d90d50d00c307106d06606405f05b05705505403903502e02c02702301f01d01c01901701501201100e00c00a008007005004003002001000 } : Fields).get c.val)
theorem record026_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record026_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record026) (record026.maps 3) (record026.inverseMaps 3) record026_frame003_indices (Fin.ofNat record026.n i)) 128 137 :=
  interval_of_check _ 128 9 (by decide +kernel)
theorem record026_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record026) (record026.maps 3)
      (record026.inverseMaps 3) record026_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 137 record026_frame003_links_0000 (interval_append _ 64 128 137 record026_frame003_links_0064 record026_frame003_links_0128))
theorem record026_frame003_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 3 :=
  of_group record026 3 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record026_frame003_indices record026_frame003_graph record026_frame003_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (Fin.cases (record026_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8cdc5221d7097844411607afa07cc3535a7cd01678328986eb3058bab29562a50515285d37299c48e23d11bc85f4172064f1a76739f1ca0e4e70136e1b08d6869933e1984c6e6262fc1758b7e5b32cd15f8acc53d29794209d44d224e12387d23cd1d68e206d03361978c745c82c314c0a1c4ea25911c089842a1e10e2067031617b0b2051026812507883901a40b905c024812207a02c815408e045010807c03c011008003000c000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0x652c9d90f1ce36c5b8af0c609c057eaf6de5bb9762e9dcdb7b6ead6da9b4b686c9d8fb15616bdd79a794da9450ba132ee54c988c114215c1e7d0f79e13b072ee0db53676a6d2192b21606bd576ae05a6b05602bb558a7547a854f49d136a5c4a49451aa0b3f87c4f59da39a6f4d99a52ea564aa14e2804e49812a242464848fd1e43846d8d619a3185e8b015a29c4f89b12a2183485c0b61141c8330640941180c01201802003 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0995.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0995.count (({ width := 12, code := 0x8d08c88a289a84283982181e8057fc7ec7e96e86c36bd69f68d66c66664861b6155f05de5ba5b555b5495255055034e64cd4b54a54a448e46b4264203e93cc3c53a537e36735134533132631d3082f92f82de2d82cd2b92af2a32a029c29227525a24423922521b20e1f31e41e21c51c01b619c19218618217c16e15b14913811a10f0fd0ec0e80e40d30c50bc0ba0af0a50a109108b07506c04503b02602402101e01100f00c009 } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0995.localPairCheck (embedding (N := 44310) record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record031_frame001_links_0000 record031_frame001_links_0064)
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0995
    Papers.RationalityTen.SharedFrameCatalogue.group0995_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb64dad6c27600a4851d682b3fa9bbcd8e68332a72f3785b8ed43686b1f58e0bf95be2d895bcaa850c282d31897e4ada52528e92a48aa4211f88fb46fa2550067ed3ac9c6cdf86792fc9724b4458c2b09530a5a4fb26d135493848823a112886c41c20810107ac38a1ad0ccc63a2f216e8af851826b13308b44322050ed871c35a1a10ca859c2a014209a048423410f08183f81f00ee07203701b20d206202e813809103c81b808e03b013009004201e008803c018009 } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record031_frame002_links_0000 record031_frame002_links_0064)
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0993.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0993.count (({ width := 11, code := 0xc9d9271f639c3184300dfebe37b6ef5dba5142e84cf09c32ea5ac988fd1ea30450855095f53df786ebdd7398708dddb4b686a8d2192b21606bd5772c7558a7547a854f49d136a5c4a49451e233456869092023fc7e4f51da39a6f4d99a3336648be96c2d6564aa14e2804e49812c24e460850fe1e8398700d519832c638bc16a2bc570a813e26c430800de1a42283904a08c1001d02203c06009 } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0993.localPairCheck (embedding (N := 44310) record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record031_frame003_links_0000 record031_frame003_links_0064)
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (embedding record031) hcells Papers.RationalityTen.SharedFrameCatalogue.group0993
    Papers.RationalityTen.SharedFrameCatalogue.group0993_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x117c894c309dbee5d6ef3689aead5e6ae34b5a30d0a66e32e994eb6259f2c955e6ac355527a13689974b8258529a93e497247d2148ef46ca2cd12087243120dd0447693a31cc0e046d935f9a64d1c67c3389984cac64a3191884b2e57b2b29560a6c52828593b49a64c7252925c8263e41e40e7872437e1b90d8c6aa3451960c685e82de1698af45702a81470a044de1ee0e886e43561860bb058827c12e08e843c1e40e506b01d40e6070013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x129c9194711efae5570036d9a80d3669ab3c99c2cd3643b1b58c4af656b2b19514a6a52fa5ed2aa94648f24251e28e346622e9158895443a18106a8124009f78fa66ff36c1b20d1c66932d18c8c4860e30217bcbc25d72e116d8a4e502273935c9784b224b11d08b444c219109c74437a1b48cf465a3171860be45d42df1660b0053a28413c09a04c025212108e84621c60d4064030a16d0b2054c25a12108a841c1d20de06a01d40e6070013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x4c997f2d64e4939131fe3ec7c8f71c2364688bb15e294017eefc1f03d77a4e71c938b708df1bab6d6ccd89ad35369ed099ab28648c5d89aca57aad955aa353ca5548a8950a9f53ca754da9a521a364548990d21741a804fa9f23cc78cd599c328628c09782de598b11592a0530a093a26a4b89492523c4648a8e71b4334650bd1742c0530a0134244428800f61542a0530460841001f0180280480800c01001802 } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
def record034_frame001_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x4b7653326b916c7f637ef7d74839f1cd2e5471b3879c14dff6f63751b80db56a034d9a6acf2670b34d90ec6d6312a3d4dea6148f23c51988ba44aa21d0c08354092004fbc7d337c9b48d8c6883319960c8e63230a9838bee5ef2f09728b845b62c11574a9e52728794089e24e726b93189784b224b11d08b444c219109c7423791b40cf462e2f91750b3058029d14389e04d426012909104742310e306a03201850b685902a612d090845420e0e906f035008e04502100f4076038013009004602200600280120080030010006002 } : Fields).get c.val)
theorem record034_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record034) (record034.maps 1) (record034.inverseMaps 1) record034_frame001_indices (Fin.ofNat record034.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record034_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record034) (record034.maps 1)
      (record034.inverseMaps 1) record034_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record034_frame001_links_0000 record034_frame001_links_0064)
theorem record034_frame001_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 1 :=
  of_group record034 1 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record034_frame001_indices record034_frame001_graph record034_frame001_links
def record034_frame002_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x1332644c297d2e25a49c93726a4b4929232424648890f21a4147e8fb1f23dc708d91a22ec578a4f89ecbd4708dd5b33626a6d3da1335650c918bb13590aed5a2a9542a714d295518a254027d4f29c136a694ba951272434768d91722a44c8790d21741a804fa9f23cc78cd519b326628bc1662c4540a61412764d49792924a47c8c9151ce368668ca17a2e8580a6140268488851001ec1c0360680c8188300460841001f0180280480800c01001802 } : Fields).get c.val)
theorem record034_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record034) (record034.maps 2) (record034.inverseMaps 2) record034_frame002_indices (Fin.ofNat record034.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record034_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record034) (record034.maps 2)
      (record034.inverseMaps 2) record034_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record034_frame002_links_0000 record034_frame002_links_0064)
theorem record034_frame002_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 2 :=
  of_group record034 2 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record034_frame002_indices record034_frame002_graph record034_frame002_links
def record034_frame003_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x1c037eef4dd1b8369e74ca794727e4dc7d8f31d638c6d8cf1862fc2b84f09601bf77c6e95c0b653f2754dc8bb13e21c3c85b09a0c40a7fcfddf43e1770e95cc3866e6d99af3596a4d3da434567ecdd9932b61ebdd73ad058eb0d5e2bb566a995129b5169ed38a694a8929079f73ce744e09b735e668c817d2e85c0b49682c054ca794823843c810fc1dc39c700d219c320610b41602a8228430820f01d03804c090118220180280480800c01001802 } : Fields).get c.val)
theorem record034_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record034) (record034.maps 3) (record034.inverseMaps 3) record034_frame003_indices (Fin.ofNat record034.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record034_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record034) (record034.maps 3)
      (record034.inverseMaps 3) record034_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record034_frame003_links_0000 record034_frame003_links_0064)
theorem record034_frame003_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 3 :=
  of_group record034 3 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record034_frame003_indices record034_frame003_graph record034_frame003_links
def record034_frame004_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0x19e73c672cd198f2bde0b576aad4da7b19622c2d82afb5eabad73a8f4f69dd1ba2743a774e69b90ee17422760e89c9b896fadd5b535a69cd219cb2f5fcbd5752da5a4b195e2b9568ac554aa6542a654b29350c9dd352594a2941252484808e51a232450869062063f07c8e29ba356664c597d2ec5a0b195729e528a193e2784d89a1302143fc790eb1bc360690c61842f45b8ab14c2882204207e0f01d03804c090118220180280480800c01001802 } : Fields).get c.val)
theorem record034_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record034) (record034.maps 4) (record034.inverseMaps 4) record034_frame004_indices (Fin.ofNat record034.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record034_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record034) (record034.maps 4)
      (record034.inverseMaps 4) record034_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record034_frame004_links_0000 record034_frame004_links_0064)
theorem record034_frame004_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 4 :=
  of_group record034 4 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record034_frame004_indices record034_frame004_graph record034_frame004_links
def record034_frame005_indices (c : Fin record034.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0929.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0929.count (({ width := 9, code := 0x4e671379b4d66933994c6612f974b6592b954a6512793496492391486411e8e42a1106783b5d4e872b8dc0dd6d361aad363b1586c15faf578bb5c2dd68b358ab95aab54a9d4aa24fa79369a4ca592a944923d188a43a14f4783b1cce06d359a0cc633017cb85b2d15cac55251208c452190882401f8f87a3c1d8e854291409c4c250e86c3419058241007030100602 } : Fields).get c.val)
theorem record034_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.graphBitCheck record034.data.requiredEdges q = true := by decide +kernel
theorem record034_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record034_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (embedding (N := 44310) record034) (record034.maps 5) (record034.inverseMaps 5) record034_frame005_indices (Fin.ofNat record034.n i)) 64 127 :=
  interval_of_check _ 64 63 (by decide +kernel)
theorem record034_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0929.localPairCheck (embedding (N := 44310) record034) (record034.maps 5)
      (record034.inverseMaps 5) record034_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 127 record034_frame005_links_0000 record034_frame005_links_0064)
theorem record034_frame005_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) : Supported record034 5 :=
  of_group record034 5 (embedding record034) hcells Papers.RationalityTen.SharedFrameCatalogue.group0929
    Papers.RationalityTen.SharedFrameCatalogue.group0929_facts record034_frame005_indices record034_frame005_graph record034_frame005_links
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (Fin.cases (record034_frame001_supported hcells) (Fin.cases (record034_frame002_supported hcells) (Fin.cases (record034_frame003_supported hcells) (Fin.cases (record034_frame004_supported hcells) (Fin.cases (record034_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x8b3444e15ce6a72f37adbbedac6d2b4b1a26d0560fb0157debe45dbae856beb3158c2a394eea6252b28a142a9e84da265d2dc94b496a4711da8d745aa2490e686541ca0910287e93e99ef4ed474a39a1c04dae6bd34d9a34cfc6703311964c9263431197e0ba25ba28413a89a44c425112508223df1e18ecc7403861c00d986c835819a8cb86382f716b0ae4556284139099447c22c10d07b83be1d10e106e43561970c305d821a0f007183500fe07d03d008403e01e00e806402e0140030010006002 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x942485e352e6d72db835c02dc36dbb3b59b8cd25ec2ecd71eb7f5adad415daacd561a90142a9f54f2a71536e97b4aaa5192368ef46522e1126886431a0dd0288033f01f50f9879f3c39dd4e066dc3649a2cccc65931a988cc206032f8978cbac5c42db9608aba54f24991c48ae449217909873a3751b38d5867e31e18c8c005f62ec1698b385822a013d89884aa23c11908b04121f80f587183681a80cd864030a1780b6859020a0e706e03480fe07d03d008403e01e00e806402e0140030010006002 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
def record036_frame003_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0939.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0939.count (({ width := 11, code := 0x98b2ee58c9892923a454849011be35c678730c614c2583b065ff3f47daf39e2bbc770ebdd5b9c724e2dc13736cad81a934e686cd994b25630c5187afc5e6ba965abe56eaa95129d52ea4145a844fc9ed3a26e4d49752a24e418800fa1f13ca788d499a324644c597b2f25a4b39632a6544a694226c4a89311a22c450828fe1ee39c700da1a6334650c317a2e8478840fe1e82d8590ae0780e01b0340580a01200c01001802 } : Fields).get c.val)
theorem record036_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record036) (record036.maps 3) (record036.inverseMaps 3) record036_frame003_indices (Fin.ofNat record036.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record036_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0939.localPairCheck (embedding (N := 44310) record036) (record036.maps 3)
      (record036.inverseMaps 3) record036_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record036_frame003_links_0000 record036_frame003_links_0064)
theorem record036_frame003_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 3 :=
  of_group record036 3 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0939
    Papers.RationalityTen.SharedFrameCatalogue.group0939_facts record036_frame003_indices record036_frame003_graph record036_frame003_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (Fin.cases (record036_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x2d6dacb43682cd584b035f2bbd76aeb5ceb355caa3522a2d37a674a69151ea2344283cf69a71862d4338570860d3e77baf41e3ba7744e71c3b7d6e4d61a5b135febd16eacf596b055e2b14d69992423c4568950e1f93e665cc99892fe5bcaf9572a84f49892d2504848c1011ec3906d8d319e330618b114a27c4e0960ec1882f85d0921201c03704e0840f8120220380680c01201801000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSix0.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x46422f913d894c18205b01c7ddbe21eeef0d74eb879b34d7e6b3b56da9cd2d65cb299854c175feade96c4b3d5922c595e6aa74d9a6593049644a0a47d20e8f346ea30913487741b2084ed27253811accd3268e33e19c4cc25902ba1560a6652527f938494849624111d88c64542098ef473c3921bf0dc86c63551920c485e82de1698af457027f136879038e1ab0c285d42c41580a184cc23a0fc07983981b007503981640b00410200098044021009804801800a0048018004000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1907c7c5af6d5f44b9da4b3643917a88f419da90ce963630ad7cebbd5d32b2d56ea9554028bd22490346d22d91248443fe9f48f9c7be3d59e64e706f73599a24ce45972c19584a984fb1ef0f3c74c3821af0c4059229e14d0a284ee26511f08a84382160e4870835618f0a5850c26c12707783a01c40db05b026c12007502f816407a027010806402e013009003001600a003000c004000 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
def record042_frame001_indices (c : Fin record042.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaafaa1a80a6c9f19cd9c79b199d98497796195695092b9238dc8d478d73e72c6bf6af6a469968567d6075f45e95d95ce5ba57c55554e53b5344e04a643842841c3e43dc36735734731a30c2e02c32bf2ac28924723422921c2112051c31b91b01a118517817416616113e13512b12110c0f80f40e80df0ce0cb0bd0b80a709d07506f06405f03703503302702602301301200c00a008006003002 } : Fields).get c.val)
theorem record042_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record042.data.requiredEdges q = true := by decide +kernel
theorem record042_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record042_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record042) (record042.maps 1) (record042.inverseMaps 1) record042_frame001_indices (Fin.ofNat record042.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record042_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record042) (record042.maps 1)
      (record042.inverseMaps 1) record042_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record042_frame001_links_0000 record042_frame001_links_0064)
theorem record042_frame001_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) : Supported record042 1 :=
  of_group record042 1 (embedding record042) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record042_frame001_indices record042_frame001_graph record042_frame001_links
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (Fin.cases (record042_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1001.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1001.count (({ width := 12, code := 0xaa9a9ca84a67a2aa219f19cd9c79b199d98497796195695078d6995ce55553b4fd4de4a64644544434384133e43dc39c38837635e35731a30c3072e02d92c32bc2ac28824723421c2051c31ba1af1a118517816616113d13512c12110c0f80e80df0ce0ca0bd0b80a709d06f05f04704503d03703503403302c02702602502301301200c00a008006003002 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1001.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1001
    Papers.RationalityTen.SharedFrameCatalogue.group1001_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
def record043_frame002_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x767ec5d539d71ae2fbab686ced89af35b6b2d4da734bd3f931005cab7166ec8182ae15acb2160aae52ea51392654b4941272394628b504a033d078cec1bf340648c31782aa53ca393d2624a48f11c20a3fc7c8ed1c2358668c71782e0540a51302383685d08e1141e83706a0d01982c04e098128230260480600a01001801802 } : Fields).get c.val)
theorem record043_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record043) (record043.maps 2) (record043.inverseMaps 2) record043_frame002_indices (Fin.ofNat record043.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record043_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record043) (record043.maps 2)
      (record043.inverseMaps 2) record043_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record043_frame002_links_0000 record043_frame002_links_0064)
theorem record043_frame002_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 2 :=
  of_group record043 2 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record043_frame002_indices record043_frame002_graph record043_frame002_links
def record043_frame003_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0761.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0761.count (({ width := 8, code := 0xa5a4a3a2a1a09f9e9d9c9b9a99989796938b847d7974737271706f6e6d6c6b6a696867666564635f5d5958555352514e4b474645444342403f3c3b3a393837353331302c2b2a2926231d1c1b1a19181716151413120d0c080706040302 } : Fields).get c.val)
theorem record043_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0761.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (embedding (N := 44310) record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (embedding (N := 44310) record043) (record043.maps 3) (record043.inverseMaps 3) record043_frame003_indices (Fin.ofNat record043.n i)) 64 93 :=
  interval_of_check _ 64 29 (by decide +kernel)
theorem record043_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0761.localPairCheck (embedding (N := 44310) record043) (record043.maps 3)
      (record043.inverseMaps 3) record043_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 93 record043_frame003_links_0000 record043_frame003_links_0064)
theorem record043_frame003_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 3 :=
  of_group record043 3 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group0761
    Papers.RationalityTen.SharedFrameCatalogue.group0761_facts record043_frame003_indices record043_frame003_graph record043_frame003_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (Fin.cases (record043_frame002_supported hcells) (Fin.cases (record043_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x8fd1da28c4e88f1021f4388690c216c2a84b08a1041e83305a07c0b7f2fdde23bc772ea5ce38c6fada9b3b5e69cc6189b04600b916c2c9590b0d5e2ab5409d93826c4d29812ea19428798ee9d43a272ce51c537e698c91862fe5e4ba16a2cc578ad1402744c08f91921a418810fb1c636c698c617a2e85a0ac14427c4c88d1142083e06f0dc1542a0520720d81302003a0640b81302401801802 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1960ca35baad9b62fb0a5796b9b5adac9555ea7d4dba68d2f2951440a1bcfba7a333898fc66a3050c6858b1b1834ba0589abc1590ab454c24311ee8af44c211103e7f83f41f5cf947b939c1b98cd85df2de1650b005641ec0f0c6f63641880bac5882b41518a5850a243116887c42e21010487f83f61f00f687683a61ca0e186e03601a00cc86383181860bf85e029814609b84a823c11708a84382040ff07a03c81d60e306c03580fe07d03a81bc0be05e02d81640aa04702280f406e027013008c04201d } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
def record045_frame002_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0814.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0814.count (({ width := 11, code := 0x620c37782eddcbb9371ae25c2b816dada5a6b4b68ed058fb1d612c0d6ead953aa6537a6b2b64cc898e11aa31c5e8b2f5de6bb3754e1dbbb666c0d6daa34c658c6183aea5c8b756bad04d699129a4b4648950ca16426841061ea3a4714df9b936068cd099732a614bf97c2e4594af152296508a093e26e4c0871051ea3946d0d11a0328608c01662c8560a613c2743c0760e21b42e85c0b215c2984708a0f41b82704c08c1081d } : Fields).get c.val)
theorem record045_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record045) (record045.maps 2) (record045.inverseMaps 2) record045_frame002_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0814.localPairCheck (embedding (N := 44310) record045) (record045.maps 2)
      (record045.inverseMaps 2) record045_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame002_links_0000 record045_frame002_links_0064)
theorem record045_frame002_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 2 :=
  of_group record045 2 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group0814
    Papers.RationalityTen.SharedFrameCatalogue.group0814_facts record045_frame002_indices record045_frame002_graph record045_frame002_links
def record045_frame003_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0813.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0813.count (({ width := 11, code := 0x47e8f515628c4788b10a2043d8770da19c2c8570aa1442183f06e0cc0f81afedfcbee7d8ea5ce38c6ecdc1b4b666bec6189b04600bb170ad259eb2d63ac1556a65442764e09ad3426142c838fe9f83cc774ea1d139a720e21ac32e624c097a2ea5a4b395d2b652ca29412764bc96120234430859072063f0720df1a8328610bc1762d4558aa1422804d09411822c3786e0d21942a8540a41402604007e0e41b02604a0881001d } : Fields).get c.val)
theorem record045_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record045) (record045.maps 3) (record045.inverseMaps 3) record045_frame003_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0813.localPairCheck (embedding (N := 44310) record045) (record045.maps 3)
      (record045.inverseMaps 3) record045_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame003_links_0000 record045_frame003_links_0064)
theorem record045_frame003_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 3 :=
  of_group record045 3 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group0813
    Papers.RationalityTen.SharedFrameCatalogue.group0813_facts record045_frame003_indices record045_frame003_graph record045_frame003_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (Fin.cases (record045_frame002_supported hcells) (Fin.cases (record045_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa70d33a96d33c9924c3a0db05281dbe61f02f6f754b9d9bd2db66af352981eb5a5892bd95b6abf5502a31504a694f7269931496f4a9a4d124091647ea3bd1c68da468a31517c8b84581fc4e7e6b73569a50d1467533118d0c565ea2b11560a7e53529014349be4d626092ec9664ae253127c91e48a1ae0d0464c30416b8b1c53e28a13a896c47222d10d88484041f00f106f034e1920bc0558294138097847c21a0ff07b83c81d40e206d81f40e606402080dc05001100700340180090040018006002 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0xabeadaaea3a869fa3a8ca2a88a1e86a16829f2799ce7095e499063b8de328b22989a228621082a06805fb7e1f57c5ed79de3779d8755d2739c36d1a46859d66d976498b629845d1715b56b59d6256d5a54d505314a519414e93947916441083fcfc3c8ea390dc34cd0328c8310c02ecb22a8a4270932408a220842007b1d8741c06c19c56148490d82f08c110380d030090200600c02 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (embedding record046) hcells Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x29bd4caa594cf264930e8f1c77239d18e8bfc5a223d10487641b20a10397cc3e05edeea973b37a5b6cd5e6a52b6d59caa054129a52de96249a24591fa8da46a23151708b03f51ebce707063639adcd3c69433e19d4cc464f31a18acbc65b12b91588a9253f2939480a1a4fa26f93589904c125c12cc9564a624f926091e48a1a08ca46082d71638a284ee25b11c88b443621010107c03c41a70ca05e02ac14a09c04b423e10d07f83dc1e20ea071036c08e04502080f407603701700b005001100700340180090040018006002 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0xabaacaaaa3a869fa769ca6e9aa6296a5292a428da2e89a2287a1a85a0a7c9e6739c2378d62c89a2281a047edf57c5e3785d8749ce709be6cdaf699a46799d661976499062d8a60d7f5d9745b96d5a1675896056d5a555535354c51d465053f4e93945911420ff3f0ea394dc34cd0328c7310c02ecaa2949c24c9022887210801ec761cc701b0670e8390d8330c82f09c2608c110380d030090200600c02 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x3b3f62e79ceb8bee8da1b134868fd1b9f334656ca78d71962dc3583afc5e7bc5732e5daeb515ee5bc017c8f51e53ad74ce55bc320628bbd70ac9584ae95b2ad558a915029652a9c92d25049c8fd1e2354668b50d21141280cfa1bf324618bc1702c4584aa94f29450ca093d2644147f8f91da3846e0d619a31c610bc1702b45408e0da11c2284107a0ec1b82c04c094118220260300500901001801802 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x7c5f81ee7ccf93f1bdd3b9f72ee1db7b4763ebfd67a9f52e99d039cf36e53c838df1ae33c6384701d3da6747682cf791b17603bd74227ecec9af34656ca491f1f237c1d80af31da2de5aab0156aa04e69a12ba42478808f89dd3ac72ce39bd3726c4d519f33864cc61812fa5ccb79672c0554a912523a448831021ee3cc760e01b2340660c51722c83d87a0ec1702c8580780ec1b82103c0740c81702601801802 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (embedding (N := 44310) record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (embedding record050) hcells Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x60cc1579ae9da6b355fea352fa273f677cc5979246424778c91721dc2c84106e07c0a809001fc3e7792f09debb8760eb1ce39a704dc9b23606a0d2593b1a5e8b9569acd57eae5592ac546a3936a634ba95926a474688cd0da0b3fa7e4f51e539a700b015129c5089e9372643f47b0f21d6398710d71582684b08b10c1a02d8390500640b81301802c0480800c01001802 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x64972296e5b645436a134d7a66d0ba8392ec968cae25331948be446a202c1a5edac55590a8c537a941476a134e524d521e8ea46ba2a113a86642920fd03e7fa3f49b98d4e5e12ca1560a7651c283937c92c4011ed8ed87463741b48cc863c30b1758b1856a24311688404121fe0fd87c03da1e60ef87503a21ca0df06d43541a00cc864c3161860bf85c42d415a0aa053028c13e09b849424411d08784202020f407903a81be0d803f81f40f207303001640ac055023811408203b014008403c01d } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (embedding record053) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
def record053_frame002_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0820.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0820.count (({ width := 11, code := 0x17d6f7db0b5560ec157caf558ab053aa734b693d05a093ae72c628b50ee1541982102201bf77cef1dddbaf754e75ccb87702dedb8b676c4c958c2f45c6b2d602b7562a894726b4b693122a354648810d214414800fd9d03846b8d219832e620c39802f45a8b49632a853ca494427e4e899930252460891001f23d0770e81c63686c0d518a2f45a0a91502884c8950e21bc368680b61542905108a10c1f8390500840f01d } : Fields).get c.val)
theorem record053_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record053) (record053.maps 2) (record053.inverseMaps 2) record053_frame002_indices (Fin.ofNat record053.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record053_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0820.localPairCheck (embedding (N := 44310) record053) (record053.maps 2)
      (record053.inverseMaps 2) record053_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record053_frame002_links_0000 record053_frame002_links_0064)
theorem record053_frame002_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) : Supported record053 2 :=
  of_group record053 2 (embedding record053) hcells Papers.RationalityTen.SharedFrameCatalogue.group0820
    Papers.RationalityTen.SharedFrameCatalogue.group0820_facts record053_frame002_indices record053_frame002_graph record053_frame002_links
def record053_frame003_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0x1676cdd82afd5c6b856cad5586b054ba95512a0d2ea5b4828ec6b8bf11a19c2183504a063fd7e0f2dde3ae74ee55c83806eedcdb2354694c4583aec5aab055aaaa54aa554326b4bc9392423c4708a10fa1840a7e8f91c5370690ce99532861cc31802f85b4b61682c0568a89492884f89a9302564708a1072043f07b8ee1ce3606b8d218c2f85a8ab15228c4c8930c81883005d0a0124230450780ec1c03504e0840f01d } : Fields).get c.val)
theorem record053_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record053) (record053.maps 3) (record053.inverseMaps 3) record053_frame003_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record053) (record053.maps 3) (record053.inverseMaps 3) record053_frame003_indices (Fin.ofNat record053.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record053_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record053) (record053.maps 3)
      (record053.inverseMaps 3) record053_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record053_frame003_links_0000 record053_frame003_links_0064)
theorem record053_frame003_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) : Supported record053 3 :=
  of_group record053 3 (embedding record053) hcells Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record053_frame003_indices record053_frame003_graph record053_frame003_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (Fin.cases (record053_frame002_supported hcells) (Fin.cases (record053_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record055_frames_supported
theorem record056_frame000_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    Supported record056 0 :=
  of_identity record056 0 (by decide +kernel)
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xab6a99a90a85a7aa4ca219d49bd9ac98f98c98996f93e91f91891790b9079028f68e98e78e58e48e28df8c28a78488087f77f07e27d17ca7617517036e960f5f55a859e59358c58257750a5044fd4ed4ac49a47f45d3da3a439237734232f32b31b3143103002a827e25022622321d21520f1ef1c71ba1af1ab1a019919217f15913112611f10c1010f60f20e70db0d40ca0c60c208507f07005d05804a04403903602602302101e01300f008001000 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record056_frame001_links_0000 record056_frame001_links_0064)
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00076

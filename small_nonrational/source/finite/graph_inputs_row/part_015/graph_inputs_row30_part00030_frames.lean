module
prelude
public import GraphInputsRow30Part00030Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups047Checked
public import SharedFrameGroups048Checked
public import SharedFrameGroups049Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups052Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups055Checked
public import SharedFrameGroups056Checked
public import SharedFrameGroups084Checked
public import SharedFrameGroups086Checked
public import SharedFrameGroups093Checked
public import SharedFrameGroups094Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups105Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups112Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030
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
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSmall.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record005_frames_supported (hcells : ∀ c, record005.data.cells c = FacetUniverses.FullSmall.cells (embedding record005 c)) :
    ∀ f : Fin record005.g, Supported record005 f :=
  (Fin.cases (record005_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record005_frames_supported
theorem record006_frame000_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    Supported record006 0 :=
  of_identity record006 0 (by decide +kernel)
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSmall.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSmall.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSmall.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
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
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x747b6c999ab9f56caa314a0a134aba50d1f48e6460a2b113488a3f49f6cf4a7933359694ab051c26f908c81e3c61d90e346f03661ab0ad454e27112f88503f41f30f587943bc1d60e8071c3841b40cf862830216c0b2857c2a4144097848423210c07b03c01aa09504902040e406f03181800ba05b02d015c0ac05502480e806e02b014009404602200f807803a01b00b004c022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record014_frame001_links_0000 record014_frame001_links_0064)
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
def record016_frame001_indices (c : Fin record016.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xfa274936e5a66cec666ae6d5b2a5a50fa84d2b694448623911a88aa44d221d08482d4069fe0fd27b93d29e4ccce5a529313ac9be4272080f607603a01bb0d986a630e17c8b645882b514289c44be21410688203f41e50e807203761ad0cc06282e616c0b2852c28813c09b04bc24e121089842c1ee0e806a81f00f207203781a00bc05b02d01600ac05502201040740370180098046022010007803a01b00b004c02200f007003401600a004802000c0050018008002000 } : Fields).get c.val)
theorem record016_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record016.data.requiredEdges q = true := by decide +kernel
theorem record016_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record016_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1) (record016.inverseMaps 1) record016_frame001_indices (Fin.ofNat record016.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record016_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record016) (record016.maps 1)
      (record016.inverseMaps 1) record016_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record016_frame001_links_0000 record016_frame001_links_0064)
theorem record016_frame001_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) : Supported record016 1 :=
  of_group record016 1 (smallEmbedding record016) (small_cells_exact record016 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record016_frame001_indices record016_frame001_graph record016_frame001_links
theorem record016_frames_supported (hcells : ∀ c, record016.data.cells c = FacetUniverses.FullSmall.cells (embedding record016 c)) :
    ∀ f : Fin record016.g, Supported record016 f :=
  (Fin.cases (record016_frame000_supported hcells) (Fin.cases (record016_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record016_frames_supported
theorem record017_frame000_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    Supported record017 0 :=
  of_identity record017 0 (by decide +kernel)
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1f32e9c6db34c99d6cd05cdab7558ea5c510a8412ae935487a3891ae8a844ea21d08482f4069fe8fd27da3dc1e8cf226672d4964ca504ed26e108c8023db1d70e8c6e83691a98c385f62d91630ad454c284137897442820d10407e83ca1d00e406b434a1980c8062830417c0ba05642a414b0a204d825e12108c04282060fc07b83a41a807c03c81a80d206803181800b005602a811008203201880c0056028010007803a01b00b004c02200f0070034016009004001c00c005002000c004000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
def record017_frame002_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x199ac5d5fc2e496bcb5055f296d4989eb4dda6d127e91b477a30d17088c44321d104080e3f61f68fa47c13c99df0ed46c032a1918bd25bc2da9524a54505271136896e4b325211908ac43c21710988343f81f30f686c234e19d0c545d02bf15809b44be24711c88c4446213100071836a1a80ce06142f21640aa84bc24411608483ac18e07c03c81a80d206803181800b005602a811008203201880c0056028010007803a01b00b004c02200f0070034016009004001c00c005002000c004000 } : Fields).get c.val)
theorem record017_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 2) (record017.inverseMaps 2) record017_frame002_indices (Fin.ofNat record017.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record017_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (smallEmbedding record017) (record017.maps 2)
      (record017.inverseMaps 2) record017_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record017_frame002_links_0000 record017_frame002_links_0064)
theorem record017_frame002_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 2 :=
  of_group record017 2 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record017_frame002_indices record017_frame002_graph record017_frame002_links
def record017_frame003_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x71d6ec6c369a6806796165d75d15a358157c53252350a4ef4e84c84c44bb49949147f47446e46745244543a3da39b3953623453402f62e72cc2ac2a728c28827f25924e24023823222b2162061fd1c51bf1bb1ae19617f17c16515c14f14614013d13a13411e11a11410d1000f90ed0e90de0d90d30ce0c40b207b07806906806706205f05705505404404103203103002b02802001e01d01b01601301100f00e00d00b009008007006005004003002000 } : Fields).get c.val)
theorem record017_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 3) (record017.inverseMaps 3) record017_frame003_indices (Fin.ofNat record017.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record017_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (smallEmbedding record017) (record017.maps 3)
      (record017.inverseMaps 3) record017_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record017_frame003_links_0000 record017_frame003_links_0064)
theorem record017_frame003_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) : Supported record017 3 :=
  of_group record017 3 (smallEmbedding record017) (small_cells_exact record017 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record017_frame003_indices record017_frame003_graph record017_frame003_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSmall.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (Fin.cases (record017_frame002_supported hcells) (Fin.cases (record017_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
def record018_frame001_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xe3b6bdb4d9a16cf66772f45640aaf53ba999368943485a3e91da8e8470a3691a68ca462a2f916a8b0454a2891368924459df0daa67131c18a0b0051c271934c98c4c125d12cc95a4a424f926091e48a24191f48ee46f2348e446302d91638aa453228a13d096c49822d10e88384001c60db069c32e1780b4852827412b08e83dc1e00e9071036c1a807703901bc0d4069034018c0c005b02d00fc07403701900c406002b014008c04401b00b004c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record018_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1) (record018.inverseMaps 1) record018_frame001_indices (Fin.ofNat record018.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record018_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (smallEmbedding record018) (record018.maps 1)
      (record018.inverseMaps 1) record018_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record018_frame001_links_0000 record018_frame001_links_0064)
theorem record018_frame001_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 1 :=
  of_group record018 1 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record018_frame001_indices record018_frame001_graph record018_frame001_links
def record018_frame002_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xf96747b709a68ced669ae7d5b2a5e511a8412ae8e64562269106879433a15508a82b4112040fec7ec3ee1f2cf747a23c819acb4a52a27793708463b21bc0d9869e3451998c846222f71770b705842b81540a5c50c26e12e08503d61d60e807083761b40d6867c33018a0c185f02ea1590a9052c288136097848423411308603d41dc0e707003641a607703901bc0d4069034018c0c005b02d00fc07403701900c406002b014008c04401b00b004c01c00d006002c014009004001c00c005002000c004001 } : Fields).get c.val)
theorem record018_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 2) (record018.inverseMaps 2) record018_frame002_indices (Fin.ofNat record018.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record018_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record018) (record018.maps 2)
      (record018.inverseMaps 2) record018_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record018_frame002_links_0000 record018_frame002_links_0064)
theorem record018_frame002_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 2 :=
  of_group record018 2 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record018_frame002_indices record018_frame002_graph record018_frame002_links
def record018_frame003_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0660.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0660.count (({ width := 12, code := 0x71a6df6aa67264b63a5ec5a657555654c4f94ca4a949e49449248647b46f46145c44d43743342941c4134023f63b336d33c31d3132c029127026525b25624d2402382282212141fe1fa1ed1e41da1c91bd18f17016015d15414f14914313813212912511f11810a1051000fb0f00ea0e00da0d40cf0be0b80b30af0aa0a706f06b06806306206105c05905405303e03a03703203103002b02802302201b01601300e00d00c00b00a009008007006005004003002001 } : Fields).get c.val)
theorem record018_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record018) (record018.maps 3) (record018.inverseMaps 3) record018_frame003_indices (Fin.ofNat record018.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record018_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0660.localPairCheck (smallEmbedding record018) (record018.maps 3)
      (record018.inverseMaps 3) record018_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record018_frame003_links_0000 record018_frame003_links_0064)
theorem record018_frame003_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 3 :=
  of_group record018 3 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0660
    Papers.RationalityTen.SharedFrameCatalogue.group0660_facts record018_frame003_indices record018_frame003_graph record018_frame003_links
def record018_frame004_indices (c : Fin record018.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x4e59a330257c9c92d1e62643083704ded3b6734e41c1b7f6f2dd1b73686c6d69a8b4c68cd019db35660c5970abd542a5d32a494688b11021b42c841062053fe7dcf71e93c4774ec1d239a694c497a2f05b0b39602b2530a213625e4a09090a2043f07a8e81c0348658c417a2a45189f1382604a06c0d0194308600be1682b8520a20f41c0350600bc1702a04e08c1101b02c04c0700d01802c0500901001c0300500800c01001 } : Fields).get c.val)
theorem record018_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record018.data.requiredEdges q = true := by decide +kernel
theorem record018_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record018_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record018) (record018.maps 4) (record018.inverseMaps 4) record018_frame004_indices (Fin.ofNat record018.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record018_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record018) (record018.maps 4)
      (record018.inverseMaps 4) record018_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record018_frame004_links_0000 record018_frame004_links_0064)
theorem record018_frame004_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) : Supported record018 4 :=
  of_group record018 4 (smallEmbedding record018) (small_cells_exact record018 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record018_frame004_indices record018_frame004_graph record018_frame004_links
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSmall.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (Fin.cases (record018_frame001_supported hcells) (Fin.cases (record018_frame002_supported hcells) (Fin.cases (record018_frame003_supported hcells) (Fin.cases (record018_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSmall.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSmall.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSmall.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
def record023_frame001_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x5c02df16deb62585abdd5aeab7555aa5d4eea574eba70934297e4b9257527891946f233914287439a1ca4e387163631a88d046713329904c426102d21610acc5592a794bca2250426c92e09264821e20dbc6c830f1810bf05d0279135897049623c11888884222020f9064830c1780b505782aa14709c84b422a10706302680f607903c01640ae056021010408002000f8078026012007803801a00a0048010006000 } : Fields).get c.val)
theorem record023_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record023) (record023.maps 1) (record023.inverseMaps 1) record023_frame001_indices (Fin.ofNat record023.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record023_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record023) (record023.maps 1)
      (record023.inverseMaps 1) record023_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record023_frame001_links_0000 record023_frame001_links_0064)
theorem record023_frame001_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 1 :=
  of_group record023 1 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record023_frame001_indices record023_frame001_graph record023_frame001_links
def record023_frame002_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x76d76975b74e7267176fc6e56de6d26c36ae66865c64d6386326236085f15ca5c75bb5ad50e5024f54ee4c14a849148547b4674534463f83e43d03c33b93a038937d35334833d3372d328227b22a22021a2081c61bd1b41aa1a119a19118517c17213012711e1121091040fb0f10e80da0d50ba09a07b07907805905705604204104002001f01e01301200f00e00d00a009004003000 } : Fields).get c.val)
theorem record023_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record023) (record023.maps 2) (record023.inverseMaps 2) record023_frame002_indices (Fin.ofNat record023.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record023_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record023) (record023.maps 2)
      (record023.inverseMaps 2) record023_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record023_frame002_links_0000 record023_frame002_links_0064)
theorem record023_frame002_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 2 :=
  of_group record023 2 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record023_frame002_indices record023_frame002_graph record023_frame002_links
def record023_frame003_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0xa04fe77369acca5d2a94c9a451e8ec6a2d1288c3a15068240dfefa7b3cddeec75391bede6eb5da4d167b2588c3612f16eb65a2c55aaa54a753890472350c7a3c9d4e26d361a0c8602f94ca44e251188a411e8e46e36178a84a23110843e1e0d0643014098481e0e058281206028080200 } : Fields).get c.val)
theorem record023_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record023) (record023.maps 3) (record023.inverseMaps 3) record023_frame003_indices (Fin.ofNat record023.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record023_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record023) (record023.maps 3)
      (record023.inverseMaps 3) record023_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record023_frame003_links_0000 record023_frame003_links_0064)
theorem record023_frame003_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 3 :=
  of_group record023 3 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record023_frame003_indices record023_frame003_graph record023_frame003_links
def record023_frame004_indices (c : Fin record023.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0965.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0965.count (({ width := 9, code := 0xcd6672992c762f0d82c05faf778b7db6d567b2d8ebf5ba9d4aa14b9a4c65b2c9448e3f1e8e45e2b138441200ff7ebe5eaf374b9dc8e165afd7ab156aad529d4da59228e4622108813f1c8de6b33990c65f2c958a24f241187e3d1e0d06431138984a1b0d0642612078381a0a048100600 } : Fields).get c.val)
theorem record023_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.graphBitCheck record023.data.requiredEdges q = true := by decide +kernel
theorem record023_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record023_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record023) (record023.maps 4) (record023.inverseMaps 4) record023_frame004_indices (Fin.ofNat record023.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record023_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0965.localPairCheck (smallEmbedding record023) (record023.maps 4)
      (record023.inverseMaps 4) record023_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record023_frame004_links_0000 record023_frame004_links_0064)
theorem record023_frame004_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) : Supported record023 4 :=
  of_group record023 4 (smallEmbedding record023) (small_cells_exact record023 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0965
    Papers.RationalityTen.SharedFrameCatalogue.group0965_facts record023_frame004_indices record023_frame004_graph record023_frame004_links
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSmall.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (Fin.cases (record023_frame001_supported hcells) (Fin.cases (record023_frame002_supported hcells) (Fin.cases (record023_frame003_supported hcells) (Fin.cases (record023_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record023_frames_supported
theorem record024_frame000_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    Supported record024 0 :=
  of_identity record024 0 (by decide +kernel)
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0x9b4aa3d12833e9eaf378bbdd8e873391c4df6f36db2d76ab49a2cd65b258ec461b017cbc5d2dd6cb358abd5aaa4ea411e8d3d1e0ea71369acd0643014ca24e2511888411e8e47036178a846220f8783a1c0d86832180b8582a14098481e0e058281206028080200 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (smallEmbedding record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (smallEmbedding record024) (small_cells_exact record024 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSmall.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record024_frames_supported
theorem record025_frame000_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    Supported record025 0 :=
  of_identity record025 0 (by decide +kernel)
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x331d968ca264031a189cc385a52d15670b2c58fac55526a8b53fa9d14d0a604f0a71d3549904b7252d25a92747ba38517e8b0446a1c4eac7423961c94df66d835f1accd5c6883359984be45b12b31584a6252329013489924b325012488143e31e38ef874e38c1b60d886b23391928c4c6022e31610ae04c024711a08884021b90d886643061730b50500260123085840017408103b81640ae0560210104080028013807c03c010007803801600a0048010006000 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (smallEmbedding record025) (small_cells_exact record025 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSmall.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcc765a3289900c6862730e1670b1f58aaa814fea68530264125a8f7470a3210e274d3a11cdce587253761b8cdb06c935f1accd3e69934419f0cd66612f3176cb885b12cd15f8acc553298948ca2a50827513489844b325012487c63c71df0ea871836c1b10ce464a3131818b8c5842b812e891c4682220ff86e43321830b985a028013009184382000ba02b815809e049021810808204001f80a8050027010807c03c010007803801600a0048010006000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
def record026_frame002_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0632.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0632.count (({ width := 11, code := 0x49191f21a3e4788e71ae16427842ff5fcbf37d8e99c33776e6dbdab2f65e8bc1752e65a8b4966ac7582af159ab255caa15129b4dc9b533a5c4a69211d2314548911121e424810fe9f93e47a8d219632061cc197b2ea5acb41622c055ca4942236454879071fc38c6e0d519e330608bb1702c8568960a6148258470861082084007e0a81402704207c0f01001e0380580a01201001800 } : Fields).get c.val)
theorem record026_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record026) (record026.maps 2) (record026.inverseMaps 2) record026_frame002_indices (Fin.ofNat record026.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record026_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0632.localPairCheck (smallEmbedding record026) (record026.maps 2)
      (record026.inverseMaps 2) record026_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record026_frame002_links_0000 record026_frame002_links_0064)
theorem record026_frame002_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) : Supported record026 2 :=
  of_group record026 2 (smallEmbedding record026) (small_cells_exact record026 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0632
    Papers.RationalityTen.SharedFrameCatalogue.group0632_facts record026_frame002_indices record026_frame002_graph record026_frame002_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSmall.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (Fin.cases (record026_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74070d6ea68267f67867266d66863a63562c62361d61356352f52451e51250c4d34ca4c44b84b043242f42842241d4183ae3a93a03973913873112d92d42ce2c22bc28325124b23f23720c2071fe1f71ef1e81db1d61cd1c61be1b71b01ac1a81a419819118a18317d11310d1070fd0f70f30ed0e30dd0da0d50cf0af09c09b08707706005f05705604903f02402301f01e01b00c00b00a009004003000 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
def record027_frame002_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0633.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0633.count (({ width := 11, code := 0x5109d33364a49391f232434848df1b232c628b515df4bc677aee1d6ba970ee09bcb736d6c899031e632c5d892d55a4b3963ac557a9c127a4b48a8ed1ba153dc7a8f09d93706d8d81aa348678ca19231a614c017a2ea5b8b39642ba55ca894c28e3c4758e41b234c678c917c2e05b8b215a25c440870ee1b02c05709e1382203c04808c0f81e0360300580a01201001800 } : Fields).get c.val)
theorem record027_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record027) (record027.maps 2) (record027.inverseMaps 2) record027_frame002_indices (Fin.ofNat record027.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record027_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0633.localPairCheck (smallEmbedding record027) (record027.maps 2)
      (record027.inverseMaps 2) record027_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record027_frame002_links_0000 record027_frame002_links_0064)
theorem record027_frame002_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) : Supported record027 2 :=
  of_group record027 2 (smallEmbedding record027) (small_cells_exact record027 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0633
    Papers.RationalityTen.SharedFrameCatalogue.group0633_facts record027_frame002_indices record027_frame002_graph record027_frame002_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSmall.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (Fin.cases (record027_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record027_frames_supported
theorem record028_frame000_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    Supported record028 0 :=
  of_identity record028 0 (by decide +kernel)
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1a3ad0f680b2f9956ca263db0dd694b4559c2cb163eb15577ab5d57caa8545a9d14c0a5b51628653bc9b84cda6412b8939496a4391ee8e146221c50cc84d416a060ea87523a39cf0e6272737e1b94d966b434c99f0cc265d31b9898be65d42de96ccb1a5712b3153ca7a52f28d93489964b524e123873638c1bd8db06c430417a0b4c57025911a08883f81e00e186e429e14009804402020ba049024410205702b012403e01e00d804402000f00700300140090028010006000 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
def record028_frame002_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6b36ae6a969769268d67f67263162e62b62661e6186045fd5f05e25cc5c05ae5a759158456555a54c54352a51b50f5004f24e54d54bb4b74b14a64a045f45d45845344c44642d4274194063f53e93d73cf3ba3aa38a38036f36334f33f3343243173072f92e02db2d52ca2c424023322721d2131da1d51c41b117a16615d14a13e12c1210e30d60cd0bc0b809808608507b05505404701f01e01b01101000f00e00c00a009005004003000 } : Fields).get c.val)
theorem record028_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record028) (record028.maps 2) (record028.inverseMaps 2) record028_frame002_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record028) (record028.maps 2)
      (record028.inverseMaps 2) record028_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame002_links_0000 record028_frame002_links_0064)
theorem record028_frame002_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 2 :=
  of_group record028 2 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record028_frame002_indices record028_frame002_graph record028_frame002_links
def record028_frame003_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x21bc3486309e1342283d049f1be17bcf71ecbd6798f19de3b3752e69c8b8e6fadd9b4b5f6aed41a1b3765cc918d313616be17aaee5cab81522a253ea754d297512a0d3d2714d09692824d47c8dd1321c428839009f53da790ed9d43986e4db1b034e688ac1512945049d12524846c898fa1de3946e8d61a232c560a41402544887e0e41c43484b0941040f81e0360440800f01c0300500900a01001800 } : Fields).get c.val)
theorem record028_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record028) (record028.maps 3) (record028.inverseMaps 3) record028_frame003_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (smallEmbedding record028) (record028.maps 3)
      (record028.inverseMaps 3) record028_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame003_links_0000 record028_frame003_links_0064)
theorem record028_frame003_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 3 :=
  of_group record028 3 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record028_frame003_indices record028_frame003_graph record028_frame003_links
def record028_frame004_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1fd2fc67ce3b45d54e96717b6d1800bf95f12f39770ba35a5acc1610ae155a2a314c4a57518286d37e9974b8a57d2428fd47523311708a444520c104a8113fa1f88d986c53571a68d0866f30b97f0ba85ad2c01560a5c52327e139c91646321e90ac7da3c91db0e607083701ab0bf05e22dd1600ab84102010fd07cc3d81c70e106d034c1810b985b02be1520a204f422210a08183d81e00c8049024410205702b012403e01e00d804402000f00700300140090028010006000 } : Fields).get c.val)
theorem record028_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 4) (record028.inverseMaps 4) record028_frame004_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record028) (record028.maps 4)
      (record028.inverseMaps 4) record028_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame004_links_0000 record028_frame004_links_0064)
theorem record028_frame004_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 4 :=
  of_group record028 4 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record028_frame004_indices record028_frame004_graph record028_frame004_links
def record028_frame005_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x75d75975573372c72a7196f266666465b65164864262c62160d5fb5eb5db5ce5ca5b05a658356e55c55654052d5265155094ff4f04c94c44b64a249442c42942041a4114083f23e63d53c13b03a239439037636934933332431c3042f52ec2db2cf2c32b628f28a27c26425a1d91d01c81bf1b919619017f17014d14013712c1221161100ec0e60df0d40d00ac08e08d07f05505404901f01e01b01101000f00e00c00a009005004003000 } : Fields).get c.val)
theorem record028_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record028) (record028.maps 5) (record028.inverseMaps 5) record028_frame005_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record028) (record028.maps 5)
      (record028.inverseMaps 5) record028_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame005_links_0000 record028_frame005_links_0064)
theorem record028_frame005_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 5 :=
  of_group record028 5 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record028_frame005_indices record028_frame005_graph record028_frame005_links
def record028_frame006_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0654.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0654.count (({ width := 11, code := 0x2764eb9cf3626b4d39972fa42c8490720a3f47a8d91962dc5288d0fa19c2f83f05e00bf17cef81e63c1772ea9d039570ada5b235b6a0d2591321640c7d8db17612bf979ae75b0b39602bb54ea7142a7a4e09ad2e2524989011c230444819009f83da798cf99a32a63cc51722d8580aa12e23e468871021ea3c0618bb16c2a8520911001fc3a84e09a1180f81e0360440800f01c0300500900a01001800 } : Fields).get c.val)
theorem record028_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record028) (record028.maps 6) (record028.inverseMaps 6) record028_frame006_indices (Fin.ofNat record028.n i)) 64 114 :=
  interval_of_check _ 64 50 (by decide +kernel)
theorem record028_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0654.localPairCheck (smallEmbedding record028) (record028.maps 6)
      (record028.inverseMaps 6) record028_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 114 record028_frame006_links_0000 record028_frame006_links_0064)
theorem record028_frame006_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) : Supported record028 6 :=
  of_group record028 6 (smallEmbedding record028) (small_cells_exact record028 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0654
    Papers.RationalityTen.SharedFrameCatalogue.group0654_facts record028_frame006_indices record028_frame006_graph record028_frame006_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSmall.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (Fin.cases (record028_frame002_supported hcells) (Fin.cases (record028_frame003_supported hcells) (Fin.cases (record028_frame004_supported hcells) (Fin.cases (record028_frame005_supported hcells) (Fin.cases (record028_frame006_supported hcells) (fun j => Fin.elim0 j))))))))
#print axioms record028_frames_supported
theorem record029_frame000_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    Supported record029 0 :=
  of_identity record029 0 (by decide +kernel)
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3475a1ed0165db2a1942c395f72efd752b495a3ace965cb2158b2b815a4ab955326d533098f4c3257927692e486a3d91c08c4438a12906081b3aa1d48e8e73c3989c9cdf86e53659ad0d3267c3309974c6e6262d19628adc56528d934890c45f2280fe87e83e51ec0f2477e3a81cf0e386fc36e1b18d7468e3321900c105e82d315c0a8853027b13487f03c01c30dc859c29a13e09704402020ba04381c40de06e02b8158092025012008c03e01e00d80300140090028010006000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
def record029_frame002_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x14fe9dd33a3b45e894f09b132a634a99512824e49892b2224247d8ed09e0f418827011fbbef7c8f6de93c9758e85ce3956a0d31a4b43682cf195b21624c1d7d2f15cab85692c9534a5147a884e094d162234387f8fd1f03d278cef1d53a0728e09bc36a6c0d49a233c660c91842ea5bcb495f2b049c8d90d20836c6a0cb1882dc588930f019c3306509e138218240460880f81e0360300500900a01001800 } : Fields).get c.val)
theorem record029_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record029) (record029.maps 2) (record029.inverseMaps 2) record029_frame002_indices (Fin.ofNat record029.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record029_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record029) (record029.maps 2)
      (record029.inverseMaps 2) record029_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record029_frame002_links_0000 record029_frame002_links_0064)
theorem record029_frame002_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 2 :=
  of_group record029 2 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record029_frame002_indices record029_frame002_graph record029_frame002_links
def record029_frame003_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x85484884081480e8057c379578077673373272a72471c7176f66f36e96dd65063f63562f61d6065f75e65d75cc5bc58557556b5604e94e34de4d94d54cd4a949c48647145e44f43a43541d40f3b63ac3a539d37233b3022ef2e52ae2aa29c29328727c26f26725e25124a23d23622d22421b20e2071f11dd1d11ca1c11b717816415214710f1040fb0f20e30dc0b008206e06c06b05405304702502402301f01e01b00c00a009005004003000 } : Fields).get c.val)
theorem record029_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3) (record029.inverseMaps 3) record029_frame003_indices (Fin.ofNat record029.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record029_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record029) (record029.maps 3)
      (record029.inverseMaps 3) record029_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record029_frame003_links_0000 record029_frame003_links_0064)
theorem record029_frame003_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) : Supported record029 3 :=
  of_group record029 3 (smallEmbedding record029) (small_cells_exact record029 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record029_frame003_indices record029_frame003_graph record029_frame003_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSmall.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (Fin.cases (record029_frame002_supported hcells) (Fin.cases (record029_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1aa6d4a69f34c99dccd6659b24590ac6d62530a170ab765b4ad8d612ae55642add552a85534295d30691e48023e50f884a41d2028ff47353981ca8e4871d38b9ae4d646a23491a08ce26583289904c626213081660b1c5722ab150ca7251d28093e09e84ee274936c9964a524111c88d245b227910c87442c2100eec73c37e1b78d6c67c31e1878c145fa2f61780b7c57228d13c89a44b224b11e08bc43e21110106542d015c09b84ac24e0f407203781a804f02480fc0540280138098048023010807c03c014009804802000f007002c014009 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record030_frame001_links_0000 (interval_append _ 64 128 130 record030_frame001_links_0064 record030_frame001_links_0128))
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x1b6cda16c1357da3ad08674b319974cb165232597d6bc35cfae2d692b2157eaba55b8ace5602ae538c95b493244d15087343021010727893c01db4eb674739a1b7cdac6c33589a74d1467a33a99bccd066132d1788ba45b12c495d4ad855129a9490a3450827d13a09be4c4254125c91a47b23691948c245b22b0fa87803951bf0da869e33018f8c405f82ec16d8b2455c28f13f09bc4b624b11d08c845422310e06942ca15209684842340f007203741a604f02480fc0540280138098048023010807c03c014009804802000f007002c014009 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record030_frame002_links_0000 (interval_append _ 64 128 130 record030_frame002_links_0064 record030_frame002_links_0128))
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x1ec3d4798f19e03bc768eb9d63a8740e69c43806f2dd5b5b636b8d61aab4d68cd09902fe5e2bb1652bd570aad5327e4f69e13a2704d895d2a25149a92522a4047a8e91b23245c89d12a1a41a821031fb3dc7a4f39e33c0770ed1cf3846f4dd9b73686c0d71aa34e678c99842f65ccb41592a0524a21402764dc9611d228434841041fe3f07b8f31dc348600b91522884f88f1102144104507e0dc1402604a0901102103e0740e0140260480800f01c02c05009 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record030_frame003_links_0000 (interval_append _ 64 128 130 record030_frame003_links_0064 record030_frame003_links_0128))
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
def record030_frame004_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0xf0fbded7b0eafa5e7798e5b90e2383dbf67d835dd4b4ad0f40cf735cbb2bc2eecb82dbaeeafaaa9da62709b66a99a6297a4991a438fe3b8de328be2c8a2248821985a0a7fdfb7e1ec785dd76dd7751d0735c16d9b26c1ac6a5a568d9f6719261d7a5c56a57d52525434f93a4d531499194410a415013f0f93d0f03acd1300b92a4a227c8f22085208430f4350a026094240882107c1d0701404c120400f0380b02809 } : Fields).get c.val)
theorem record030_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record030_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record030) (record030.maps 4) (record030.inverseMaps 4) record030_frame004_indices (Fin.ofNat record030.n i)) 128 130 :=
  interval_of_check _ 128 2 (by decide +kernel)
theorem record030_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record030) (record030.maps 4)
      (record030.inverseMaps 4) record030_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 130 record030_frame004_links_0000 (interval_append _ 64 128 130 record030_frame004_links_0064 record030_frame004_links_0128))
theorem record030_frame004_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) : Supported record030 4 :=
  of_group record030 4 (smallEmbedding record030) (small_cells_exact record030 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record030_frame004_indices record030_frame004_graph record030_frame004_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSmall.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (Fin.cases (record030_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
def record031_frame001_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0xd32648b0a1704b7d5bb2dc16d2b635802bdd5caad75642add540a97542a9dd4d0a574bda45921890547ea3d90e886242920fd05e8224091ffcfde7353981ca8e4871d38b9ae4d646a23491a08ce26583289904c626213081558a024f927a13b89d248223a91a48b644f22310e88584201dc0ed47483951c28dd46b03551a20cd464a3151838c005f22f316d0b585842ac14b0a044e026312a091446c22910d082c3321890be05982b41580a584d425212809104441e40e206f835410e08103b81800be05c02d815c0ac04f02480fc050027012008c03e01e } : Fields).get c.val)
theorem record031_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record031) (record031.maps 1) (record031.inverseMaps 1) record031_frame001_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (smallEmbedding record031) (record031.maps 1)
      (record031.inverseMaps 1) record031_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame001_links_0000 (interval_append _ 64 128 133 record031_frame001_links_0064 record031_frame001_links_0128))
theorem record031_frame001_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 1 :=
  of_group record031 1 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record031_frame001_indices record031_frame001_graph record031_frame001_links
def record031_frame002_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xd5f66332597bebd55e1aec573eb8b59eaccd642b0f57eaba55b2ad55672b1d580ab94dea54d28492f48ca42114088f43e21990aa84c422a0f506c7893c01db4eb674739a1b7cdac6c33589a74d1467a33a99bccd066132d1624a6a52828d14209f44a824d92348f646d23311848b64561f20f7878c3b21ce8e1c6ce3651aa8d1866e32618b8c1c5ee2e61630b105682a514b0a144ec26612b091446822d113087c3541970c2058829e14d0a004ac23e11b088040c1dc0e206f035010e08103b81800be05c02d815c0ac04f02480fc050027012008c03e01e } : Fields).get c.val)
theorem record031_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 2) (record031.inverseMaps 2) record031_frame002_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (smallEmbedding record031) (record031.maps 2)
      (record031.inverseMaps 2) record031_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame002_links_0000 (interval_append _ 64 128 133 record031_frame002_links_0064 record031_frame002_links_0128))
theorem record031_frame002_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 2 :=
  of_group record031 2 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record031_frame002_indices record031_frame002_graph record031_frame002_links
def record031_frame003_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x3c675ce69c3384700df5bcb756d2d9db1b606b8d61a9b5169ad29a334263abed7baf35dcba563ac357eae95aab155aaa151a7e4f69e13a2704d895d2a25149a92522a4047a8e91b23245c834f71ea3ce78cf01c237c6ecdb9b43626b8d51a733a670cb19130e5f4b91712d6598ae15229651ca193e26c4d49792a2404588790b20e4087f0fa1ec3c46a0ce1902f85c0b716229c508a013a25c4688710c20c340630ba1482884e09a1242404507e0dc130250440840e81c } : Fields).get c.val)
theorem record031_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record031) (record031.maps 3) (record031.inverseMaps 3) record031_frame003_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (smallEmbedding record031) (record031.maps 3)
      (record031.inverseMaps 3) record031_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame003_links_0000 (interval_append _ 64 128 133 record031_frame003_links_0064 record031_frame003_links_0128))
theorem record031_frame003_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 3 :=
  of_group record031 3 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record031_frame003_indices record031_frame003_graph record031_frame003_links
def record031_frame004_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1069.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1069.count (({ width := 10, code := 0x3b0e6383db76bd9f64d835dd434ed2b47d0f40cef39cd732cbb2bc26eab9ae2b76d8ae6b5ac6aca9ea3a7e9aa56709b66a99a6297a4991a438fe3b8de328be2c8a224881ff785de76dd7751b66cdb06b1a9699a367d9c64590629855f1735a5685895d5514b515414f5384c12f4a52446d1243108410ff3ecf73ccee34cce320be2e0b72c4a7284a0274972348721883194601685013c4c12c47118430f43509825088210741c } : Fields).get c.val)
theorem record031_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame004_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record031) (record031.maps 4) (record031.inverseMaps 4) record031_frame004_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1069.localPairCheck (smallEmbedding record031) (record031.maps 4)
      (record031.inverseMaps 4) record031_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame004_links_0000 (interval_append _ 64 128 133 record031_frame004_links_0064 record031_frame004_links_0128))
theorem record031_frame004_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 4 :=
  of_group record031 4 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1069
    Papers.RationalityTen.SharedFrameCatalogue.group1069_facts record031_frame004_indices record031_frame004_graph record031_frame004_links
def record031_frame005_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xe906dbb4ad804bf65efaf2d76aba059d2cb562eb055792b79580ab45502a314eea624aca39d1ac8c3455a2610608214079fe4fce7db3e51ed4f4a6ce3611aacd2e6813361818bf25e32e896f8b5458c2c015b0ab054329710947663a21c78ddc6c82fc1768b6c58a2b31538a5850227111b08cc45822510f085c41820910107ec3e81ed0f407843b41d30e3070c3781b50d7069c34419b0ca063430c17f0bc05c427c138098849423c11c08a84242040ff07c83c81cc0df06e035810e08103b81800be05c02d815c0ac04f02480fc050027012008c03e01e } : Fields).get c.val)
theorem record031_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame005_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5) (record031.inverseMaps 5) record031_frame005_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record031) (record031.maps 5)
      (record031.inverseMaps 5) record031_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame005_links_0000 (interval_append _ 64 128 133 record031_frame005_links_0064 record031_frame005_links_0128))
theorem record031_frame005_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 5 :=
  of_group record031 5 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record031_frame005_indices record031_frame005_graph record031_frame005_links
def record031_frame006_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x74170d6ea68367e67767166c66763a63562c62361d6136035fc5f35ea5e35d756352a52251c51550e4d34ca4c44b84b04a94a049248843342e42742141c4173ea3e33da3d13ca3be3ae3a93a039739138730c2d92d22cc2c52be28327927026225825124b23f23720b2081ff1f81f01e91da1d71ce1c71bf1b81b11ad1a91a519c19919218b18417e17917116815f15614e14513c11410f1090fc0f60f50ef0e20dc0db0d70d20c60c00be0b708708107706005f05c05b05705604f04903f02802702402301f01e } : Fields).get c.val)
theorem record031_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame006_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record031) (record031.maps 6) (record031.inverseMaps 6) record031_frame006_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record031) (record031.maps 6)
      (record031.inverseMaps 6) record031_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame006_links_0000 (interval_append _ 64 128 133 record031_frame006_links_0064 record031_frame006_links_0128))
theorem record031_frame006_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 6 :=
  of_group record031 6 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record031_frame006_indices record031_frame006_graph record031_frame006_links
def record031_frame007_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1099.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1099.count (({ width := 11, code := 0x6d2d61a4f1e638c638a30fe18be57baf35ddba9736e1dc0b756d2d7daaa5d3e2774e59b133e4b48b9051d2354628b71522840c811001fbbee7cef09df3b775ce95cf394722e2dc2b806f6bfd63abc566a954da634b294121a3a4668b112a213f67e8f99ee3d2790ec9d739e720e11ba3686b4d319e31e634c297e2f05c0b51632b8550a61482885008c91421c4107f8fd1ea3a06f8dd1ac338608b816c2c04187d0e81782e85a0b21542a04d08e0f81402704808c0f81e } : Fields).get c.val)
theorem record031_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame007_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record031) (record031.maps 7) (record031.inverseMaps 7) record031_frame007_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1099.localPairCheck (smallEmbedding record031) (record031.maps 7)
      (record031.inverseMaps 7) record031_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame007_links_0000 (interval_append _ 64 128 133 record031_frame007_links_0064 record031_frame007_links_0128))
theorem record031_frame007_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 7 :=
  of_group record031 7 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1099
    Papers.RationalityTen.SharedFrameCatalogue.group1099_facts record031_frame007_indices record031_frame007_graph record031_frame007_links
def record031_frame008_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1068.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1068.count (({ width := 9, code := 0x12892c8a35198c45e2d158843e1d0d8642e130883c1a0b047f3e1eef679bc9d8eb7539dcce572385c0d86bb59aad469b399acc65b2992c76331588c3612f16cb55a2c560aa54aa14aa451a893e9e4c25d2a9348235108742a0d007d3d1e0ec74381bcda6b34194c4602f170b4582b1509c4b249188843208f8783b1c8dc6832188bc5a2c158a450261288c44211007c3a1c0d0642e16 } : Fields).get c.val)
theorem record031_frame008_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame008_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame008_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame008_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record031) (record031.maps 8) (record031.inverseMaps 8) record031_frame008_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame008_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1068.localPairCheck (smallEmbedding record031) (record031.maps 8)
      (record031.inverseMaps 8) record031_frame008_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame008_links_0000 (interval_append _ 64 128 133 record031_frame008_links_0064 record031_frame008_links_0128))
theorem record031_frame008_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 8 :=
  of_group record031 8 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1068
    Papers.RationalityTen.SharedFrameCatalogue.group1068_facts record031_frame008_indices record031_frame008_graph record031_frame008_links
def record031_frame009_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0661.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0661.count (({ width := 12, code := 0xad4a95a519d29cb9c49ba9ae9a297e97796d96195694b93c93592c9209139068507f77e27d17bd7a675073d7297116fe6ef6dd6c66b366866365d65664b63d61861360a5ff5f35e55d75d25c95bf5b15a05044bd4ae4a048e47e4364274174023f33e83da3c53b637637336635934c34132a32631930c2fc2ed2df2d32c72b529f29c28c27c26e2612512412312202112021f31e218817816a14e13e13b12f1151041020f60eb0d40c80c50b708307d07505e05d05a05905505404f04903f02802702402301f01e } : Fields).get c.val)
theorem record031_frame009_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame009_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 9) (record031.inverseMaps 9) record031_frame009_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame009_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 9) (record031.inverseMaps 9) record031_frame009_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame009_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 9) (record031.inverseMaps 9) record031_frame009_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame009_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0661.localPairCheck (smallEmbedding record031) (record031.maps 9)
      (record031.inverseMaps 9) record031_frame009_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame009_links_0000 (interval_append _ 64 128 133 record031_frame009_links_0064 record031_frame009_links_0128))
theorem record031_frame009_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 9 :=
  of_group record031 9 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0661
    Papers.RationalityTen.SharedFrameCatalogue.group0661_facts record031_frame009_indices record031_frame009_graph record031_frame009_links
def record031_frame010_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0x67ecb191b0ce15c23826ffdf7bc5786ee5d5b9b702db5b4b636b6d4da5a89446834fb9d937652c9d92720238c6a8cd1822cc288490820e413818fc1f7beb7ccf79ea3c878cf0de03bc76ed659532062ec297face58aaf9572a353aa694aa904d89a52f25348e8f51722c4468790aa0d4027d8f79e63ac754e79c637e6d4d49a232e638c097d2f25c89b12923c4187b0f51da3786a0d219230c590a814c2743a86f0d01582a8520a2134260470860ec1402704808c0f81e } : Fields).get c.val)
theorem record031_frame010_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame010_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record031) (record031.maps 10) (record031.inverseMaps 10) record031_frame010_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame010_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record031) (record031.maps 10) (record031.inverseMaps 10) record031_frame010_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame010_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record031) (record031.maps 10) (record031.inverseMaps 10) record031_frame010_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame010_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record031) (record031.maps 10)
      (record031.inverseMaps 10) record031_frame010_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame010_links_0000 (interval_append _ 64 128 133 record031_frame010_links_0064 record031_frame010_links_0128))
theorem record031_frame010_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 10 :=
  of_group record031 10 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record031_frame010_indices record031_frame010_graph record031_frame010_links
def record031_frame011_indices (c : Fin record031.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0618.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0618.count (({ width := 9, code := 0x1379b4d66531984be5d2d95caa532893c9a492391486411f8bc4a231087c360f0682c1205007fbf9f8f479bc9e2f077ba9d2e873b99cae270b81bede6eb55a0cf6733598c662b1186c2602fd7cbd5c2dd68b1572ad50a7522853c9b4ca5d2a9247a39168842a09007e3e1e4ee75399c0d26732180bc5d2d158a853289389448239147a3c1d0d86a34198c4602d160a442200f878381b } : Fields).get c.val)
theorem record031_frame011_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.graphBitCheck record031.data.requiredEdges q = true := by decide +kernel
theorem record031_frame011_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record031) (record031.maps 11) (record031.inverseMaps 11) record031_frame011_indices (Fin.ofNat record031.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record031_frame011_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record031) (record031.maps 11) (record031.inverseMaps 11) record031_frame011_indices (Fin.ofNat record031.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record031_frame011_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record031) (record031.maps 11) (record031.inverseMaps 11) record031_frame011_indices (Fin.ofNat record031.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record031_frame011_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0618.localPairCheck (smallEmbedding record031) (record031.maps 11)
      (record031.inverseMaps 11) record031_frame011_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record031_frame011_links_0000 (interval_append _ 64 128 133 record031_frame011_links_0064 record031_frame011_links_0128))
theorem record031_frame011_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) : Supported record031 11 :=
  of_group record031 11 (smallEmbedding record031) (small_cells_exact record031 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0618
    Papers.RationalityTen.SharedFrameCatalogue.group0618_facts record031_frame011_indices record031_frame011_graph record031_frame011_links
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSmall.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (Fin.cases (record031_frame001_supported hcells) (Fin.cases (record031_frame002_supported hcells) (Fin.cases (record031_frame003_supported hcells) (Fin.cases (record031_frame004_supported hcells) (Fin.cases (record031_frame005_supported hcells) (Fin.cases (record031_frame006_supported hcells) (Fin.cases (record031_frame007_supported hcells) (Fin.cases (record031_frame008_supported hcells) (Fin.cases (record031_frame009_supported hcells) (Fin.cases (record031_frame010_supported hcells) (Fin.cases (record031_frame011_supported hcells) (fun j => Fin.elim0 j)))))))))))))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x34a1a36d0d67fb351970ca565030e97e0bc05d52b815a4ab95532a8951aa76530a7493649954c726192bc93b49721c905e81a3f51f50df86e53659ad0d4069633c9980be65d42de96ccb4658a2b715949a64a824d117089a3fa1fa0f947b03c91df8ea073c38e1bf0db86c630417a0b4c5702a214c09ec4d225712508c84401fc0f0070c3721af0c886042e21670a684f825c0f2072836c19408703881bc0dc061030017c09203501980c804a024011806c01800a0048014008003 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
def record032_frame002_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x6b66b16ac6a769a69569068b67366065464d6005f85ea5dc5d65ce5c35b156155554653d53752c51e5124bc4a84a149348d42d4274194063f83f23e63d438a38036f36335534c33c3312e12d02c92b62b228828427926d26025424824223522a2202161da1d51c41b119f19b18d18117817416415b14a13e12c1211171070fd0f10ee0e10d40cb0b20ab0a609f07d06e06c06b05f05e05d04703403203102502402301b00c00a009005004003 } : Fields).get c.val)
theorem record032_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record032) (record032.maps 2) (record032.inverseMaps 2) record032_frame002_indices (Fin.ofNat record032.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record032_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (smallEmbedding record032) (record032.maps 2)
      (record032.inverseMaps 2) record032_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record032_frame002_links_0000 record032_frame002_links_0064)
theorem record032_frame002_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 2 :=
  of_group record032 2 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record032_frame002_indices record032_frame002_graph record032_frame002_links
def record032_frame003_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x78077a77376a75574c7457417116ee6db6d463b63262061060c5ff5ec5da58a57a56c56355e54953952f4d64b64ae49a48e3f33e63d33c13af3a639438434032b31b3113002f02e22d928626a25e23d23520c2071fe1f71ef1e81db1d61cd1c61be1b719d19818a17d17216e16115814f14b13e13512d12311911310d1040fd0f70f30ea0e30dd0c70c10bd0b608707106f06e06106005f04903503303202502402301b00c00a009005004003 } : Fields).get c.val)
theorem record032_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 3) (record032.inverseMaps 3) record032_frame003_indices (Fin.ofNat record032.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record032_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (smallEmbedding record032) (record032.maps 3)
      (record032.inverseMaps 3) record032_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record032_frame003_links_0000 record032_frame003_links_0064)
theorem record032_frame003_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 3 :=
  of_group record032 3 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record032_frame003_indices record032_frame003_graph record032_frame003_links
def record032_frame004_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0982.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0982.count (({ width := 11, code := 0x12ca584ad95527a4c49592922a414768e309610c1481d032033fd7e0f09dcbb075ceb1d0b96720d89a7b4a67ace175ae45aeb3d62ac0570ab9442794de9b13125b4a493911a134187dcf99d239c714de9b83646a4d29a0332640c496d2ce55ca49402764b89311e232434828fc1e43a0720e01ae344660c817e2e85a0a0132254480750d0198328580ae158220350660c81282404606c0600a01201402003 } : Fields).get c.val)
theorem record032_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record032) (record032.maps 4) (record032.inverseMaps 4) record032_frame004_indices (Fin.ofNat record032.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record032_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0982.localPairCheck (smallEmbedding record032) (record032.maps 4)
      (record032.inverseMaps 4) record032_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record032_frame004_links_0000 record032_frame004_links_0064)
theorem record032_frame004_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 4 :=
  of_group record032 4 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0982
    Papers.RationalityTen.SharedFrameCatalogue.group0982_facts record032_frame004_indices record032_frame004_graph record032_frame004_links
def record032_frame005_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x15169ed39a654928dd15a233c66cccb98f2224247d8ed1d2384668b90c212c1c82b04e023f77deeb5cdb94704de995b21624c1d7eaf85deb895cab054ca854d29451ea212a2404708890d9fe3f47c0f49e33bc754e81ca3826f0da998324610ba96f2d257cac14e2944f49a927236434820ff1e43a0700db1a832c620ac15028c4d8780ce198328580ae1582183105e0b81202304406c0600a01201402003 } : Fields).get c.val)
theorem record032_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record032) (record032.maps 5) (record032.inverseMaps 5) record032_frame005_indices (Fin.ofNat record032.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record032_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record032) (record032.maps 5)
      (record032.inverseMaps 5) record032_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record032_frame005_links_0000 record032_frame005_links_0064)
theorem record032_frame005_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) : Supported record032 5 :=
  of_group record032 5 (smallEmbedding record032) (small_cells_exact record032 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record032_frame005_indices record032_frame005_graph record032_frame005_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSmall.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (Fin.cases (record032_frame002_supported hcells) (Fin.cases (record032_frame003_supported hcells) (Fin.cases (record032_frame004_supported hcells) (Fin.cases (record032_frame005_supported hcells) (fun j => Fin.elim0 j)))))))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x1872bee5a62d0d66ab2a58e2c515c0ad255caa99516a7453026d533098f4bca56526c92c46221c509483040da02cfb87c63ab9d40e8a73a3979c98dda6e03631ac8d3267c3309748b765b22d19628adc56528d934896449e24812188be4501fc8fd47ce3d91e58f0074c3a11c88e046e23651af0d206663211878be85b22bb1500a784f226713308fc45a2050f287203761a20c785fc2da14b09d84ac23010607703841bc0cd04382040e206f03701740b805b02b815809e04901c80dc06c025012008c03e01e } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
def record033_frame002_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0628.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0628.count (({ width := 11, code := 0x25649b8df1b2344638bf1722744887d0ca15c1f826f95ed3d379af19de3b1732e15bdb756dcda9afb58646c858eb19628c3d7eaf95e4b956ead2586a4d43a7e4ea9bd3325d48c8c91522343a865072083d47a0ef1d73a071cdd1b83626a0cf99731a61cc097b2ec5c8b215429051c9f13826e4b0911142163f4790e41bc350650c417a2dc590ae14a27c4e8980e61bc320630c41542a05309e138238410680cc1902504808c0f81e } : Fields).get c.val)
theorem record033_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record033) (record033.maps 2) (record033.inverseMaps 2) record033_frame002_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0628.localPairCheck (smallEmbedding record033) (record033.maps 2)
      (record033.inverseMaps 2) record033_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame002_links_0000 record033_frame002_links_0064)
theorem record033_frame002_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 2 :=
  of_group record033 2 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0628
    Papers.RationalityTen.SharedFrameCatalogue.group0628_facts record033_frame002_indices record033_frame002_graph record033_frame002_links
def record033_frame003_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x298d1b9d739e724df9b135a61cbc95d2964dc8d90113a1fc3a8690a60ec167fef81ea3cc788f01d8baa6e6dc1b53656bed699fb3b65ac958cb0b5feb155c2b2550a7d4aa8e4ea9712a24c48c90d1b230412818fd9f43d6788ec9d639a714de9b235c690cd19331861cbc1682ba570a894a2924e09812222c4207f0f41d23806c0cb1882f85c0b214c27c4e8981021f03706d0d81742e05b0ae158278490720dc1b02504808c0f81e } : Fields).get c.val)
theorem record033_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3) (record033.inverseMaps 3) record033_frame003_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (smallEmbedding record033) (record033.maps 3)
      (record033.inverseMaps 3) record033_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame003_links_0000 record033_frame003_links_0064)
theorem record033_frame003_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 3 :=
  of_group record033 3 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record033_frame003_indices record033_frame003_graph record033_frame003_links
def record033_frame004_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1b74d2b6012fd97bebcb5daae81676b2a5812b6d568a8c53126512dc95c4a1a4791f48e744520c101c7f73f29f6cf6a7a53671b08d5669734099b0c0e5f62e7169cb0055829711808744282078fa878c3b31ab0bf05b42c31588a9c50227111b08cc45822510f085c41820910107ec3e81ed0f407843b41d30e6070c36a1a70ce066831c1870c305e02e21620a9851427c132095849023811008484081f20f1073037c1ba0d604382040e206f03701740b805b02b815809e04901c80dc06c025012008c03e01e } : Fields).get c.val)
theorem record033_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4) (record033.inverseMaps 4) record033_frame004_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record033) (record033.maps 4)
      (record033.inverseMaps 4) record033_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame004_links_0000 record033_frame004_links_0064)
theorem record033_frame004_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 4 :=
  of_group record033 4 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record033_frame004_indices record033_frame004_graph record033_frame004_links
def record033_frame005_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1006.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1006.count (({ width := 12, code := 0x6f46cf66766365a65064764162261c6085f95eb5db5ce56c55a55554a53d52a5254f04c94b34a449749147946d42d42841f4194104073e83e13d03bf3b03a239433132231b3103012f22eb2b628f27926725c25723c2322062031fc1f41ed1e71de1db1d21ca1c11bb1b81b21ab1a319b19218117216916815b15315214613d12e12411811210a1040fc0f40eb0e40dd0d60d10c50bd0bb0b508307f06f06d06c05b05a05905505404d04903903703602502402301f01e } : Fields).get c.val)
theorem record033_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record033) (record033.maps 5) (record033.inverseMaps 5) record033_frame005_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1006.localPairCheck (smallEmbedding record033) (record033.maps 5)
      (record033.inverseMaps 5) record033_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame005_links_0000 record033_frame005_links_0064)
theorem record033_frame005_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 5 :=
  of_group record033 5 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1006
    Papers.RationalityTen.SharedFrameCatalogue.group1006_facts record033_frame005_indices record033_frame005_graph record033_frame005_links
def record033_frame006_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0627.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0627.count (({ width := 11, code := 0x2784d895729a4f49b92f252444848fb1da374658b509e0f418821005fa3eb792eb1d0b9c72ae41bf3766a4d2da3b42680ced9431e61ec0d7d2f15caab952a9f534a5147a884e094d22a3c4688b111a1c3fa7ecf89ea3c877cea1d2396708de9b63626a8d199f338654c39772da5b0ae9562aa5149d92b23c440830fa1e239c6f0d21923085c8b315629c5209c0f01d0338660ca1502985209e1382404306a0cc190240460880f81e } : Fields).get c.val)
theorem record033_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record033) (record033.maps 6) (record033.inverseMaps 6) record033_frame006_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0627.localPairCheck (smallEmbedding record033) (record033.maps 6)
      (record033.inverseMaps 6) record033_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame006_links_0000 record033_frame006_links_0064)
theorem record033_frame006_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 6 :=
  of_group record033 6 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0627
    Papers.RationalityTen.SharedFrameCatalogue.group0627_facts record033_frame006_indices record033_frame006_graph record033_frame006_links
def record033_frame007_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0x7c37957357317297237197166f66f36e96dd6d16c06a865063f63562b6196025f35bc58557556b56055953f5314eb4e14dd4d84d44cc4a549848246d45e44f43a3d83c93bd3b63ac3a539d37233b3263163093022ef2e52ad2ab29e29528827e26e26a26025424b23f23722e22521c21320b1f61e01cf1ce1bf1b51b419d19117d16915614a13812b11f1131020f80f00e60de0cf0c60c30bb08207d06e06c06b05a05905805405304d04703803603502502402301f01e } : Fields).get c.val)
theorem record033_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 7) (record033.inverseMaps 7) record033_frame007_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 7) (record033.inverseMaps 7) record033_frame007_indices (Fin.ofNat record033.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record033_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (smallEmbedding record033) (record033.maps 7)
      (record033.inverseMaps 7) record033_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record033_frame007_links_0000 record033_frame007_links_0064)
theorem record033_frame007_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) : Supported record033 7 :=
  of_group record033 7 (smallEmbedding record033) (small_cells_exact record033 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record033_frame007_indices record033_frame007_graph record033_frame007_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSmall.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (Fin.cases (record033_frame002_supported hcells) (Fin.cases (record033_frame003_supported hcells) (Fin.cases (record033_frame004_supported hcells) (Fin.cases (record033_frame005_supported hcells) (Fin.cases (record033_frame006_supported hcells) (Fin.cases (record033_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSmall.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record034_frames_supported
theorem record035_frame000_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    Supported record035 0 :=
  of_identity record035 0 (by decide +kernel)
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSmall.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0x7fc7f07ea7d67ca7c477376a75c74f7246e26ae6386305ee5ad5a159759058557b57450f50a5034fd4f64ef4b94a548e4824674534463e43d03c33b139d38637a34833d33732832131b30d3063002c82bb29e28227026324622a22221c21520e2051c61bb1b119118517c16f13011e1121091020f80d50c60c206f06e05c05b05705604f04903803703602502402302001f01e01501301201100f00e00a009008004003001000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (smallEmbedding record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
def record036_frame002_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3171884c39607afd57dcb5c5a1aca9628aea553298131e98349621c50a083040d9fe0fb87c63ab9d40e8a73a3979c98ddc6d535d9ac8d1066b3309748b765b22d19628adc56527c936c9a44ad24f12408de45f2280ff47e03d41de8ea473637b1b10d4067e32718a8c1c5702a7148892c4682220ff06e43341840ba059429c0fe06b83240de06e02e016c0ae056027812407003701b0094048023010007c03c015009804802200f0070028012008002000c002000 } : Fields).get c.val)
theorem record036_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record036) (record036.maps 2) (record036.inverseMaps 2) record036_frame002_indices (Fin.ofNat record036.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record036_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record036) (record036.maps 2)
      (record036.inverseMaps 2) record036_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record036_frame002_links_0000 record036_frame002_links_0064)
theorem record036_frame002_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) : Supported record036 2 :=
  of_group record036 2 (smallEmbedding record036) (small_cells_exact record036 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record036_frame002_indices record036_frame002_graph record036_frame002_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSmall.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (Fin.cases (record036_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSmall.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x693b471a1cd00669327d7e0b475972c595bead5563aaf155caa7546a9d94c2a5a515a8613a49b24caa63925c923472233914287e4391fa8fa87653a91cf0e4e6a234b19e4cc05f32ea16f4b665a82b2957ca9253029113f09bc4d323a117089a3fa1fa0f947b03c91df8e786fc3631ae8cc86402f41718b4c5842b812b88c84401fc0f0070c3721af0c886042e216709f04b824c0ff079039419409c04d821c0ee061030017c07e03501980c804802300d803001600a0048014008003 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (smallEmbedding record038) (small_cells_exact record038 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSmall.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (Fin.cases (record038_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record038_frames_supported
theorem record039_frame000_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    Supported record039 0 :=
  of_identity record039 0 (by decide +kernel)
theorem record039_frames_supported (hcells : ∀ c, record039.data.cells c = FacetUniverses.FullSmall.cells (embedding record039 c)) :
    ∀ f : Fin record039.g, Supported record039 f :=
  (Fin.cases (record039_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record039_frames_supported
theorem record040_frame000_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    Supported record040 0 :=
  of_identity record040 0 (by decide +kernel)
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3405942c5c62130e57dcbbf5d4ad6d68ab2c58aabb1592ab05542981458a194bf24b113c87b4389f70f8c7583a69cdce4a6ee36a9aecd646613151864ba45bb2d916a0aca54629914909f24db26912b493c49022f91408883fc1f90f8c7ac3c71df0eac73637b1b10d3867c3251898c145c62c215c0aa452027d13588d04442120fe07803861b90b2854419205c02d81600ae056027810c08204001c00dc06c024011808003e01e00d804401e00e0058028012005002000c002000 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (smallEmbedding record040) (small_cells_exact record040 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSmall.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSmall.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xdf86eb36c1a7cd1668133b991ab935b8ad2d5b2ab154eaa254509ab4d426853349934c6261d2fc9704b1257529e9484a024c524691c48824252048fa479239d1c07d23a89c94e206962ef1700b325862bc9460a144df26792688ee46722090c08424021b78d446543171850aa453627013008ac4101f80e907043641930ac0524276134097049023a116089042c2060fc07b83a01c40dc06c034015408e046821c0d606a01980c8052028013809004602000f8078038014009804801e00e0058028012007 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (smallEmbedding record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (smallEmbedding record045) (small_cells_exact record045 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSmall.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
def record046_frame001_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0xcc4658b281870bed58a2b1d55caa752fa77131c92c48f23a11a4871425a0c903a75039d1c98db06be3599a98cc05e62ed9710b625972bd9594aac53429314689a44b325012489063fe1f08f1477a3af1b10d5064e3151718b0857029213f89b44921ff0dc86a032e16309084001b008e04681ac0d406002f81700b605702b015009e03301900a8050027013009004601f00f0070028013009003c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record046_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 1) (record046.inverseMaps 1) record046_frame001_indices (Fin.ofNat record046.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record046_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record046) (record046.maps 1)
      (record046.inverseMaps 1) record046_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record046_frame001_links_0000 record046_frame001_links_0064)
theorem record046_frame001_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 1 :=
  of_group record046 1 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record046_frame001_indices record046_frame001_graph record046_frame001_links
def record046_frame002_indices (c : Fin record046.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0x4e29b5342584978b913a2343d846ff5f03be770e99ceb7a6dcd89acb2763ac357d2ed5c6b7d652a253aa353ea764d89852e24c4848f50e21140a7e4fa1c937e6b0d21a13005ecb495d2a05189f13225247c8a8ff1c83746b0c81642a84c0770ec188308570ac14c2904e09a12c240310600a41382604a08c1101e03a06c0a01302403c0700b0140240380400600800800 } : Fields).get c.val)
theorem record046_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record046.data.requiredEdges q = true := by decide +kernel
theorem record046_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record046_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record046) (record046.maps 2) (record046.inverseMaps 2) record046_frame002_indices (Fin.ofNat record046.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record046_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (smallEmbedding record046) (record046.maps 2)
      (record046.inverseMaps 2) record046_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record046_frame002_links_0000 record046_frame002_links_0064)
theorem record046_frame002_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) : Supported record046 2 :=
  of_group record046 2 (smallEmbedding record046) (small_cells_exact record046 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record046_frame002_indices record046_frame002_graph record046_frame002_links
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSmall.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (Fin.cases (record046_frame001_supported hcells) (Fin.cases (record046_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x74836dda50bf65e5ae8162eaf256f2b1d4be959473a359156898418203cff27e73611a5ccd85e32df16a8b2652b2128ecc7443771b20bf05b62c515988c845622410e885841a2080fd07b03c61d50e707203761ad0d3065831e1880c105f027a13509704641fc0ef06d823811a08703581a80c005f02e016c0ae05602a013c066032014009c04802300f807803801b00a8050026012008803c01c00b005002400e0040018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (smallEmbedding record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0646.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0646.count (({ width := 11, code := 0xcfd96322e15c137deee5cdb816ded2544a2341a764dd94b24e40471849072063eb7bcf51e4bb66b2ca99030a5feb395f2ae5469912ca4f4868e117a2843681cfd9ea3ba75ce59bc35e670c91852fe5ec989242323cc680c11481e83c8750c21802b0550a41442684c09411c1983205009c1202303e0780e01b02a0500981202203c0700b0140240380400600800800 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0646.localPairCheck (smallEmbedding record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0646
    Papers.RationalityTen.SharedFrameCatalogue.group0646_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
def record047_frame003_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x7d2f5de4ba0728e3dbf3756dcda9ad328630c4d812f95d2b7968acc51ea093f2684be96529a414167ecfb9e73be73ce29b93685e4b896b2ca57cac9562985149f93125849c8f9182264187f8fa1ee3c8670c91842c0500961141c83886d0ba1702a0530a013c2584a09010c1883005009c1202303e0780e01b02a0500981202203c0700b0140240380400600800800 } : Fields).get c.val)
theorem record047_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record047) (record047.maps 3) (record047.inverseMaps 3) record047_frame003_indices (Fin.ofNat record047.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record047_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (smallEmbedding record047) (record047.maps 3)
      (record047.inverseMaps 3) record047_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record047_frame003_links_0000 record047_frame003_links_0064)
theorem record047_frame003_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) : Supported record047 3 :=
  of_group record047 3 (smallEmbedding record047) (small_cells_exact record047 hcells) Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record047_frame003_indices record047_frame003_graph record047_frame003_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSmall.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (Fin.cases (record047_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSmall.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSmall.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
def record050_frame001_indices (c : Fin record050.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1007.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1007.count (({ width := 13, code := 0x3451a0cd0065f32ad944c5961fb0e1824bf85f7af5177cba85ac2ce163eb1553e29954be9cd4e3a6e135499b4c8257127292d48723dd1c28c144f21ed0e27f03ed1f10ec27253599980c8e62b30d178cbb65c42d89598a9c53129194749a44b625012488f245d227110c8183f21eb0ef87623621a98d0864a3131848ae04861f60f707443721a70ce860c2e61560a004c024611107e032014c06c03581a80d005802b815808204001980c8054028013807c03c00f00700280120070030010006000 } : Fields).get c.val)
theorem record050_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.graphBitCheck record050.data.requiredEdges q = true := by decide +kernel
theorem record050_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record050_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record050) (record050.maps 1) (record050.inverseMaps 1) record050_frame001_indices (Fin.ofNat record050.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record050_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1007.localPairCheck (smallEmbedding record050) (record050.maps 1)
      (record050.inverseMaps 1) record050_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record050_frame001_links_0000 record050_frame001_links_0064)
theorem record050_frame001_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) : Supported record050 1 :=
  of_group record050 1 (smallEmbedding record050) (small_cells_exact record050 hcells) Papers.RationalityTen.SharedFrameCatalogue.group1007
    Papers.RationalityTen.SharedFrameCatalogue.group1007_facts record050_frame001_indices record050_frame001_graph record050_frame001_links
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSmall.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (Fin.cases (record050_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record050_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00030

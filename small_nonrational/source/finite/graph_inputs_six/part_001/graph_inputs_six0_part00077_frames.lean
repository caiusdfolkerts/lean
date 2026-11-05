module
prelude
public import GraphInputsSix0Part00077Data
public import RawFrameSupport
public import SharedFrameGroups043Checked
public import SharedFrameGroups051Checked
public import SharedFrameGroups053Checked
public import SharedFrameGroups058Checked
public import SharedFrameGroups059Checked
public import SharedFrameGroups060Checked
public import SharedFrameGroups066Checked
public import SharedFrameGroups067Checked
public import SharedFrameGroups069Checked
public import SharedFrameGroups070Checked
public import SharedFrameGroups073Checked
public import SharedFrameGroups074Checked
public import SharedFrameGroups075Checked
public import SharedFrameGroups078Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups097Checked
public import SharedFrameGroups098Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups104Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077
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
def record002_frame001_indices (c : Fin record002.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x509a8252f196d4b3649123290c47a63af1c98bac57a03d00c7d23cbde50f1f6a0b40194ab4c595aac93c09bf4a323651828ac449a0ccf566d433a1990c9c63b2bf947ca1e4f92731270900470235106479c3ab1c70c5c4d426112688f445221810687fc3e41870bf05a82b414609a84a823810f07a836812809104801fc0da05e02c81580a804d025011c06c02700f007403801900b004001e009003800c002000 } : Fields).get c.val)
theorem record002_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record002.data.requiredEdges q = true := by decide +kernel
theorem record002_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record002_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1) (record002.inverseMaps 1) record002_frame001_indices (Fin.ofNat record002.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record002_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record002) (record002.maps 1)
      (record002.inverseMaps 1) record002_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record002_frame001_links_0000 record002_frame001_links_0064)
theorem record002_frame001_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) : Supported record002 1 :=
  of_group record002 1 (embedding record002) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record002_frame001_indices record002_frame001_graph record002_frame001_links
theorem record002_frames_supported (hcells : ∀ c, record002.data.cells c = FacetUniverses.FullSix0.cells (embedding record002 c)) :
    ∀ f : Fin record002.g, Supported record002 f :=
  (Fin.cases (record002_frame000_supported hcells) (Fin.cases (record002_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa1850667ff3f8957ca6e4ff26691f48963d91da8e6c6fe246fd27e0bc61dbaed674ab969c7ee2f71436c1b36d1768132e1922c8a6182fc5796ba25c8ad3d652b00577ab0155aa9f4c225511a28a1426a11106e7723ac1cb8d906ae34219a0ca264d31e9754b9256429b1488a3e50b26b92a492a49223f11948c44572290f206f235318f0c105de2d915909f44c624e11c08c845821c10b076834014509b84c424810807d03d01ce0d203301740b004a0218100072036013008402c00e0048010002000 } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 120 :=
  interval_of_check _ 64 56 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 120 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
theorem record004_frames_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    ∀ f : Fin record004.g, Supported record004 f :=
  (Fin.cases (record004_frame000_supported hcells) (Fin.cases (record004_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record006_frames_supported (hcells : ∀ c, record006.data.cells c = FacetUniverses.FullSix0.cells (embedding record006 c)) :
    ∀ f : Fin record006.g, Supported record006 f :=
  (Fin.cases (record006_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record008_frames_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) :
    ∀ f : Fin record008.g, Supported record008 f :=
  (Fin.cases (record008_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa2c511284d412993cc465872a2931c9423b51cc893c1de09b0367e83ecde78f336a834d9a30d0b682b0f56bab2756c2a6d5169f14dda5b125e91f46d23351868b8458229d12488d3f69c10daa6a53389990c9c5af2c01540a3850f27c929094048f24512108ee46f235906c79e3951960c205dc29a1340958496239116886041a1e40db86142e61680ab052826a12a08083e41d40e206d83500e206d03501880bc05b02680e806e03201580a00460140080038012008003800c004001 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (Fin.cases (record011_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record014_frame001_indices (c : Fin record014.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa48519284140995b4a8a4eb2348f7477224d0a5827c051f9cfbd7bebcf5dd6ee3717b88d91ac7b5da2c495aaac755baad153ea374c3a4e926290f46a221d0fc85c425a0f906e8313ee1db0e606c23431960ca864531e9580a4251727c934c92848a236119c8b8457228900873034e18a0bfc5b22ad1398978470233111887042c1de0ca05e02b014309e04c024811508303fc1e60e706c034813c09403e01c80bc0590220100074036014808803a01900b003c01c00a0048014002000 } : Fields).get c.val)
theorem record014_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record014.data.requiredEdges q = true := by decide +kernel
theorem record014_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record014_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record014) (record014.maps 1) (record014.inverseMaps 1) record014_frame001_indices (Fin.ofNat record014.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record014_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record014) (record014.maps 1)
      (record014.inverseMaps 1) record014_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record014_frame001_links_0000 record014_frame001_links_0064)
theorem record014_frame001_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) : Supported record014 1 :=
  of_group record014 1 (embedding record014) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record014_frame001_indices record014_frame001_graph record014_frame001_links
theorem record014_frames_supported (hcells : ∀ c, record014.data.cells c = FacetUniverses.FullSix0.cells (embedding record014 c)) :
    ∀ f : Fin record014.g, Supported record014 f :=
  (Fin.cases (record014_frame000_supported hcells) (Fin.cases (record014_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record014_frames_supported
theorem record015_frame000_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    Supported record015 0 :=
  of_identity record015 0 (by decide +kernel)
def record015_frame001_indices (c : Fin record015.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x14a3a3bd0828133de9ee4b065792a8900c7e23dd1dc8bd453e2070ce81fc011f9cfbd7b5bcaddd0ee06583249762b0f5632ad946298a4ad24f92188d7453a22d0b283b41a9f70b8258a2af14c4a564fe268929093c47123191548083951a80c706242db15789ec4e223a11788883b81a40c4055828613c097049023010607f83c41ce0db059824011c06d03501880c205e02c815008803a01980c805c029012007c03801400900380120070028008002000 } : Fields).get c.val)
theorem record015_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record015.data.requiredEdges q = true := by decide +kernel
theorem record015_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record015_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record015) (record015.maps 1) (record015.inverseMaps 1) record015_frame001_indices (Fin.ofNat record015.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record015_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record015) (record015.maps 1)
      (record015.inverseMaps 1) record015_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record015_frame001_links_0000 record015_frame001_links_0064)
theorem record015_frame001_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) : Supported record015 1 :=
  of_group record015 1 (embedding record015) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record015_frame001_indices record015_frame001_graph record015_frame001_links
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
def record017_frame001_indices (c : Fin record017.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x284b40e99bcbee56329d93ac8d23dd1dc8cac2920850077d9be9dc5ed6366532358f6bf15da2e4569eb12577ab6d58eac055a2a7d4429ca4c4255127491f487a355142887436217109684541ba0c4f3c76b3971bd0d826843309950c9863d2c29584a6c52128493e49a84a924a11f08d8467230915c8a24021bc8d3466031e18a0bbc5b22ac14789f44e624e11c08cc45421c10b077c3401940b3056028613b098849022a10607f03d01ce0d8069027812805e02c8128080036014008803a01900b004001c00b0048010002000 } : Fields).get c.val)
theorem record017_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record017.data.requiredEdges q = true := by decide +kernel
theorem record017_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record017_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record017) (record017.maps 1) (record017.inverseMaps 1) record017_frame001_indices (Fin.ofNat record017.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record017_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record017) (record017.maps 1)
      (record017.inverseMaps 1) record017_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record017_frame001_links_0000 record017_frame001_links_0064)
theorem record017_frame001_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) : Supported record017 1 :=
  of_group record017 1 (embedding record017) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record017_frame001_indices record017_frame001_graph record017_frame001_links
theorem record017_frames_supported (hcells : ∀ c, record017.data.cells c = FacetUniverses.FullSix0.cells (embedding record017 c)) :
    ∀ f : Fin record017.g, Supported record017 f :=
  (Fin.cases (record017_frame000_supported hcells) (Fin.cases (record017_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record017_frames_supported
theorem record018_frame000_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    Supported record018 0 :=
  of_identity record018 0 (by decide +kernel)
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record021_frames_supported
theorem record022_frame000_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    Supported record022 0 :=
  of_identity record022 0 (by decide +kernel)
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record022_frames_supported
theorem record023_frame000_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    Supported record023 0 :=
  of_identity record023 0 (by decide +kernel)
theorem record023_frames_supported (hcells : ∀ c, record023.data.cells c = FacetUniverses.FullSix0.cells (embedding record023 c)) :
    ∀ f : Fin record023.g, Supported record023 f :=
  (Fin.cases (record023_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record025_frame001_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0812.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0812.count (({ width := 11, code := 0x1d9fb1738e5fc8b9071ae2fc2783ef5de3b3b626bcd6dacb5369cd2fa033ae6bcc38f71b62fc5587f0de0fc197d6f45dfbb560eb9d3fa232ae504988f5005f739571adc59b321616b81682c8582aa54f2945049992d25049c9292223b4628b5049fd3d078cec1b333e648c31722aa53ca013d26c4d49892923c470828ff1e63b4728d619a31c5e0b81502944c05d08e1101e83806a0d01982904e0981282302c0480600a01001801802 } : Fields).get c.val)
theorem record025_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record025) (record025.maps 1) (record025.inverseMaps 1) record025_frame001_indices (Fin.ofNat record025.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record025_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0812.localPairCheck (embedding (N := 44310) record025) (record025.maps 1)
      (record025.inverseMaps 1) record025_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record025_frame001_links_0000 record025_frame001_links_0064)
theorem record025_frame001_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 1 :=
  of_group record025 1 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group0812
    Papers.RationalityTen.SharedFrameCatalogue.group0812_facts record025_frame001_indices record025_frame001_graph record025_frame001_links
def record025_frame002_indices (c : Fin record025.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0704.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0704.count (({ width := 9, code := 0x405fafc7dbe9f2f87bbd9eaf479bc9e2ef75ba9d2e873b95c6e270b75b6d96bb51a4d067b2d92c561b0982be5d2d568b357aad50a350a793094492311489442190a83409f4f67a3c9e0ee763a1ccde6c349a0ca602e970b255291449e4e26930964a2411c8843209007e3d1d8e46e36190c460291087c3c1d0d86832170b0542813070301007030100602 } : Fields).get c.val)
theorem record025_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0704.graphBitCheck record025.data.requiredEdges q = true := by decide +kernel
theorem record025_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (embedding (N := 44310) record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record025_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (embedding (N := 44310) record025) (record025.maps 2) (record025.inverseMaps 2) record025_frame002_indices (Fin.ofNat record025.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record025_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0704.localPairCheck (embedding (N := 44310) record025) (record025.maps 2)
      (record025.inverseMaps 2) record025_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record025_frame002_links_0000 record025_frame002_links_0064)
theorem record025_frame002_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) : Supported record025 2 :=
  of_group record025 2 (embedding record025) hcells Papers.RationalityTen.SharedFrameCatalogue.group0704
    Papers.RationalityTen.SharedFrameCatalogue.group0704_facts record025_frame002_indices record025_frame002_graph record025_frame002_links
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (Fin.cases (record025_frame001_supported hcells) (Fin.cases (record025_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1059.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1059.count (({ width := 9, code := 0xb157eb356a7d3a994b9e4e6632b92c7e331386c1e00fd7abc9e2ec73395c4de6cb61aad165b298ec35f2f574b659ac15eaa52a611e8c45a08f076391b4d66932980b6512792c8c44210f872381a8d05a2812088401e0d8643015098481c0a048140200 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 88 :=
  interval_of_check _ 64 24 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1059.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 88 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1059
    Papers.RationalityTen.SharedFrameCatalogue.group1059_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
theorem record027_frames_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    ∀ f : Fin record027.g, Supported record027 f :=
  (Fin.cases (record027_frame000_supported hcells) (Fin.cases (record027_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record030_frames_supported
theorem record031_frame000_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    Supported record031 0 :=
  of_identity record031 0 (by decide +kernel)
theorem record031_frames_supported (hcells : ∀ c, record031.data.cells c = FacetUniverses.FullSix0.cells (embedding record031 c)) :
    ∀ f : Fin record031.g, Supported record031 f :=
  (Fin.cases (record031_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record031_frames_supported
theorem record032_frame000_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    Supported record032 0 :=
  of_identity record032 0 (by decide +kernel)
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x8df89888886185685581a80e7e97dc7b47a779c77c77276474b7466c36b96b068a67963f62460f5df5c758e57156454652b52551a4c74bd4b34b24ab4a44864774704634504314244174073f43c73be3b73a338d37836535e34633b31d3173043022fc2f123d2321e11d019318617314d1350ff0ea0df0cb0c60c10a908c08b07d05404502101e01901000f00e00b009004003000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 99 :=
  interval_of_check _ 64 35 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 99 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (Fin.cases (record032_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record033_frames_supported
theorem record034_frame000_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    Supported record034 0 :=
  of_identity record034 0 (by decide +kernel)
theorem record034_frames_supported (hcells : ∀ c, record034.data.cells c = FacetUniverses.FullSix0.cells (embedding record034 c)) :
    ∀ f : Fin record034.g, Supported record034 f :=
  (Fin.cases (record034_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x92f92d8f38ee8ac89f87887485f85e85c85a85685585084f8498418318208178127ff7ee7e57df7da7d77b17ab7a479b77977676f76374772a71d70a6866766576415db5c45ac59053251c50548647747046344d43842e4223c73be3b73a338a37f37536331830a2f72ec2da29227e27325023f2341e11d01c11af1ab19918417f17114d13512d1211121050f40e80dd0cd0bc0b80b108106e06c05e05d04503403303102602402301900b009004003 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record038_frame001_indices (c : Fin record038.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xab1a94a4fa24a1b9d59c39ba9ae9a998e98b98696c93792791591391090e8ea8e38e28df8037f77ea7dd7d17c477176575c75570d6f96c364d6196055bb5a559a59058957e5745014f64ef4a24824463c339a37a33733232131b3173063002a929025123822421b21620e1ec1b81b21a919a18817c1561271151090ff0f90f00da0cf0c60c207106e05e05b05905604d04703703602402301f01e01401201000e009008003001000 } : Fields).get c.val)
theorem record038_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record038.data.requiredEdges q = true := by decide +kernel
theorem record038_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record038_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record038) (record038.maps 1) (record038.inverseMaps 1) record038_frame001_indices (Fin.ofNat record038.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record038_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record038) (record038.maps 1)
      (record038.inverseMaps 1) record038_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record038_frame001_links_0000 record038_frame001_links_0064)
theorem record038_frame001_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) : Supported record038 1 :=
  of_group record038 1 (embedding record038) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record038_frame001_indices record038_frame001_graph record038_frame001_links
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
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa13504a5d72d48ea471a3111708acc4a5f9afb079fbcd9cbcd9e6a83509a68d18682b3c16deb5f5a62ca15daad8501a7cd3c09bc4c0a5b11d08da466231d1728b2453a26d12478f3821b5cd4a6643271898b5e5822a8143c9f24d1253128091e48824211dc8de46b1e70eac72c3551960a604d626112688e0452218106880036a1880bf05a82aa14609a84a823a0f907483881b80d403681a80bc05b02680dc06c032014009c04601900800380140090038010006001 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record041_frames_supported
theorem record042_frame000_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    Supported record042 0 :=
  of_identity record042 0 (by decide +kernel)
theorem record042_frames_supported (hcells : ∀ c, record042.data.cells c = FacetUniverses.FullSix0.cells (embedding record042 c)) :
    ∀ f : Fin record042.g, Supported record042 f :=
  (Fin.cases (record042_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record042_frames_supported
theorem record043_frame000_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    Supported record043 0 :=
  of_identity record043 0 (by decide +kernel)
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa3f514a83d407990cb9655f29b94c4a4a4fb25291e484605aff27f4bd69e34f15651b22d55ea9c4ff251d25c91c44a21ed0d2849417199cc7c5e92ea96f8aa252228c942c98849524611f88a030b17e8bb45ba26a12e09304782300db868832017a0b4051427813108b84201fe0f406d02c812008d04281a80d206602d81580a804d02180e406a03201880b804c023010807803801900a004c01c00d004802000e005002000c002000 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0871.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0871.count (({ width := 12, code := 0xe9ee8ee5ce52e08df8dc6dbcdbadb4da3d9ad90d84d0bceececc9bc7ec7cb12ae397c94e90886c84c8387b47977827536fb6085b958f58157651c4ed4e24d449046545a44b3ed3092f92e92d82722642542462311b51a819a1851761541451351141010f70ea0cc0a909008d08506a06906605b05605404d04303903503203102e02602302101e01c01901401300e00d009008007005004003001000 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0871.localPairCheck (embedding (N := 44310) record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group0871
    Papers.RationalityTen.SharedFrameCatalogue.group0871_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x8cf8c78b08ad88386d85584f84e84d84984083b8327df7d77d67a67977966d36c15f35e55ae5465315244d24be4b349847f3e03c33a339738b35133232e3232fc2dd2d82d02a920f2081fc1f41b41aa1a419918e14613a12f11d1110f90f40eb0d70cb0c50bf0a909508408107906406306005705205004904103903503203102e02602302101e01c01901401300e00d009008007005004003001000 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record045_frames_supported
theorem record046_frame000_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    Supported record046 0 :=
  of_identity record046 0 (by decide +kernel)
theorem record046_frames_supported (hcells : ∀ c, record046.data.cells c = FacetUniverses.FullSix0.cells (embedding record046 c)) :
    ∀ f : Fin record046.g, Supported record046 f :=
  (Fin.cases (record046_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record046_frames_supported
theorem record047_frame000_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    Supported record047 0 :=
  of_identity record047 0 (by decide +kernel)
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xac3abfab0a93a55a48a36a1d9b99a899799197996a95194f94c94a93792791090e9039018fb8f78f58f38e88e68808307f77d17bd7b17547086a868e6145ea5d05ad5a859058c5745705104fc4f54a749a45d4374223da39f39236e35934f34233732f31b3143002fc2ab2902532382211ea1c61ba1b21ac19917c1761541301261091010f90f30e00db0c60c207a07806e05b05705604304204003903602602302101f01e01901401201000e00d00a009008004003001000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0832.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0832.count (({ width := 9, code := 0x79bc9e2f0767afd5e9f3797cae4f1f8dc4e1f0b83bfdeef377b8dbedb6bb4d9ecb63add468f419dcde3b0776b7d7eb352a551e853f9d4de5b2892c662f0a823fdeaec75381b6d86a3419ac862b017ab3582a14aa04ba491e8d45a18fc7c3b9c8de673298cc25c2d154a643208fc74361a8bc5c2c150a444210f87438170a048200e0682812080200c0200 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group0832
    Papers.RationalityTen.SharedFrameCatalogue.group0832_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
def record048_frame003_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0828.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0828.count (({ width := 9, code := 0x41607017fbe1ecf4793b1d4e974399cae371385c0de6e36db4d76b355a8d369345a0cc6431586c1602e566b056aa14aa24fa7534994b2551c8c45a11067e3e1e8ec73391b0d46933998c6612f974b8592c154a851271309448239108441200f876391c0d86a33190bc5c24118843e1d0e0602e160a04c2210078381a0c058281208038180a04018080200 } : Fields).get c.val)
theorem record048_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0828.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record048_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record048) (record048.maps 3)
      (record048.inverseMaps 3) record048_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record048_frame003_links_0000 record048_frame003_links_0064)
theorem record048_frame003_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 3 :=
  of_group record048 3 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group0828
    Papers.RationalityTen.SharedFrameCatalogue.group0828_facts record048_frame003_indices record048_frame003_graph record048_frame003_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (Fin.cases (record048_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
def record049_frame001_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x4c866212d8963c77638d18e8bbc24e0d1040815b705a7ccb8627b075810b695722a11496a4351a26c929a90d482a3d90ee868421a0b50508033f69fa0e6e72438e9a84d1e640317180cbfe5f22c195c8a5c51d27c13d09d24ce25412148e045f226910486041e20d8e706fc33c18f0c145fa2f015c09e44ca25a12688ac4402130fd071c3241800bb05b029e14509d849823a0f707383701a406e035017c0b603901b00d406402a013809804601900a004802000e0050024010007002000c004001 } : Fields).get c.val)
theorem record049_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record049) (record049.maps 1) (record049.inverseMaps 1) record049_frame001_indices (Fin.ofNat record049.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record049_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record049) (record049.maps 1)
      (record049.inverseMaps 1) record049_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record049_frame001_links_0000 record049_frame001_links_0064)
theorem record049_frame001_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 1 :=
  of_group record049 1 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record049_frame001_indices record049_frame001_graph record049_frame001_links
def record049_frame002_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x515a885425a08cc666072e996946f23111708acb979b3cd4268c34159e0be65ac2bb5544a8b53227b130293648fa3e11988c645ba2b915489b4492234fb67a03c79c24dee6a53489974c9c6262da1688aa053c28413e49a24c1259929893a49124412048ee46f2358f447503551960c185dc2c514c09ac4b024b11e086841a2000f206d43101750b4056426e12a08e84041f00e9071036c1a806e035017c0b603901b00d406402a013809804601900a004802000e0050024010007002000c004001 } : Fields).get c.val)
theorem record049_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record049) (record049.maps 2) (record049.inverseMaps 2) record049_frame002_indices (Fin.ofNat record049.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record049_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record049) (record049.maps 2)
      (record049.inverseMaps 2) record049_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record049_frame002_links_0000 record049_frame002_links_0064)
theorem record049_frame002_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 2 :=
  of_group record049 2 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record049_frame002_indices record049_frame002_graph record049_frame002_links
def record049_frame003_indices (c : Fin record049.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xab0aa8a9da93a48a3ca29a1d9b99a899799187f82f7f87d27be7b27557086c86a769f6906526145e95e15d25ae5a959958f58d57d5735715114fd4f64a749a46645a4394334243e33d739f39237036a35b35034333832e32331a3133082ff2fd2ab29025323822321b20e1ea1c61ba1b21ac19618f18717715413012311c1141010f90f30e10dd0d00cb0c50c106e06a05f05b03903603503202a02702602301901401201000e00a009008007004003002001 } : Fields).get c.val)
theorem record049_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record049.data.requiredEdges q = true := by decide +kernel
theorem record049_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record049_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record049) (record049.maps 3) (record049.inverseMaps 3) record049_frame003_indices (Fin.ofNat record049.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record049_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record049) (record049.maps 3)
      (record049.inverseMaps 3) record049_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record049_frame003_links_0000 record049_frame003_links_0064)
theorem record049_frame003_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) : Supported record049 3 :=
  of_group record049 3 (embedding record049) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record049_frame003_indices record049_frame003_graph record049_frame003_links
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (Fin.cases (record049_frame001_supported hcells) (Fin.cases (record049_frame002_supported hcells) (Fin.cases (record049_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record049_frames_supported
theorem record050_frame000_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    Supported record050 0 :=
  of_identity record050 0 (by decide +kernel)
theorem record050_frames_supported (hcells : ∀ c, record050.data.cells c = FacetUniverses.FullSix0.cells (embedding record050 c)) :
    ∀ f : Fin record050.g, Supported record050 f :=
  (Fin.cases (record050_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record050_frames_supported
theorem record051_frame000_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    Supported record051 0 :=
  of_identity record051 0 (by decide +kernel)
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x56a2b2b4069f5caf254d27592ec8223df1c58d646262e713188f421e0ed02d80d3e41f00ebe6eb3499970c7861d2dc5582a53509a75535e9a34cd264d2fc9784b825892ba948495244521e8fc47aa3b11c08dd34298fcb7c5992a71460a144cf227910881a3f01e88d3c6542df1548a6c4c01e00e986783021620a384ec26812e092047c22c112085840c1f80f707883a81c80dc06b034012809104802340e206e03681a806c03201700a404e024011807803a01c00c805002400f0070024010007 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
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
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record056_frame001_indices (c : Fin record056.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19e7ce0e28f0b384ac19e042dc36c4b56da6ad0b66eaf3d73eb3f584aafd2de9474989f1cf1a77733698ecc2a495231913c6623011738a9c4f2260d7268ab331796a9f525a8492388fa46b22610c681c3fd9fa0fac7c73db9e98f2a6972b5945c9bc3e81e30e886c832f1740b1c5682a21498a0c4e4261112083c3fe1fa0f9878c39c1c20dd064431217b0ba85b42ce14409e84d425e12808c84301fc0f607803880e206d033017c0ba05b02b81540a803901a80b804e025011807c03a01c00c8054024011008003801800a004001c00a0040018008002000 } : Fields).get c.val)
theorem record056_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record056.data.requiredEdges q = true := by decide +kernel
theorem record056_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record056_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record056_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1) (record056.inverseMaps 1) record056_frame001_indices (Fin.ofNat record056.n i)) 128 133 :=
  interval_of_check _ 128 5 (by decide +kernel)
theorem record056_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record056) (record056.maps 1)
      (record056.inverseMaps 1) record056_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 133 record056_frame001_links_0000 (interval_append _ 64 128 133 record056_frame001_links_0064 record056_frame001_links_0128))
theorem record056_frame001_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) : Supported record056 1 :=
  of_group record056 1 (embedding record056) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record056_frame001_indices record056_frame001_graph record056_frame001_links
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (Fin.cases (record056_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record056_frames_supported
theorem record057_frame000_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    Supported record057 0 :=
  of_identity record057 0 (by decide +kernel)
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30d5859c2260b70336bfb56da6ad0b66eb13582eb3357eab44bee5c12c992848de4531a28c545de2130f0871b461996b05524a8451a289942120c10427e73eb1f20f6e7a73ca1744a2a4dd1ce8d9461c2fc1768acc54429414189cc4c02240e787243841b40d6869833a1880be05d42dc1660a204f426a12f094046422610c08283d81b609803d81d40da06602f81680b005702b015008603d01a80b804e022010007c03c01c00c8054024011006803001600a004801c00a0040018008002000 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
def record059_frame001_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x33cf9c1c5f62a30b382ac085b86d896adb4059bac41605af0d726b654b7a51d2628f545fa29d08e8234039f1cf1a7773ad9ca4df655f29093c496247f22d8afc52226911187c439da36ccd546292142691c47d234518289a431a0c10387fb3f49f6cf4a7932ac14509be3e81e30e7471a3661978bf05d02c715a8a9c4e225f10787fc3f41f30ef07403841ba0da069832218a0c085b02ca14409e84d425e12809084642180f607803540f607103301740b605a02b81580aa04301c80b804a023011007c03c01d00c8054022010007003401800a004802000a0040018008002000 } : Fields).get c.val)
theorem record059_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record059_frame001_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1) (record059.inverseMaps 1) record059_frame001_indices (Fin.ofNat record059.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record059_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record059) (record059.maps 1)
      (record059.inverseMaps 1) record059_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record059_frame001_links_0000 (interval_append _ 64 128 138 record059_frame001_links_0064 record059_frame001_links_0128))
theorem record059_frame001_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 1 :=
  of_group record059 1 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record059_frame001_indices record059_frame001_graph record059_frame001_links
def record059_frame002_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0859.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0859.count (({ width := 12, code := 0x90e9078df8d78bf8b78ab87d87586385b85384b84483d83682f81981881581481381080a8088058038017fe7fd7fb7f97d17cd7c97be7bb7b779178d78977e77b7776c66b46055f45e656c55553d5305194f84da4c94b24a549b4874803e13d23c435734833332d31b3022ed2de2cf2c62bd2af2aa2452382302262091f41e41dd1d51c41a519918f18117a14613a12d11f1131070fb0eb0cd0c50a207106a06005905705605305205104103902e02502302201f01e01d01901501101000e00d00c00a009008005004003002001000 } : Fields).get c.val)
theorem record059_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record059_frame002_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record059) (record059.maps 2) (record059.inverseMaps 2) record059_frame002_indices (Fin.ofNat record059.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record059_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0859.localPairCheck (embedding (N := 44310) record059) (record059.maps 2)
      (record059.inverseMaps 2) record059_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record059_frame002_links_0000 (interval_append _ 64 128 138 record059_frame002_links_0064 record059_frame002_links_0128))
theorem record059_frame002_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 2 :=
  of_group record059 2 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group0859
    Papers.RationalityTen.SharedFrameCatalogue.group0859_facts record059_frame002_indices record059_frame002_graph record059_frame002_links
def record059_frame003_indices (c : Fin record059.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0858.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0858.count (({ width := 11, code := 0x27ecfb9e33c275ce79c936a6bcd49a1336664cb99131e61cbe97b2ee5d4b996f2d2594b095d2ae54ca894d2924bc9592723e46c8a8f71ea3bc738e31ba0ec0f75ce81c835f6aed29a3b3c65ac798ab09606bf9762e750e9e534a364568790c20c3fe7ccf51e13b875ce29c0320618c117b2cc560a69472864d49011922841c818ed1cc3806c8d119a3145d8a8148234360650b41482804f09812c2503f06e0b41282304407c0f01d0320540881001c0340600a0120200280400600800800 } : Fields).get c.val)
theorem record059_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.graphBitCheck record059.data.requiredEdges q = true := by decide +kernel
theorem record059_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (embedding (N := 44310) record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record059_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (embedding (N := 44310) record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 64 128 :=
  interval_of_check _ 64 64 (by decide +kernel)
theorem record059_frame003_links_0128 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (embedding (N := 44310) record059) (record059.maps 3) (record059.inverseMaps 3) record059_frame003_indices (Fin.ofNat record059.n i)) 128 138 :=
  interval_of_check _ 128 10 (by decide +kernel)
theorem record059_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0858.localPairCheck (embedding (N := 44310) record059) (record059.maps 3)
      (record059.inverseMaps 3) record059_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 138 record059_frame003_links_0000 (interval_append _ 64 128 138 record059_frame003_links_0064 record059_frame003_links_0128))
theorem record059_frame003_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) : Supported record059 3 :=
  of_group record059 3 (embedding record059) hcells Papers.RationalityTen.SharedFrameCatalogue.group0858
    Papers.RationalityTen.SharedFrameCatalogue.group0858_facts record059_frame003_indices record059_frame003_graph record059_frame003_links
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (Fin.cases (record059_frame001_supported hcells) (Fin.cases (record059_frame002_supported hcells) (Fin.cases (record059_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1451a1ed082819319981cba65a52bc94dc9e24c324e68c33fd9dca9853324b11f48df469a33118c8be45ba2c11548a244da24911669131414f09a64c826092e09664ad253127493049124512048fa47723791a46022c713d09ac4b024c11e08b443420e100065c3101750b4856429413709584741f00f007483881b60d405902780ea06a03481980b605a02180f407203501900c405c02a013008c044019007003401600a004802000e005002000c004001 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
def record062_frame001_indices (c : Fin record062.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0857.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0857.count (({ width := 11, code := 0x1c9f8ef04ddfb335d6b3d5dab34ee9cd35a4746689d0f9d739665ca58d713619c317e6fa5f3b8f6dec54ff9bd33238c4286107e0a3f87ccf7de53886fedddab34e68ecf59bb3065cca59231b62ac3d71ad357eac956aaa524a4540a7e4cc98124a373d0738dd1ab33e610be1672c2570aa1452744c0820ff1d438c6c0d3196310600b616429c5189412220c4106a0d21742383d04c0941180c01402403003 } : Fields).get c.val)
theorem record062_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.graphBitCheck record062.data.requiredEdges q = true := by decide +kernel
theorem record062_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record062_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (embedding (N := 44310) record062) (record062.maps 1) (record062.inverseMaps 1) record062_frame001_indices (Fin.ofNat record062.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record062_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0857.localPairCheck (embedding (N := 44310) record062) (record062.maps 1)
      (record062.inverseMaps 1) record062_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record062_frame001_links_0000 record062_frame001_links_0064)
theorem record062_frame001_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) : Supported record062 1 :=
  of_group record062 1 (embedding record062) hcells Papers.RationalityTen.SharedFrameCatalogue.group0857
    Papers.RationalityTen.SharedFrameCatalogue.group0857_facts record062_frame001_indices record062_frame001_graph record062_frame001_links
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (Fin.cases (record062_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x1d3ee9169cb4dd4a6a4050c285540c9f54f2a75938a9b1499246d1f48ef46f23291708a7449a210c946353099840c025f12f19750b885b325412588f8474233916889843f21910946ac33f18f0c646142fb1760b7459c2bd15a0a8050a27b13789884aa24911e08c045821c10487e03d61d60e306a03381900c285e42da0b205581fc0f006602f80f406c02e01380640240060028010006002 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
def record063_frame002_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0714.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0714.count (({ width := 9, code := 0x353a8d3e9b1386c05fef979bb5cee16ab1582bd5bacd5aa751a752e39198a44e210d8541e08ff6c359a6d26833998ca6431554a65027d36984aa451c894421502803e9ecf2763a1c4e06d3519cc8612f970b4592c158aa42208f076381b8a45022108502206028100602 } : Fields).get c.val)
theorem record063_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (embedding (N := 44310) record063) (record063.maps 2) (record063.inverseMaps 2) record063_frame002_indices (Fin.ofNat record063.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record063_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0714.localPairCheck (embedding (N := 44310) record063) (record063.maps 2)
      (record063.inverseMaps 2) record063_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record063_frame002_links_0000 record063_frame002_links_0064)
theorem record063_frame002_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 2 :=
  of_group record063 2 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0714
    Papers.RationalityTen.SharedFrameCatalogue.group0714_facts record063_frame002_indices record063_frame002_graph record063_frame002_links
def record063_frame003_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0689.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0689.count (({ width := 9, code := 0x25127934963517894461d0b8441604fd7dbe5f0f579bc5deed75ba9a2ce653258cc3602f574b651a853e9e4e26930964a249188942a11027e3d9e0ea71381b8d86b3499cca633097cbc5b2c154a44f27134984b2512490371b0c4602d16090461d0e04420050200c0401 } : Fields).get c.val)
theorem record063_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0689.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0689.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0689.localPairCheck (embedding (N := 44310) record063) (record063.maps 3) (record063.inverseMaps 3) record063_frame003_indices (Fin.ofNat record063.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record063_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0689.localPairCheck (embedding (N := 44310) record063) (record063.maps 3)
      (record063.inverseMaps 3) record063_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record063_frame003_links_0000 record063_frame003_links_0064)
theorem record063_frame003_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 3 :=
  of_group record063 3 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group0689
    Papers.RationalityTen.SharedFrameCatalogue.group0689_facts record063_frame003_indices record063_frame003_graph record063_frame003_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (Fin.cases (record063_frame002_supported hcells) (Fin.cases (record063_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record065_frames_supported
theorem record066_frame000_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    Supported record066 0 :=
  of_identity record066 0 (by decide +kernel)
theorem record066_frames_supported (hcells : ∀ c, record066.data.cells c = FacetUniverses.FullSix0.cells (embedding record066 c)) :
    ∀ f : Fin record066.g, Supported record066 f :=
  (Fin.cases (record066_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record066_frames_supported
theorem record067_frame000_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    Supported record067 0 :=
  of_identity record067 0 (by decide +kernel)
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record067_frames_supported
theorem record068_frame000_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    Supported record068 0 :=
  of_identity record068 0 (by decide +kernel)
theorem record068_frames_supported (hcells : ∀ c, record068.data.cells c = FacetUniverses.FullSix0.cells (embedding record068 c)) :
    ∀ f : Fin record068.g, Supported record068 f :=
  (Fin.cases (record068_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record068_frames_supported
theorem record069_frame000_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    Supported record069 0 :=
  of_identity record069 0 (by decide +kernel)
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1039.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1039.count (({ width := 11, code := 0xce796325e26c3385704df8bc363ec0556a9d4f29d534a654be94d27a493f2764ce9872ea5aca38cf17629c4a88b0b2073d378cef9dd3a772ce3db0b3c66ac9590aee5d8b9d652c85869b13324e4929150ca1441a800fc9f13d4794ef9ad34e614bf1752e05a4b113a26a4c4959262403ec7a0e71c0364658c41862c0548a313c21c430690d01582a8510a01202183904602000800 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1039.localPairCheck (embedding (N := 44310) record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (embedding record070) hcells Papers.RationalityTen.SharedFrameCatalogue.group1039
    Papers.RationalityTen.SharedFrameCatalogue.group1039_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0841.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0841.count (({ width := 11, code := 0xc338630bdf4be37c2e7db4b5f6aac6d6ead3592b1560ab5556a1d3aa2342279cf19992f6584a79491ea3cc6282efedf83c677eee1d53a673ee5dc6b726c0d45a4344622c4177a954e89a52023946489d1121b42882cee1b1314614a39341be330590ac14026c4a09311822c4286a0b40dc120140260400780b01001000800 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0841.localPairCheck (embedding (N := 44310) record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (embedding record071) hcells Papers.RationalityTen.SharedFrameCatalogue.group0841
    Papers.RationalityTen.SharedFrameCatalogue.group0841_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (Fin.cases (record071_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record071_frames_supported
theorem record072_frame000_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    Supported record072 0 :=
  of_identity record072 0 (by decide +kernel)
theorem record072_frames_supported (hcells : ∀ c, record072.data.cells c = FacetUniverses.FullSix0.cells (embedding record072 c)) :
    ∀ f : Fin record072.g, Supported record072 f :=
  (Fin.cases (record072_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record072_frames_supported
theorem record073_frame000_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    Supported record073 0 :=
  of_identity record073 0 (by decide +kernel)
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x8fe3a8ce2f8b62c8ae278962183e057f5f57b5e775dcd715bd6d5ac67190611755a55a44d1043908415013fcfc3e0f23bceb3a4e6388de36cd9318b92d0b02aca12709824c8d214791c06b18c6116c531444e10c421003f0f03b0e438094200641203c0c02c0801404 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x8f2378d6338c62f6859a64d8a61d7e5e16f5b16357d58531414e5304a12044d1143908411013fcfb3e0f23b8eb3a4e5388de370d931cb82d0af2aca02709724c8e2007419862180561485010c400ec380c42a09825084200641203c0c02c080140400c0200400 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
def record075_frame001_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x8f63b8e2368d2328c22e82a007e1f07a1e275dcd715bd6d5ac69da46719865590631846017a5d5715a565569564511043507415023f8fc3e4f13bcec3a0e638cdf36cd8328c630cbb2e4b62c8b02b4a32849e26898254912348a214811e4751c06b19c631845b15c531444e108410fc3e0f03b0e43809c220641202c04 } : Fields).get c.val)
theorem record075_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record075) (record075.maps 1) (record075.inverseMaps 1) record075_frame001_indices (Fin.ofNat record075.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record075_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record075) (record075.maps 1)
      (record075.inverseMaps 1) record075_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record075_frame001_links_0000 record075_frame001_links_0064)
theorem record075_frame001_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 1 :=
  of_group record075 1 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record075_frame001_indices record075_frame001_graph record075_frame001_links
def record075_frame002_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb3c59b6b09570aa2d4e28213f572cb869bd2d7169f33257e8bb55c22c315b2a644db268531e9884bba5ad2c89564a7a4c524a91e48824251dc8e72d4964cb0053f2981474a0e4f927312288f846c22b912086e40f1fe8fac6743241888b405822ae14c0a284ee21b10687f43d01d90e4068031c17c09e04d424e12008b043020c0fe07b83ac1ca0de06c034014c0a5047823810608203601ac0980350138070024007 } : Fields).get c.val)
theorem record075_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record075) (record075.maps 2) (record075.inverseMaps 2) record075_frame002_indices (Fin.ofNat record075.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record075_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record075) (record075.maps 2)
      (record075.inverseMaps 2) record075_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record075_frame002_links_0000 record075_frame002_links_0064)
theorem record075_frame002_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 2 :=
  of_group record075 2 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record075_frame002_indices record075_frame002_graph record075_frame002_links
def record075_frame003_indices (c : Fin record075.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1013.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1013.count (({ width := 7, code := 0xc78b0e0bf7aedcb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record075_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1013.graphBitCheck record075.data.requiredEdges q = true := by decide +kernel
theorem record075_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1013.localPairCheck (embedding (N := 44310) record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record075_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1013.localPairCheck (embedding (N := 44310) record075) (record075.maps 3) (record075.inverseMaps 3) record075_frame003_indices (Fin.ofNat record075.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record075_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1013.localPairCheck (embedding (N := 44310) record075) (record075.maps 3)
      (record075.inverseMaps 3) record075_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record075_frame003_links_0000 record075_frame003_links_0064)
theorem record075_frame003_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) : Supported record075 3 :=
  of_group record075 3 (embedding record075) hcells Papers.RationalityTen.SharedFrameCatalogue.group1013
    Papers.RationalityTen.SharedFrameCatalogue.group1013_facts record075_frame003_indices record075_frame003_graph record075_frame003_links
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (Fin.cases (record075_frame001_supported hcells) (Fin.cases (record075_frame002_supported hcells) (Fin.cases (record075_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
def record076_frame001_indices (c : Fin record076.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x8d2328c22e8a62688e206257d5b962549474fd364b9264511143507411023f8fb3e4f13b8ec3a0e538cdf370d8328c730cbb2e0b62c8af2b4a32809e26897254912388a1f8721906218054148501043e0ec380d4320c42e0ac2a09c26088210641202c0400c0200400 } : Fields).get c.val)
theorem record076_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record076.data.requiredEdges q = true := by decide +kernel
theorem record076_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record076_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record076) (record076.maps 1) (record076.inverseMaps 1) record076_frame001_indices (Fin.ofNat record076.n i)) 64 84 :=
  interval_of_check _ 64 20 (by decide +kernel)
theorem record076_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record076) (record076.maps 1)
      (record076.inverseMaps 1) record076_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 84 record076_frame001_links_0000 record076_frame001_links_0064)
theorem record076_frame001_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) : Supported record076 1 :=
  of_group record076 1 (embedding record076) hcells Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record076_frame001_indices record076_frame001_graph record076_frame001_links
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (Fin.cases (record076_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x84884784681981881778077f75f75d73973172b7117076fd6cb6ae69465c6405da5d95bc5ae5a753b53050b4fe4f14a347046a44a4203ef39e39d35e3503492ff2f42a829b28e24a23422e2021e61d21c91c61b416215e14c14814113410e1050fa0f10ee0e50c00ba0b10a90a80a40a207206b06205b03803402802401000f00b007004001 } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 89 :=
  interval_of_check _ 64 25 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 89 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (embedding record077) hcells Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (Fin.cases (record077_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record077_frames_supported
theorem record078_frame000_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    Supported record078 0 :=
  of_identity record078 0 (by decide +kernel)
theorem record078_frames_supported (hcells : ∀ c, record078.data.cells c = FacetUniverses.FullSix0.cells (embedding record078 c)) :
    ∀ f : Fin record078.g, Supported record078 f :=
  (Fin.cases (record078_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record078_frames_supported
theorem record079_frame000_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    Supported record079 0 :=
  of_identity record079 0 (by decide +kernel)
def record079_frame001_indices (c : Fin record079.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc2860e6d3f68aa8454069f14ef9cece126b734d9564a363cd1cd88743d60a70247b13b89be4c6a60faf7d618aea54729c94c29864aaa3651868ab42ca0c504880f3f59f4cf8a7b639b1bacd565d82db1568a7c52d229108474a38f1bb8c945fa2f016d8adc53e291141090445821a10988083ec1ef0f087683541a80cd86342f21770b7850026212509184542120ff07903a81c80dc069024010608203981b00c005c02a012c09403b01a00a004801c } : Fields).get c.val)
theorem record079_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record079.data.requiredEdges q = true := by decide +kernel
theorem record079_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record079_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1) (record079.inverseMaps 1) record079_frame001_indices (Fin.ofNat record079.n i)) 64 108 :=
  interval_of_check _ 64 44 (by decide +kernel)
theorem record079_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record079) (record079.maps 1)
      (record079.inverseMaps 1) record079_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 108 record079_frame001_links_0000 record079_frame001_links_0064)
theorem record079_frame001_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) : Supported record079 1 :=
  of_group record079 1 (embedding record079) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record079_frame001_indices record079_frame001_graph record079_frame001_links
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (Fin.cases (record079_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record079_frames_supported
theorem record080_frame000_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    Supported record080 0 :=
  of_identity record080 0 (by decide +kernel)
theorem record080_frames_supported (hcells : ∀ c, record080.data.cells c = FacetUniverses.FullSix0.cells (embedding record080 c)) :
    ∀ f : Fin record080.g, Supported record080 f :=
  (Fin.cases (record080_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record080_frames_supported
theorem record081_frame000_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    Supported record081 0 :=
  of_identity record081 0 (by decide +kernel)
def record081_frame001_indices (c : Fin record081.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xa024fa6315174819c081f48f957c2bde5ec4f35786b4c1a3acbd654323d596ab852c290d45495f4a524691fa8e9471a2c1140891419207d0187ae3bc1d14e5e6f92d99680afe50727b137c91e47e235915c88a4272078ffc7e03441988c40530287138088041e1fc0f407583701a00c8060426011507b038c1b60d705282080c606002f81700ac05401a80d005002400e004c01e0070020008002000 } : Fields).get c.val)
theorem record081_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record081.data.requiredEdges q = true := by decide +kernel
theorem record081_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record081_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record081) (record081.maps 1) (record081.inverseMaps 1) record081_frame001_indices (Fin.ofNat record081.n i)) 64 96 :=
  interval_of_check _ 64 32 (by decide +kernel)
theorem record081_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record081) (record081.maps 1)
      (record081.inverseMaps 1) record081_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 96 record081_frame001_links_0000 record081_frame001_links_0064)
theorem record081_frame001_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) : Supported record081 1 :=
  of_group record081 1 (embedding record081) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record081_frame001_indices record081_frame001_graph record081_frame001_links
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (Fin.cases (record081_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record081_frames_supported
theorem record082_frame000_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    Supported record082 0 :=
  of_identity record082 0 (by decide +kernel)
theorem record082_frames_supported (hcells : ∀ c, record082.data.cells c = FacetUniverses.FullSix0.cells (embedding record082 c)) :
    ∀ f : Fin record082.g, Supported record082 f :=
  (Fin.cases (record082_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record082_frames_supported
theorem record083_frame000_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    Supported record083 0 :=
  of_identity record083 0 (by decide +kernel)
theorem record083_frames_supported (hcells : ∀ c, record083.data.cells c = FacetUniverses.FullSix0.cells (embedding record083 c)) :
    ∀ f : Fin record083.g, Supported record083 f :=
  (Fin.cases (record083_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record083_frames_supported
theorem record084_frame000_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    Supported record084 0 :=
  of_identity record084 0 (by decide +kernel)
theorem record084_frames_supported (hcells : ∀ c, record084.data.cells c = FacetUniverses.FullSix0.cells (embedding record084 c)) :
    ∀ f : Fin record084.g, Supported record084 f :=
  (Fin.cases (record084_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record084_frames_supported
theorem record085_frame000_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    Supported record085 0 :=
  of_identity record085 0 (by decide +kernel)
theorem record085_frames_supported (hcells : ∀ c, record085.data.cells c = FacetUniverses.FullSix0.cells (embedding record085 c)) :
    ∀ f : Fin record085.g, Supported record085 f :=
  (Fin.cases (record085_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record085_frames_supported
theorem record086_frame000_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    Supported record086 0 :=
  of_identity record086 0 (by decide +kernel)
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0655.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0655.count (({ width := 12, code := 0x81d81a80f7e07c87c378378075373b72e6f66f36e16d76d56d06bf6ba6af69e69366666362761f5f25d95c25a558b57f54e53a51d4fe4ec4e049048a47847547346143942541b4073c63b339237e37136431b3102ed2e72dd2c02bb2b726e26124c2051f81ef1c61ab1a518f18917916815412e11b10d0ff0f90e20d80c40a908707c06f06105505405204104003402501f01c01300d00a007004001000 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0655.localPairCheck (embedding (N := 44310) record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (embedding record089) hcells Papers.RationalityTen.SharedFrameCatalogue.group0655
    Papers.RationalityTen.SharedFrameCatalogue.group0655_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
def record090_frame001_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0585.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0585.count (({ width := 8, code := 0xd1d0cfcecdcccbcac9c8c7c6c4c2c1beb8b7b5b0afa9a7a39f9a9491908d8c87807f7b7a7877757372706f6c6a676661605f5e5c5b585352504f4d4b48473d3b383634312f2b2a262421201e1d1c1b1a19171513110c0b0605020100 } : Fields).get c.val)
theorem record090_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (embedding (N := 44310) record090) (record090.maps 1) (record090.inverseMaps 1) record090_frame001_indices (Fin.ofNat record090.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record090_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0585.localPairCheck (embedding (N := 44310) record090) (record090.maps 1)
      (record090.inverseMaps 1) record090_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record090_frame001_links_0000 record090_frame001_links_0064)
theorem record090_frame001_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 1 :=
  of_group record090 1 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0585
    Papers.RationalityTen.SharedFrameCatalogue.group0585_facts record090_frame001_indices record090_frame001_graph record090_frame001_links
def record090_frame002_indices (c : Fin record090.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0584.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0584.count (({ width := 7, code := 0xb76acd8af5aad4a74a8d09f3a6cc972a4c88f1a2c4870a0c07ef9ebc76e9cb86ed9ab466c98b05eb96ac56a94a84e992a446890a03e78e9c3668c982e58a9426488901e3868c16284880e182840608080 } : Fields).get c.val)
theorem record090_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0584.graphBitCheck record090.data.requiredEdges q = true := by decide +kernel
theorem record090_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0584.localPairCheck (embedding (N := 44310) record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record090_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0584.localPairCheck (embedding (N := 44310) record090) (record090.maps 2) (record090.inverseMaps 2) record090_frame002_indices (Fin.ofNat record090.n i)) 64 92 :=
  interval_of_check _ 64 28 (by decide +kernel)
theorem record090_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0584.localPairCheck (embedding (N := 44310) record090) (record090.maps 2)
      (record090.inverseMaps 2) record090_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 92 record090_frame002_links_0000 record090_frame002_links_0064)
theorem record090_frame002_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) : Supported record090 2 :=
  of_group record090 2 (embedding record090) hcells Papers.RationalityTen.SharedFrameCatalogue.group0584
    Papers.RationalityTen.SharedFrameCatalogue.group0584_facts record090_frame002_indices record090_frame002_graph record090_frame002_links
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (Fin.cases (record090_frame001_supported hcells) (Fin.cases (record090_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record090_frames_supported
theorem record091_frame000_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    Supported record091 0 :=
  of_identity record091 0 (by decide +kernel)
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
def record092_frame001_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1032.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1032.count (({ width := 9, code := 0xcde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b017ebd5e2ed75b9dbed364add62ad54a95469145994b63d1b8943e1b09843fdf8f8783b9cce36f36db0cf65b1988c05ead96ab057a91449d4ca591a8c42a11007b3b1d4d06530978ae552812c92431d8d4622e160ac502712888381a0b844200b038080200 } : Fields).get c.val)
theorem record092_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (embedding (N := 44310) record092) (record092.maps 1) (record092.inverseMaps 1) record092_frame001_indices (Fin.ofNat record092.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record092_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1032.localPairCheck (embedding (N := 44310) record092) (record092.maps 1)
      (record092.inverseMaps 1) record092_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record092_frame001_links_0000 record092_frame001_links_0064)
theorem record092_frame001_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 1 :=
  of_group record092 1 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group1032
    Papers.RationalityTen.SharedFrameCatalogue.group1032_facts record092_frame001_indices record092_frame001_graph record092_frame001_links
def record092_frame002_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0644.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0644.count (({ width := 11, code := 0xbe57c2f75ecbd571adcd9fb35656c657faef5d6b7d6bacf536a2d40a754b694521a3946a825009db3aa714df9a52ca50c958f317a2bc4e8970fe15421770e99b736266ec6187ae85cab4566ac8514a01352654b894122a2d442845051fc3e8798f11a934e628c297b2dc580a21422644b49111521a4246e8d619e3205e0b21542884c08c0ee1882b85309c12c228440820e41802904a06c0a00b00e00800800 } : Fields).get c.val)
theorem record092_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record092) (record092.maps 2) (record092.inverseMaps 2) record092_frame002_indices (Fin.ofNat record092.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record092_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0644.localPairCheck (embedding (N := 44310) record092) (record092.maps 2)
      (record092.inverseMaps 2) record092_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record092_frame002_links_0000 record092_frame002_links_0064)
theorem record092_frame002_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 2 :=
  of_group record092 2 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group0644
    Papers.RationalityTen.SharedFrameCatalogue.group0644_facts record092_frame002_indices record092_frame002_graph record092_frame002_links
def record092_frame003_indices (c : Fin record092.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0582.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0582.count (({ width := 7, code := 0xfbf3dfaf3e3bf6ebd39f2e3c37eedbb35ead3a33e6cb931e2c382fdebb72ddab362bd6ab529d2a3427ce9b325ca93223c5890e0c07ef9ebc76e9cb86ed9ab466c98b05eb962b54a54274c952234280f9e3a70d9a3260b962a50992224070d18244060808080 } : Fields).get c.val)
theorem record092_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.graphBitCheck record092.data.requiredEdges q = true := by decide +kernel
theorem record092_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (embedding (N := 44310) record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record092_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (embedding (N := 44310) record092) (record092.maps 3) (record092.inverseMaps 3) record092_frame003_indices (Fin.ofNat record092.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record092_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0582.localPairCheck (embedding (N := 44310) record092) (record092.maps 3)
      (record092.inverseMaps 3) record092_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record092_frame003_links_0000 record092_frame003_links_0064)
theorem record092_frame003_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) : Supported record092 3 :=
  of_group record092 3 (embedding record092) hcells Papers.RationalityTen.SharedFrameCatalogue.group0582
    Papers.RationalityTen.SharedFrameCatalogue.group0582_facts record092_frame003_indices record092_frame003_graph record092_frame003_links
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (Fin.cases (record092_frame001_supported hcells) (Fin.cases (record092_frame002_supported hcells) (Fin.cases (record092_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record092_frames_supported
theorem record093_frame000_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    Supported record093 0 :=
  of_identity record093 0 (by decide +kernel)
theorem record093_frames_supported (hcells : ∀ c, record093.data.cells c = FacetUniverses.FullSix0.cells (embedding record093 c)) :
    ∀ f : Fin record093.g, Supported record093 f :=
  (Fin.cases (record093_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record093_frames_supported
theorem record094_frame000_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    Supported record094 0 :=
  of_identity record094 0 (by decide +kernel)
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0865.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0865.count (({ width := 12, code := 0x91d9028d68bb88988687186085d85b85885485284d84784484083582c82381480e8037f57f17e27dc7d47ce7cd7cb7c27bb7b47a979f78d78677c77476774474173d6dc6c765063a6245a558957153e53a53552b5254cf4b54274163fe36835d33d31330e3052ff2f92b529525123822d2162091cd1c91b01aa18617716a13d1321201130ea0e30d60c60c10ba0b508d08c07b07a07106105404003f03702801d01000f00b004000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0865.localPairCheck (embedding (N := 44310) record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0865
    Papers.RationalityTen.SharedFrameCatalogue.group0865_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
def record094_frame002_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x83f82a80b7f77de7dd7cf7c17bc7bb7b47a87a679d78c78778277e77d77c76b76275b75875774e74974674173e73d73a73272c7267237127086fe6f76ec6cd6c96c363d62b5be5ac59850d4ef4d349c4974914834784053ec37936034e2b72aa28c25d25224323e2381e61d21b41a319b18b18316215e14c14813813112a10e1050fa0f10de0dc0d60c90c40bc0b609509207c07b07206205504204103802801d01000f00b004000 } : Fields).get c.val)
theorem record094_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record094) (record094.maps 2) (record094.inverseMaps 2) record094_frame002_indices (Fin.ofNat record094.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record094_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record094) (record094.maps 2)
      (record094.inverseMaps 2) record094_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record094_frame002_links_0000 record094_frame002_links_0064)
theorem record094_frame002_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 2 :=
  of_group record094 2 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record094_frame002_indices record094_frame002_graph record094_frame002_links
def record094_frame003_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0819.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0819.count (({ width := 11, code := 0xb3f65ac7580af35e2ba572ad75a6b2d62abf56eab554aa5536a4d44a794d69852aa514768c513a17426845039f73ce77cee9c93726b4d09992e25a4ad8d918a1241a81eefdd5b9e6ecdcdb53616aec51842be55aa8928a4b47886d082043fc7e8e19b632c620c09772dc54ca79402784988d1121ea3a4708da1822f0598a71422684a0750e61883085d0a41181c83806609c0e81001e02c02000 } : Fields).get c.val)
theorem record094_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record094) (record094.maps 3) (record094.inverseMaps 3) record094_frame003_indices (Fin.ofNat record094.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record094_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0819.localPairCheck (embedding (N := 44310) record094) (record094.maps 3)
      (record094.inverseMaps 3) record094_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record094_frame003_links_0000 record094_frame003_links_0064)
theorem record094_frame003_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 3 :=
  of_group record094 3 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group0819
    Papers.RationalityTen.SharedFrameCatalogue.group0819_facts record094_frame003_indices record094_frame003_graph record094_frame003_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (Fin.cases (record094_frame002_supported hcells) (Fin.cases (record094_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
def record095_frame001_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x2961443a15504e6bf2cc95b4a8a22f09383fc1bdc16dd56d6b4f1a28cb861eaffd7aab5d599ab553d29da4dfa5d12d295549f24c923a8c145b228911687f435212d08c83e3ef1e80eda6f636199bcb6c59b2c59558a825372959458a184c925a12a893c48923f919c8c045c1d70e5c6f83431990c746243001760a8852227c138897c496233115888c38c1b40d086202f21690ab850c272130092846020c0fc07983a01b60d203281880bc05901600a404a02000b004c01e00a0018008002000 } : Fields).get c.val)
theorem record095_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record095) (record095.maps 1) (record095.inverseMaps 1) record095_frame001_indices (Fin.ofNat record095.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record095_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record095) (record095.maps 1)
      (record095.inverseMaps 1) record095_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record095_frame001_links_0000 record095_frame001_links_0064)
theorem record095_frame001_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 1 :=
  of_group record095 1 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record095_frame001_indices record095_frame001_graph record095_frame001_links
def record095_frame002_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x22043e8770e21942e85509a0c41582503deebd97acf05df3aa726e31c236f6ced459532563cc2181afc5ecbd177ad459eb21612c0576ac1572a9526a0d3c25c4a28e90e21141c7f4f91ef3d6798f21d138c70cdf9ba3706c8d69ab31c614bd1632b453ca514528049c8f11321c424820fd1f03cc6e8d519e324628c21782c8570ab14a2784c09412222c420810aa1502804b05209c1181e02c04c0780a00600800800 } : Fields).get c.val)
theorem record095_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record095) (record095.maps 2) (record095.inverseMaps 2) record095_frame002_indices (Fin.ofNat record095.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record095_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record095) (record095.maps 2)
      (record095.inverseMaps 2) record095_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record095_frame002_links_0000 record095_frame002_links_0064)
theorem record095_frame002_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 2 :=
  of_group record095 2 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record095_frame002_indices record095_frame002_graph record095_frame002_links
def record095_frame003_indices (c : Fin record095.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1012.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1012.count (({ width := 8, code := 0xc7c5c3c1bfbdbbb9b7b6b5b4b3b2b1b0afaeadaba9a7a5a3a09f9d9b9a9896959391908e8c8b89878684817e7b787572716e6d6c6968676463625f5e5d5a59585554514f4d4b4947464442403e3c3b3937363432302e2d2b29282725232221201e1c1b1a19181716151412100e0c0a08060403020100 } : Fields).get c.val)
theorem record095_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1012.graphBitCheck record095.data.requiredEdges q = true := by decide +kernel
theorem record095_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record095) (record095.maps 3) (record095.inverseMaps 3) record095_frame003_indices (Fin.ofNat record095.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record095_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record095) (record095.maps 3) (record095.inverseMaps 3) record095_frame003_indices (Fin.ofNat record095.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record095_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record095) (record095.maps 3)
      (record095.inverseMaps 3) record095_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record095_frame003_links_0000 record095_frame003_links_0064)
theorem record095_frame003_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) : Supported record095 3 :=
  of_group record095 3 (embedding record095) hcells Papers.RationalityTen.SharedFrameCatalogue.group1012
    Papers.RationalityTen.SharedFrameCatalogue.group1012_facts record095_frame003_indices record095_frame003_graph record095_frame003_links
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (Fin.cases (record095_frame001_supported hcells) (Fin.cases (record095_frame002_supported hcells) (Fin.cases (record095_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa56d0fa84940d9af4b2e5692a0615afcd786b51590ab393de9d84dfa5ed2cc9554a2a4bd23a8c8459a28912487c435213508a83e4019fc4fbc7bd3d79e80f207803b69c4ce0a6f63731b58d8667c33a99bcb5e59f2c5953ca8a5372921468a184c225c12a892e48d23f91948c245c2018f007563931be0d3c68232e18e8c405f82ec1570a8051a27c137896c496232115088c3921b60d0862c2f61690ab851427613009284602100fe07983a01b60d201680a804c02100b8058028013008003c01600a0018008002000 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
def record096_frame002_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1064.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1064.count (({ width := 11, code := 0x87f0f21cc368630b614c25722e29c036d6c6d3596b2463cc2d812fc5f0bcd77ad759cb21622bf576ac956aa953aa6149a8d510a0d3fa7b4f099930a5c4b095128a4147a8e90ca1441c7e8fa9ef3d279cf21ce39270cde9bb3706c0d71ab34464cc69822f45a0b115729e524a21402584988d91321a420820fc1ee3cc6f0d719e32c630c21782d0578ab14a2784d09512222c420810540a01201f02e0580a01302003c0580a00600800800 } : Fields).get c.val)
theorem record096_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record096) (record096.maps 2) (record096.inverseMaps 2) record096_frame002_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record096) (record096.maps 2) (record096.inverseMaps 2) record096_frame002_indices (Fin.ofNat record096.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record096_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1064.localPairCheck (embedding (N := 44310) record096) (record096.maps 2)
      (record096.inverseMaps 2) record096_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record096_frame002_links_0000 record096_frame002_links_0064)
theorem record096_frame002_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 2 :=
  of_group record096 2 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1064
    Papers.RationalityTen.SharedFrameCatalogue.group1064_facts record096_frame002_indices record096_frame002_graph record096_frame002_links
def record096_frame003_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1012.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1012.count (({ width := 8, code := 0xc6c4c2c0bebcbab8acaaa8a6a4a2a19e9d9c9998979493928f8e8d8a89888584838281807f7e7d7c7b7a7978777675747372706f6d6b6a6866656361605e5c5b595756545352504e4d4c4a4847454342413f3d3c3a3837353332312f2d2c2a282726242221201f1d1b1a191813110f0d0b0a09080706050403020100 } : Fields).get c.val)
theorem record096_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1012.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record096) (record096.maps 3) (record096.inverseMaps 3) record096_frame003_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record096) (record096.maps 3) (record096.inverseMaps 3) record096_frame003_indices (Fin.ofNat record096.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record096_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1012.localPairCheck (embedding (N := 44310) record096) (record096.maps 3)
      (record096.inverseMaps 3) record096_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record096_frame003_links_0000 record096_frame003_links_0064)
theorem record096_frame003_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 3 :=
  of_group record096 3 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1012
    Papers.RationalityTen.SharedFrameCatalogue.group1012_facts record096_frame003_indices record096_frame003_graph record096_frame003_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (Fin.cases (record096_frame002_supported hcells) (Fin.cases (record096_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record096_frames_supported
theorem record097_frame000_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    Supported record097 0 :=
  of_identity record097 0 (by decide +kernel)
theorem record097_frames_supported (hcells : ∀ c, record097.data.cells c = FacetUniverses.FullSix0.cells (embedding record097 c)) :
    ∀ f : Fin record097.g, Supported record097 f :=
  (Fin.cases (record097_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record097_frames_supported
theorem record098_frame000_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    Supported record098 0 :=
  of_identity record098 0 (by decide +kernel)
theorem record098_frames_supported (hcells : ∀ c, record098.data.cells c = FacetUniverses.FullSix0.cells (embedding record098 c)) :
    ∀ f : Fin record098.g, Supported record098 f :=
  (Fin.cases (record098_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record098_frames_supported
theorem record099_frame000_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    Supported record099 0 :=
  of_identity record099 0 (by decide +kernel)
theorem record099_frames_supported (hcells : ∀ c, record099.data.cells c = FacetUniverses.FullSix0.cells (embedding record099 c)) :
    ∀ f : Fin record099.g, Supported record099 f :=
  (Fin.cases (record099_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record099_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00077

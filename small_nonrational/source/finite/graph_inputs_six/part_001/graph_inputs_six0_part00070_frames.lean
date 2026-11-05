module
prelude
public import GraphInputsSix0Part00070Data
public import RawFrameSupport
public import SharedFrameGroups069Checked
public import SharedFrameGroups095Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups103Checked
public import SharedFrameGroups106Checked
public import SharedFrameGroups108Checked
public import SharedFrameGroups109Checked
public import SharedFrameGroups110Checked
public import SharedFrameGroups111Checked
public import SharedFrameGroups113Checked
public import SharedFrameGroups116Checked
public import SharedFrameGroups117Checked
public import SharedFrameGroups118Checked
public import SharedFrameGroups119Checked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x30a1839bfb5faa8133c39b64d8e3c11c78d9c68e31717875cb79dab0bb557929d133a95949ba36518689843da09101e7e73e99f14d025be2a011a484a4031d28e3c6c83471780b6c56629f14888ac43a2160f9877039c1ad0cb062027a12e08904301fc0ef074836c15209004681b00d406002f816c0ac05401a00c80500270118078038014009804802000e005802400e0040018008002000 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 94 :=
  interval_of_check _ 64 30 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 94 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
theorem record000_frames_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    ∀ f : Fin record000.g, Supported record000 f :=
  (Fin.cases (record000_frame000_supported hcells) (Fin.cases (record000_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5626b07428a0a4ff27f33ae9c8cdf268914e89d442e1e70ca85b4182092ffe7f83f35f60f3f79b3931b18d4969db4d1a22cfe6782dc9650aff50326f13268cc45ca2c914689b4491f6cf4078f38a1c1cdce6d735b1a04cc264a31316fcb645922c11584a5850c27a93449744ad253125891e48823d91dc8de46b1f28efc72c3681a08aa04d625c11c08a443820b10007143101790aa851827212808e83c41d20e206e03500d405b02700e006e03601a00c8052028013809404601a00880380140090038010006001 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record003_frames_supported
theorem record004_frame000_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) :
    Supported record004 0 :=
  of_identity record004 0 (by decide +kernel)
def record004_frame001_indices (c : Fin record004.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x2fe97e8b7a5b5e7353818f0471e21b0f46dbb029796bb558babc95bcab353a267d2b293446b230d1308304079fe4fce7c53db9b58d2e6812f196f8b5457f2a011ac84a4001d10e3c6c82fc16d8b1456629114188e845e22c112887842e21010587ec3e81e80f0874c3881bc0d7069c3361940c686142f21760b5856c27c138098849423c11c08a84342040ff07903981be0dc069023410c06c03501800be05b02b81580a804e01a00c8050027011807c03c01c } : Fields).get c.val)
theorem record004_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record004.data.requiredEdges q = true := by decide +kernel
theorem record004_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record004_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1) (record004.inverseMaps 1) record004_frame001_indices (Fin.ofNat record004.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record004_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record004) (record004.maps 1)
      (record004.inverseMaps 1) record004_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record004_frame001_links_0000 record004_frame001_links_0064)
theorem record004_frame001_supported (hcells : ∀ c, record004.data.cells c = FacetUniverses.FullSix0.cells (embedding record004 c)) : Supported record004 1 :=
  of_group record004 1 (embedding record004) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record004_frame001_indices record004_frame001_graph record004_frame001_links
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
theorem record011_frames_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    ∀ f : Fin record011.g, Supported record011 f :=
  (Fin.cases (record011_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record011_frames_supported
theorem record012_frame000_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    Supported record012 0 :=
  of_identity record012 0 (by decide +kernel)
def record012_frame001_indices (c : Fin record012.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xa11502e7a739f9b2c2220f105880ebed1f50e357143889b50d62687b32592cc8363e2f6d78cba25c72ce5648b005762b39580ab9556aa9953e9974a9a39114084541ea0d8f0874436d1a68cc264a32318f4bba5b42b8149ca224f8271926890846b23091748ac4521f80f887583981b10cc061e2fa17a0b6458228f13709644a623811508944382160f5873029013b096042c1fc0ef069019c0b805b02b815808404001c00d804601e0080038016009003000c002000 } : Fields).get c.val)
theorem record012_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record012.data.requiredEdges q = true := by decide +kernel
theorem record012_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record012_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1) (record012.inverseMaps 1) record012_frame001_indices (Fin.ofNat record012.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record012_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record012) (record012.maps 1)
      (record012.inverseMaps 1) record012_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record012_frame001_links_0000 record012_frame001_links_0064)
theorem record012_frame001_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) : Supported record012 1 :=
  of_group record012 1 (embedding record012) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record012_frame001_indices record012_frame001_graph record012_frame001_links
theorem record012_frames_supported (hcells : ∀ c, record012.data.cells c = FacetUniverses.FullSix0.cells (embedding record012 c)) :
    ∀ f : Fin record012.g, Supported record012 f :=
  (Fin.cases (record012_frame000_supported hcells) (Fin.cases (record012_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record012_frames_supported
theorem record013_frame000_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    Supported record013 0 :=
  of_identity record013 0 (by decide +kernel)
def record013_frame001_indices (c : Fin record013.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0xaa954ce84540b9d44dd26c0e357143889b4ad0c644b2098f0bdb5e32e8971cb395922c015d8ace5602ae555aaa654fa89d3e09994a224cd242903473224510086e428211507c8364189e18ee074a39b9b70d8c6a034699bccc265a327191cc825dc2db95b4a5451e28813d49c049d248920c8d046122e11588a635e1a78cc063e2bd1570a3c4fc22a11188703e01cc0a404ec26010b07f03cc1a409b048816c0ac02300f006802000f007002c014009003000c002000 } : Fields).get c.val)
theorem record013_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record013.data.requiredEdges q = true := by decide +kernel
theorem record013_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record013_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record013) (record013.maps 1) (record013.inverseMaps 1) record013_frame001_indices (Fin.ofNat record013.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record013_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record013) (record013.maps 1)
      (record013.inverseMaps 1) record013_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record013_frame001_links_0000 record013_frame001_links_0064)
theorem record013_frame001_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) : Supported record013 1 :=
  of_group record013 1 (embedding record013) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record013_frame001_indices record013_frame001_graph record013_frame001_links
theorem record013_frames_supported (hcells : ∀ c, record013.data.cells c = FacetUniverses.FullSix0.cells (embedding record013 c)) :
    ∀ f : Fin record013.g, Supported record013 f :=
  (Fin.cases (record013_frame000_supported hcells) (Fin.cases (record013_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record015_frames_supported (hcells : ∀ c, record015.data.cells c = FacetUniverses.FullSix0.cells (embedding record015 c)) :
    ∀ f : Fin record015.g, Supported record015 f :=
  (Fin.cases (record015_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record018_frames_supported (hcells : ∀ c, record018.data.cells c = FacetUniverses.FullSix0.cells (embedding record018 c)) :
    ∀ f : Fin record018.g, Supported record018 f :=
  (Fin.cases (record018_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record018_frames_supported
theorem record019_frame000_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    Supported record019 0 :=
  of_identity record019 0 (by decide +kernel)
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x99d4c425e32c794f49ce42b020803bf71fa4fb97c73dd9ec4f3378fbba5da6ec375aba7dd1ee8169f33558d8c1b60ab0196d2a4251aa7112be90d482a3d909c84141820390027f03f39cdce4871d3589940c085fe2f99630ae453728e93e09e84e926511cc8ca45d228111086c42e210906876037e1a80c7860a2fd1780ae449a23d109880c3f41d80c906002ec16c0a7851427612608483a40e006c02f816c0ae05502a00e006802f015009c04c02300f8074038014009004001c00b005002000e0040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18c9c59e143073787bbb5d66c5160dacdd6027853b19cd4e066d932f98b4a7a4ff26a8d1462a2ef109878438dff6de76c2b435a02ccb5792ad94aaa34508a69d26e8ce45f22650e0830412203cfce7d33e29edcf4e7942df1608a4250026e91cc80639a1c50d946782fc1780b6c56629f1488a0c4e626010e873c3761ad0d306583101750b7059827a12e0940448218105077836c13c09904801e80d805f02d015c0ac05402100d004e02200f8078038014009004001a00b005002400e0040018008002000 } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record020_frames_supported
theorem record021_frame000_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    Supported record021 0 :=
  of_identity record021 0 (by decide +kernel)
def record021_frame001_indices (c : Fin record021.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1539a93cf6a7873919be443a1ed0da86342c613102d80dbf51f6ef8f7beba01b80d3b68533f59eacea618affd6d6b365832ad954ca7e52f27fd39499a4a524e92248f2470a34d1988bc45ba2b913a8964479e8cdda6b13391998ca06212cc1570a3a51127d93309744ad253126891847d23a91bc8d84091e10eb46ca34418e0c405a22a814c89e84d625e123089c43c1fc0f707a038a1b60cb86202f61630a204ec23210b08283c01d20e206e835415e09b03801b80c205f02400cc064024011806801600a0048014008003 } : Fields).get c.val)
theorem record021_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record021.data.requiredEdges q = true := by decide +kernel
theorem record021_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record021_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1) (record021.inverseMaps 1) record021_frame001_indices (Fin.ofNat record021.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record021_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record021) (record021.maps 1)
      (record021.inverseMaps 1) record021_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record021_frame001_links_0000 record021_frame001_links_0064)
theorem record021_frame001_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) : Supported record021 1 :=
  of_group record021 1 (embedding record021) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record021_frame001_indices record021_frame001_graph record021_frame001_links
theorem record021_frames_supported (hcells : ∀ c, record021.data.cells c = FacetUniverses.FullSix0.cells (embedding record021 c)) :
    ∀ f : Fin record021.g, Supported record021 f :=
  (Fin.cases (record021_frame000_supported hcells) (Fin.cases (record021_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record025_frames_supported (hcells : ∀ c, record025.data.cells c = FacetUniverses.FullSix0.cells (embedding record025 c)) :
    ∀ f : Fin record025.g, Supported record025 f :=
  (Fin.cases (record025_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record025_frames_supported
theorem record026_frame000_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    Supported record026 0 :=
  of_identity record026 0 (by decide +kernel)
def record026_frame001_indices (c : Fin record026.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xad3d652af9568a94d35a98b3b79b3cd4e3ad1bd8d2466e30b16f8a144d624510b87b4385aa6ce063f31a15dca7b50ca80d2d095148da43120c8ff47823a91b88323af1b88d8067f3371750ac652b28393c8952467229110886442320790047e23d11b28bd057829814188e83f01e30e9870c3681a00c906082c414809d04cc23c11708203d81d208d03501840ba05b02b81580aa05401f00e406a032014809404601f00f00740380140080038014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record026_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record026.data.requiredEdges q = true := by decide +kernel
theorem record026_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record026_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1) (record026.inverseMaps 1) record026_frame001_indices (Fin.ofNat record026.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record026_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record026) (record026.maps 1)
      (record026.inverseMaps 1) record026_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record026_frame001_links_0000 record026_frame001_links_0064)
theorem record026_frame001_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) : Supported record026 1 :=
  of_group record026 1 (embedding record026) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record026_frame001_indices record026_frame001_graph record026_frame001_links
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (Fin.cases (record026_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record026_frames_supported
theorem record027_frame000_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) :
    Supported record027 0 :=
  of_identity record027 0 (by decide +kernel)
def record027_frame001_indices (c : Fin record027.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x14a2a4651768933959c04dce6b72ec96acaea53326392843e61c30ca85b42b612906b827c0e1aaed52688b4119f0cee5b3aa7150aa664fda4c12328fa47323691988c345fa2dd1608a9451a26d12488b38d9a04c505c6296134c9844ba256929894049624892288f647723791a47de2ed1638a904d625612488f045a20b10007043101730b3056429412808e83e41e20e9071036c1a80b104e81d80e206a034819c0c405b02d010807003401900c4052025011808801c00d0050024010007002000c004001 } : Fields).get c.val)
theorem record027_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record027.data.requiredEdges q = true := by decide +kernel
theorem record027_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record027_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1) (record027.inverseMaps 1) record027_frame001_indices (Fin.ofNat record027.n i)) 64 121 :=
  interval_of_check _ 64 57 (by decide +kernel)
theorem record027_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record027) (record027.maps 1)
      (record027.inverseMaps 1) record027_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 121 record027_frame001_links_0000 record027_frame001_links_0064)
theorem record027_frame001_supported (hcells : ∀ c, record027.data.cells c = FacetUniverses.FullSix0.cells (embedding record027 c)) : Supported record027 1 :=
  of_group record027 1 (embedding record027) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record027_frame001_indices record027_frame001_graph record027_frame001_links
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
def record029_frame001_indices (c : Fin record029.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x342d9b5c5162330eb824c085e16ee975cb4dda1acdf5e1ae4d6caa93530a8f4f8a78b3ba9cc4dfe6e933b9914c325d32ce961b85d9f6b2851d26911f48bf439a0c103880c3fd9fa4f8e7b73ca97d0a0c4701e30e2c67e2fc1740b6058e2b51498a0c4c223911807cc3b81b40d3065c32218a0c185ec2ea1670ac054828813d09a84a024210c07f03d81e008d03b01c40d406102e816c0ae05602a815007c03901900a404a02300f807803a01c00d00540280100070030014009004001c00a0040018008002000 } : Fields).get c.val)
theorem record029_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record029.data.requiredEdges q = true := by decide +kernel
theorem record029_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record029_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1) (record029.inverseMaps 1) record029_frame001_indices (Fin.ofNat record029.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record029_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record029) (record029.maps 1)
      (record029.inverseMaps 1) record029_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record029_frame001_links_0000 record029_frame001_links_0064)
theorem record029_frame001_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) : Supported record029 1 :=
  of_group record029 1 (embedding record029) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record029_frame001_indices record029_frame001_graph record029_frame001_links
theorem record029_frames_supported (hcells : ∀ c, record029.data.cells c = FacetUniverses.FullSix0.cells (embedding record029 c)) :
    ∀ f : Fin record029.g, Supported record029 f :=
  (Fin.cases (record029_frame000_supported hcells) (Fin.cases (record029_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record029_frames_supported
theorem record030_frame000_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    Supported record030 0 :=
  of_identity record030 0 (by decide +kernel)
def record030_frame001_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb80dbfaddd5e6aeed7269cb4d4a61d0667fd3e39bccd966a330c97acb7a3ad1bd8d2466e30b16f8a144d624510b87b4385aa0c68575a80d35c9a54b4254526c91b489a43120c8ff47823a91b8762337178cba052b27912ac8ce45422110c88464011f88f446e836115e0a0c4781f80f2874c3861b40c906082c41560a4050427413308f045c22010407b03bc1d208d035019c0c406102e816c0ae05602a815006402f01500a404a02300f807803a01c00d00540280100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record030_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1) (record030.inverseMaps 1) record030_frame001_indices (Fin.ofNat record030.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record030_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record030) (record030.maps 1)
      (record030.inverseMaps 1) record030_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record030_frame001_links_0000 record030_frame001_links_0064)
theorem record030_frame001_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 1 :=
  of_group record030 1 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record030_frame001_indices record030_frame001_graph record030_frame001_links
def record030_frame002_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd10e87742d8cec5c628af07772bb3da66d09679aefd71eb77547a9754927c53c59dd4e626ff37499dcc8a6192e99674b0dc28cfb59628e936c9a047d22fd0ea83040f2030ff67e93e39edcf2a5f828312088d83c61c58d045f82ea16c0b1c56a29314189844722300f987703821a60cf065c32218a0bd85d42ce1600a9052c28813d094048423410c07f03dc1e008d035019c0c406102e816c0ae05602a815006402f01500a404a02300f807803a01c00d00540280100070028012008003801800a0040018008002000 } : Fields).get c.val)
theorem record030_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 2) (record030.inverseMaps 2) record030_frame002_indices (Fin.ofNat record030.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record030_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record030) (record030.maps 2)
      (record030.inverseMaps 2) record030_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record030_frame002_links_0000 record030_frame002_links_0064)
theorem record030_frame002_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 2 :=
  of_group record030 2 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record030_frame002_indices record030_frame002_graph record030_frame002_links
def record030_frame003_indices (c : Fin record030.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1113.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1113.count (({ width := 11, code := 0x9d33a273cbf9772de5049d9351fa3d4768c917e2d4478870fe16c2a84f09611c218410720c41181b025c834b5e6ab946a884de9912ca4e49491d22a424768e5199ed35061cc11692bc54ca41442824fc9e1352664b48f1192003d4750df1b63606b0d3198328620c117e2f85e8bc1722e05b8b51662c8588890d01943005f0b61642a8540a61481902f0540a41282303e0780e81c0340540a01001c0280480800e0180280400600800800 } : Fields).get c.val)
theorem record030_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.graphBitCheck record030.data.requiredEdges q = true := by decide +kernel
theorem record030_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record030_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record030) (record030.maps 3) (record030.inverseMaps 3) record030_frame003_indices (Fin.ofNat record030.n i)) 64 124 :=
  interval_of_check _ 64 60 (by decide +kernel)
theorem record030_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1113.localPairCheck (embedding (N := 44310) record030) (record030.maps 3)
      (record030.inverseMaps 3) record030_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 124 record030_frame003_links_0000 record030_frame003_links_0064)
theorem record030_frame003_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) : Supported record030 3 :=
  of_group record030 3 (embedding record030) hcells Papers.RationalityTen.SharedFrameCatalogue.group1113
    Papers.RationalityTen.SharedFrameCatalogue.group1113_facts record030_frame003_indices record030_frame003_graph record030_frame003_links
theorem record030_frames_supported (hcells : ∀ c, record030.data.cells c = FacetUniverses.FullSix0.cells (embedding record030 c)) :
    ∀ f : Fin record030.g, Supported record030 f :=
  (Fin.cases (record030_frame000_supported hcells) (Fin.cases (record030_frame001_supported hcells) (Fin.cases (record030_frame002_supported hcells) (Fin.cases (record030_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record032_frame001_indices (c : Fin record032.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x557e8eb430a0e4ffe7652b994c48fa44911588841f20d305e823b905b02d3360daff57aab725942bb958eab3541a9c140c9bc4c1256d28e91748223811a48cb459a2b0f7879d38e9a10c9e6423119720a5e4fa27693389584972470fe077e37f1b18d046583001700b0c55827a12e090845220c10187c03cc1c90cb85e42be146094848021a103073836818e09204882000b005702b010c080036013808003c01d008804001c00b0048014006000 } : Fields).get c.val)
theorem record032_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record032.data.requiredEdges q = true := by decide +kernel
theorem record032_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record032_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1) (record032.inverseMaps 1) record032_frame001_indices (Fin.ofNat record032.n i)) 64 107 :=
  interval_of_check _ 64 43 (by decide +kernel)
theorem record032_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record032) (record032.maps 1)
      (record032.inverseMaps 1) record032_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 107 record032_frame001_links_0000 record032_frame001_links_0064)
theorem record032_frame001_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) : Supported record032 1 :=
  of_group record032 1 (embedding record032) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record032_frame001_indices record032_frame001_graph record032_frame001_links
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
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x50aa8273d69d14d765ab28b92547223750e385741f20d8e286b93365970ca464eb2298f8bd3598ab1d564aac54da70132c97649a247120c8e3461a2050d2853425a11906c8303a21a68cc264a31e9718b4058c2b8950ca2850b27c139096c48723f11ac8ce46022b11486fc36317d8bb458425a12608cc45621c10a87b034417e0b40554286139098845c20c0fc07a03681a4078037019c0bc05b02c815808404001c00d804a02301000780260120070034012008002000c002000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x95b92290c9048ff8f48e38db8da89d89688187a80e80c7e77d47ce7cb7b17a376d7406cf67866d66863361a5e45c55c45b858156352f51e51250c4e84cb4ae48e48342841d4183cb3a738e3753743683112f72d92ce2c22bc29825e2522352331fe1ef1e81cd1be1b71ac1a81a419f19618a18316a16515814714213513211e1131070fd0f70ed0e30dd0da0d40c10bd0b60a60a409c09b07006e06706005f03403202f02402301a00c00b009006004003 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
theorem record037_frames_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    ∀ f : Fin record037.g, Supported record037 f :=
  (Fin.cases (record037_frame000_supported hcells) (Fin.cases (record037_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record037_frames_supported
theorem record038_frame000_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    Supported record038 0 :=
  of_identity record038 0 (by decide +kernel)
theorem record038_frames_supported (hcells : ∀ c, record038.data.cells c = FacetUniverses.FullSix0.cells (embedding record038 c)) :
    ∀ f : Fin record038.g, Supported record038 f :=
  (Fin.cases (record038_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record040_frame001_indices (c : Fin record040.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1098.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1098.count (({ width := 11, code := 0x37fefcdf3aff5aeb0d55a7f4ce97c5d8570a613c251922d45589f12621c3c86b0b61241f82b042054047fcfddf83e87bed69aa34a68ace59932959ab255f2bb552a89472834ec9c52f25448c750e49bc36e690cd18c2f45d8b59682ac53c8d1152124087a8ee1c6364690ce1903145d8b41602a8470860da1942f05607e0d81382504808c110120160280480800a01001802 } : Fields).get c.val)
theorem record040_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.graphBitCheck record040.data.requiredEdges q = true := by decide +kernel
theorem record040_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record040_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record040) (record040.maps 1) (record040.inverseMaps 1) record040_frame001_indices (Fin.ofNat record040.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record040_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1098.localPairCheck (embedding (N := 44310) record040) (record040.maps 1)
      (record040.inverseMaps 1) record040_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record040_frame001_links_0000 record040_frame001_links_0064)
theorem record040_frame001_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) : Supported record040 1 :=
  of_group record040 1 (embedding record040) hcells Papers.RationalityTen.SharedFrameCatalogue.group1098
    Papers.RationalityTen.SharedFrameCatalogue.group1098_facts record040_frame001_indices record040_frame001_graph record040_frame001_links
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (Fin.cases (record040_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
def record041_frame001_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5546a775299d5ce4e6fd33598d4c1160eaee563aacd518a7b530a66d30495b4a3a48121e8f5474a3851a68cc45f22dd15c6c73579a98d2868433a9988c9e63c31195c8ab455129f94bca4050d27d139c99c4c825f92e89664ad253127c9304912440d9c6ae32c18c8bc05b42a614c89e84d624c11e087c4181fe0f807883861b60cb86202d215909e04a423610d07f83e01e00e9071036c0f006e02f812008003e01b00bc04e012008003c01c00d00580280120080028010006002 } : Fields).get c.val)
theorem record041_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1) (record041.inverseMaps 1) record041_frame001_indices (Fin.ofNat record041.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record041_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record041) (record041.maps 1)
      (record041.inverseMaps 1) record041_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record041_frame001_links_0000 record041_frame001_links_0064)
theorem record041_frame001_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 1 :=
  of_group record041 1 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record041_frame001_indices record041_frame001_graph record041_frame001_links
def record041_frame002_indices (c : Fin record041.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1091.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1091.count (({ width := 10, code := 0x2b2ac6b0aa2a6a92a2a829e8fa3a8d2308a6258820d826037fdf87d1ef7a9e6781dc755d1731a6689a06759a65d926418d621765c9705b56a59d625815d561555454f53149519414fd3c4dd1f4711243504400f33c0e6384d8350cb318c3300bb2ccb0298a12609422c8620c801ec771c86f1b067154511203b0d4340b828088120400f0380d02c0a024080140400c02 } : Fields).get c.val)
theorem record041_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.graphBitCheck record041.data.requiredEdges q = true := by decide +kernel
theorem record041_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record041_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record041) (record041.maps 2) (record041.inverseMaps 2) record041_frame002_indices (Fin.ofNat record041.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record041_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1091.localPairCheck (embedding (N := 44310) record041) (record041.maps 2)
      (record041.inverseMaps 2) record041_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record041_frame002_links_0000 record041_frame002_links_0064)
theorem record041_frame002_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) : Supported record041 2 :=
  of_group record041 2 (embedding record041) hcells Papers.RationalityTen.SharedFrameCatalogue.group1091
    Papers.RationalityTen.SharedFrameCatalogue.group1091_facts record041_frame002_indices record041_frame002_graph record041_frame002_links
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (Fin.cases (record041_frame001_supported hcells) (Fin.cases (record041_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xcdfe05aecf6b8ab2d46daf2d49698b4099d4cc155d2a8d4f4a6551f28a941094c4952491224900476a36918e8b3449219d08a8334081ff8fc87d13e09ebcf3c5862b79518a6250a27b13508303f61f80f787983b91d30e4c6fe35e1998c445fe2dc1650ac053a28d13d89a83821bb0d686983301910b0054829614409e84d825e128077039c1c00d9057828c13606e033817c06c02f013806802400b00500240100060028010006002 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
def record044_frame001_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0xb4f5a429a94c3a1ed08a82f3fc6663299920c69629b0dd4cea41515a8113dc9d24c2a5e92ee9704b4a5892b69544a6a509272931491a47121c90747e23d11da8e646f95e8ab45552a194c4a3c50b27d139c9924ab24d11dc8ce4432190c2c5d62e616a0b0855e29c14589e04b423c11588203f01d40e1855c29c1490a104ec26812d093047c22c113086841c2000f907803a01c40dc06b028c13609104001e00dc036017809c04001f00f00740340120058028012008 } : Fields).get c.val)
theorem record044_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record044) (record044.maps 1) (record044.inverseMaps 1) record044_frame001_indices (Fin.ofNat record044.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record044_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record044) (record044.maps 1)
      (record044.inverseMaps 1) record044_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record044_frame001_links_0000 record044_frame001_links_0064)
theorem record044_frame001_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 1 :=
  of_group record044 1 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record044_frame001_indices record044_frame001_graph record044_frame001_links
def record044_frame002_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x9534a4221d0fa84dc21e0d50595dfae8171ab6c5acad35442a024f8a7493829b349ba43d2108f347123391788ab44ba2090d284f413a058fe67e23e79ee0f427893bb9504a3e51828393e49d84dc267130496049224091908ae43c2178d5866432918c8c285f62ec16e8b3857a29c14509b44c024711d07643821b80d506783241870bd85bc2c61610a704e825011c08603d81cc0db068828c13609104001e00dc036017809c04001f00f00740340120058028012008 } : Fields).get c.val)
theorem record044_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record044) (record044.maps 2) (record044.inverseMaps 2) record044_frame002_indices (Fin.ofNat record044.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record044_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record044) (record044.maps 2)
      (record044.inverseMaps 2) record044_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record044_frame002_links_0000 record044_frame002_links_0064)
theorem record044_frame002_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 2 :=
  of_group record044 2 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record044_frame002_indices record044_frame002_graph record044_frame002_links
def record044_frame003_indices (c : Fin record044.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x82481c7a279b77776c76375f5a759a59558457e5754f24e34dd4ce4c94c048747c47947246a46345a45244b44143943142441e41040a4013f93f23eb3e42e82d42d32cb2c42bd2b42ab2a229528827e27126c25e2571e31cf1ce1c51bc1b31aa1a319c19018317916816115615111d11511110a1050ff0f90f40ee0e70e60e00db0d50d00c90c20bc0b80b509709008707b07406b03602f02702001f01e01d01a01200b00a009008 } : Fields).get c.val)
theorem record044_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record044.data.requiredEdges q = true := by decide +kernel
theorem record044_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record044_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record044) (record044.maps 3) (record044.inverseMaps 3) record044_frame003_indices (Fin.ofNat record044.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record044_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record044) (record044.maps 3)
      (record044.inverseMaps 3) record044_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record044_frame003_links_0000 record044_frame003_links_0064)
theorem record044_frame003_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) : Supported record044 3 :=
  of_group record044 3 (embedding record044) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record044_frame003_indices record044_frame003_graph record044_frame003_links
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (Fin.cases (record044_frame001_supported hcells) (Fin.cases (record044_frame002_supported hcells) (Fin.cases (record044_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record044_frames_supported
theorem record045_frame000_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    Supported record045 0 :=
  of_identity record045 0 (by decide +kernel)
def record045_frame001_indices (c : Fin record045.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1015.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1015.count (({ width := 10, code := 0x8fa398ce2f8aa2889222755cf71dbf6ddaa6859e64d8e61d825e1735b16757d5c52d424e9314a51f44d0e421013fcf83c8eb3a4e2378d9350ce318c42fcb92d4b02b0a72849d260942348b18860148501244410c400f0390c42a094200641202c0400c0200400 } : Fields).get c.val)
theorem record045_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.graphBitCheck record045.data.requiredEdges q = true := by decide +kernel
theorem record045_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record045_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record045) (record045.maps 1) (record045.inverseMaps 1) record045_frame001_indices (Fin.ofNat record045.n i)) 64 82 :=
  interval_of_check _ 64 18 (by decide +kernel)
theorem record045_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1015.localPairCheck (embedding (N := 44310) record045) (record045.maps 1)
      (record045.inverseMaps 1) record045_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 82 record045_frame001_links_0000 record045_frame001_links_0064)
theorem record045_frame001_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) : Supported record045 1 :=
  of_group record045 1 (embedding record045) hcells Papers.RationalityTen.SharedFrameCatalogue.group1015
    Papers.RationalityTen.SharedFrameCatalogue.group1015_facts record045_frame001_indices record045_frame001_graph record045_frame001_links
theorem record045_frames_supported (hcells : ∀ c, record045.data.cells c = FacetUniverses.FullSix0.cells (embedding record045 c)) :
    ∀ f : Fin record045.g, Supported record045 f :=
  (Fin.cases (record045_frame000_supported hcells) (Fin.cases (record045_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record048_frames_supported
theorem record049_frame000_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    Supported record049 0 :=
  of_identity record049 0 (by decide +kernel)
theorem record049_frames_supported (hcells : ∀ c, record049.data.cells c = FacetUniverses.FullSix0.cells (embedding record049 c)) :
    ∀ f : Fin record049.g, Supported record049 f :=
  (Fin.cases (record049_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record056_frames_supported (hcells : ∀ c, record056.data.cells c = FacetUniverses.FullSix0.cells (embedding record056 c)) :
    ∀ f : Fin record056.g, Supported record056 f :=
  (Fin.cases (record056_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x277d38a8fac78e13efb17d2bc5ddb4ed37573a79ce6e63727b8fdc62e2a6e0349d944c9e648afed778b5958d2b09566aa9528a6212d49574a3a4711aa8b745222510d284d422a0e10607e33d29dc8eba7493999becd906b334f9a24cd266232a1934c7e54c29a14b4a164bf25392808fc46722b11488163ba1a98cd86402f91768ac852a27f12c093045821d10a86782d0131091045c1e80e506d034814209704281e80e002b011807802600d0040010002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
theorem record058_frames_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    ∀ f : Fin record058.g, Supported record058 f :=
  (Fin.cases (record058_frame000_supported hcells) (Fin.cases (record058_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record058_frames_supported
theorem record059_frame000_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    Supported record059 0 :=
  of_identity record059 0 (by decide +kernel)
theorem record059_frames_supported (hcells : ∀ c, record059.data.cells c = FacetUniverses.FullSix0.cells (embedding record059 c)) :
    ∀ f : Fin record059.g, Supported record059 f :=
  (Fin.cases (record059_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record059_frames_supported
theorem record060_frame000_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    Supported record060 0 :=
  of_identity record060 0 (by decide +kernel)
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x8137eb7ab77575475174e74b73973672672371f71c7167096f46eb6d86cc6bf6bc6ba6a768767b67566c65865565365265064c6456436346005f85cf5c85a355754052350f4d74a549447646646244e44a42f42341a40f4063e93e23ad3aa37b37435633f32d2c62be2ac27426925a24a23022b1bd1a519d16415914e14512c1231061000f50ef0dc0d20cd0bb0b90b60b109a09408a07e07606c06305a05404604303c03902301e00d008001000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
theorem record061_frames_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    ∀ f : Fin record061.g, Supported record061 f :=
  (Fin.cases (record061_frame000_supported hcells) (Fin.cases (record061_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record061_frames_supported
theorem record062_frame000_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    Supported record062 0 :=
  of_identity record062 0 (by decide +kernel)
theorem record062_frames_supported (hcells : ∀ c, record062.data.cells c = FacetUniverses.FullSix0.cells (embedding record062 c)) :
    ∀ f : Fin record062.g, Supported record062 f :=
  (Fin.cases (record062_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record062_frames_supported
theorem record063_frame000_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    Supported record063 0 :=
  of_identity record063 0 (by decide +kernel)
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2c91630a27d0d27732d896bcb465a1283935c73a36b0c6856be49f04f6d7b2395dc28d38665b30191cc7e6342fc975ead3533296d452a19501a6c933a9954c725e52ca9634ab24c923c90f481a3cd1d68e546e9af0cfe5ae2cf162ca7452528393e491446c22910b081e3e01e88cfc65e31c1658ad853028a10d87f43c61bd0d005c42c413c09a849c24011808603f01ee0e506f03581a00ab054028012408804281f40de04601c80d404601d00e0038010007 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (embedding record064) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x24331ab8c045c61e307e823c06dcc2e49709b7f1b92db26bfb5dda9ad45592a88129c9464a023c11ba8b945320d90228023ee9eece8a73f39b9c5cde069933a1870aa654f2a514009ec4d526591bc8b24472188db86ce3611910c586082e916b8a244f425e12a08e0442212100869433618f0c105e02d81640aa050c24811808303a81c00d6048022010a054028013406a02d015009804201c00c805c02c01400980400140070018008002000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record069_frame001_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xae2ae1ae0adda87a7da73a7097996a91090e8e88e68cb8aa87e84b82e8147f47ce7bd7b17957797527327086f76e66a86936746146035f25ea5d55aa5a859358c57757054551b4f24ce4a749448643c42740539f38c37e37335e33433231e3173032fc2ab2531ea1b21ac1761540f90f30e00c60c20b70b60af0a109709507a05704201f01901401000d00a008004001000 } : Fields).get c.val)
theorem record069_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record069) (record069.maps 1) (record069.inverseMaps 1) record069_frame001_indices (Fin.ofNat record069.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record069_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record069) (record069.maps 1)
      (record069.inverseMaps 1) record069_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record069_frame001_links_0000 record069_frame001_links_0064)
theorem record069_frame001_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) : Supported record069 1 :=
  of_group record069 1 (embedding record069) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record069_frame001_indices record069_frame001_graph record069_frame001_links
def record069_frame002_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0832.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0832.count (({ width := 9, code := 0x1ecf5fabd1dfef777b7c7e36f377b2d8ec35dabd4e9b4ba2cfe773798cae371383c0dfeed71b657ebb5bacd529347a1cfe77379a4c249208cc56250680bf1d8e872b89bacf673258cc15eacd509746a2cf87731984b855299409e4e2612490431b0b83a170a0401a0a040100200 } : Fields).get c.val)
theorem record069_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record069) (record069.maps 2) (record069.inverseMaps 2) record069_frame002_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record069) (record069.maps 2) (record069.inverseMaps 2) record069_frame002_indices (Fin.ofNat record069.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record069_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0832.localPairCheck (embedding (N := 44310) record069) (record069.maps 2)
      (record069.inverseMaps 2) record069_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record069_frame002_links_0000 record069_frame002_links_0064)
theorem record069_frame002_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) : Supported record069 2 :=
  of_group record069 2 (embedding record069) hcells Papers.RationalityTen.SharedFrameCatalogue.group0832
    Papers.RationalityTen.SharedFrameCatalogue.group0832_facts record069_frame002_indices record069_frame002_graph record069_frame002_links
def record069_frame003_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0828.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0828.count (({ width := 9, code := 0x10b854260efe7ebf1f4e672b6db4d16833d9acb64b1d8cc46130580be5e2e16cb3592c560ae55aa14ea652a8d3c9d4da652e9549a41148842209007d3d9e0e671379b4d66532188c05e2e164aa4e2411c82401b0d4662f170b0562a1489c4c240e85c1c0c058240e060200c0200 } : Fields).get c.val)
theorem record069_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0828.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record069) (record069.maps 3) (record069.inverseMaps 3) record069_frame003_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record069) (record069.maps 3) (record069.inverseMaps 3) record069_frame003_indices (Fin.ofNat record069.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record069_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0828.localPairCheck (embedding (N := 44310) record069) (record069.maps 3)
      (record069.inverseMaps 3) record069_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record069_frame003_links_0000 record069_frame003_links_0064)
theorem record069_frame003_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) : Supported record069 3 :=
  of_group record069 3 (embedding record069) hcells Papers.RationalityTen.SharedFrameCatalogue.group0828
    Papers.RationalityTen.SharedFrameCatalogue.group0828_facts record069_frame003_indices record069_frame003_graph record069_frame003_links
def record069_frame004_indices (c : Fin record069.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x19b4cd9e6c735f80bbee5e4af033b99bec87e4330e786dc1da07efb6787bac1ca4ddc6a9b4799aec73614aeb16b6b1657b2b7d4aca194e8a4812028eb46e22890528263f81f74f5879739f9bd4cf06272f11708b5652227292747d83cd1db8ea06dc2f51790af055227813188a43fe1ba0cb86442ca15108904301fa0da06a83141880bb050825c12a07a02b810803e01900a004001a00a0040010002000 } : Fields).get c.val)
theorem record069_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record069.data.requiredEdges q = true := by decide +kernel
theorem record069_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record069) (record069.maps 4) (record069.inverseMaps 4) record069_frame004_indices (Fin.ofNat record069.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record069_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record069) (record069.maps 4) (record069.inverseMaps 4) record069_frame004_indices (Fin.ofNat record069.n i)) 64 97 :=
  interval_of_check _ 64 33 (by decide +kernel)
theorem record069_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record069) (record069.maps 4)
      (record069.inverseMaps 4) record069_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 97 record069_frame004_links_0000 record069_frame004_links_0064)
theorem record069_frame004_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) : Supported record069 4 :=
  of_group record069 4 (embedding record069) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record069_frame004_indices record069_frame004_graph record069_frame004_links
theorem record069_frames_supported (hcells : ∀ c, record069.data.cells c = FacetUniverses.FullSix0.cells (embedding record069 c)) :
    ∀ f : Fin record069.g, Supported record069 f :=
  (Fin.cases (record069_frame000_supported hcells) (Fin.cases (record069_frame001_supported hcells) (Fin.cases (record069_frame002_supported hcells) (Fin.cases (record069_frame003_supported hcells) (Fin.cases (record069_frame004_supported hcells) (fun j => Fin.elim0 j))))))
#print axioms record069_frames_supported
theorem record070_frame000_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    Supported record070 0 :=
  of_identity record070 0 (by decide +kernel)
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
def record071_frame001_indices (c : Fin record071.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1080.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1080.count (({ width := 12, code := 0x95295094e94d8d78c286d86b86a8697a17a07957717476a766a62b6266115ca5bd57c57756451e5114c64ba47f43841a39f39a38537a36d2f22ed2da2ce2c124d24122f1eb1ba1ac1a419017b16e15c14b1391321221111070fa0ed0e00da0ba0b30ad0ac0a709e09409008c08808305705505004501f01c01901701600a004000 } : Fields).get c.val)
theorem record071_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.graphBitCheck record071.data.requiredEdges q = true := by decide +kernel
theorem record071_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record071_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record071) (record071.maps 1) (record071.inverseMaps 1) record071_frame001_indices (Fin.ofNat record071.n i)) 64 86 :=
  interval_of_check _ 64 22 (by decide +kernel)
theorem record071_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1080.localPairCheck (embedding (N := 44310) record071) (record071.maps 1)
      (record071.inverseMaps 1) record071_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 86 record071_frame001_links_0000 record071_frame001_links_0064)
theorem record071_frame001_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) : Supported record071 1 :=
  of_group record071 1 (embedding record071) hcells Papers.RationalityTen.SharedFrameCatalogue.group1080
    Papers.RationalityTen.SharedFrameCatalogue.group1080_facts record071_frame001_indices record071_frame001_graph record071_frame001_links
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
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record074_frames_supported
theorem record075_frame000_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    Supported record075 0 :=
  of_identity record075 0 (by decide +kernel)
theorem record075_frames_supported (hcells : ∀ c, record075.data.cells c = FacetUniverses.FullSix0.cells (embedding record075 c)) :
    ∀ f : Fin record075.g, Supported record075 f :=
  (Fin.cases (record075_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record075_frames_supported
theorem record076_frame000_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    Supported record076 0 :=
  of_identity record076 0 (by decide +kernel)
theorem record076_frames_supported (hcells : ∀ c, record076.data.cells c = FacetUniverses.FullSix0.cells (embedding record076 c)) :
    ∀ f : Fin record076.g, Supported record076 f :=
  (Fin.cases (record076_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record076_frames_supported
theorem record077_frame000_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    Supported record077 0 :=
  of_identity record077 0 (by decide +kernel)
def record077_frame001_indices (c : Fin record077.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1894c3eda7ed1550fa85d41a9ff4c6a594bea5bf24d91a457628d1058764145f96f1f762343d8d0c195e8ac295d6a9e548a9d54a4a124c9a6192b4914471a36513886640ca028fa67b63ca9cd0dca69d2eb16dcad455d2a094789bc45f22910987c03af1d28da06642e516b0a7c50426111e88b843421810187d43d21d30df06c032a18c0be85dc2e01680aa0500262129091842420e0ff07903a81b00d204a024011008303e01c00b805502a014009604401c009003a01c } : Fields).get c.val)
theorem record077_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record077.data.requiredEdges q = true := by decide +kernel
theorem record077_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record077_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record077) (record077.maps 1) (record077.inverseMaps 1) record077_frame001_indices (Fin.ofNat record077.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record077_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record077) (record077.maps 1)
      (record077.inverseMaps 1) record077_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record077_frame001_links_0000 record077_frame001_links_0064)
theorem record077_frame001_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) : Supported record077 1 :=
  of_group record077 1 (embedding record077) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record077_frame001_indices record077_frame001_graph record077_frame001_links
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
theorem record079_frames_supported (hcells : ∀ c, record079.data.cells c = FacetUniverses.FullSix0.cells (embedding record079 c)) :
    ∀ f : Fin record079.g, Supported record079 f :=
  (Fin.cases (record079_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record081_frames_supported (hcells : ∀ c, record081.data.cells c = FacetUniverses.FullSix0.cells (embedding record081 c)) :
    ∀ f : Fin record081.g, Supported record081 f :=
  (Fin.cases (record081_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record086_frame001_indices (c : Fin record086.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0xa2fd12e7c73cc979cb724d32568abc011ff4fec7a23cede64f2478dba99bccd4668eb2fd8aab9a577ab15570a9f517260d2b294c499a3751428984461fece8870c3371984bde5b728c943096e49524811a88423ba1d60c5860429f13f09b44b424710e07f43e21e40de066c3141770b204e423410e08083b81d009804982380fc07003081600aa054023011006602400f807403801800a804401c0080038008002000 } : Fields).get c.val)
theorem record086_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record086.data.requiredEdges q = true := by decide +kernel
theorem record086_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record086_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record086) (record086.maps 1) (record086.inverseMaps 1) record086_frame001_indices (Fin.ofNat record086.n i)) 64 100 :=
  interval_of_check _ 64 36 (by decide +kernel)
theorem record086_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record086) (record086.maps 1)
      (record086.inverseMaps 1) record086_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 100 record086_frame001_links_0000 record086_frame001_links_0064)
theorem record086_frame001_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) : Supported record086 1 :=
  of_group record086 1 (embedding record086) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record086_frame001_indices record086_frame001_graph record086_frame001_links
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (Fin.cases (record086_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record089_frames_supported
theorem record090_frame000_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    Supported record090 0 :=
  of_identity record090 0 (by decide +kernel)
theorem record090_frames_supported (hcells : ∀ c, record090.data.cells c = FacetUniverses.FullSix0.cells (embedding record090 c)) :
    ∀ f : Fin record090.g, Supported record090 f :=
  (Fin.cases (record090_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record094_frame001_indices (c : Fin record094.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x312f880bf35e6eedb6b7b38599abd75d3ae0551ea5d524a2245d62d11078774365edaf1372435a59eec275ae2c6552ea3d4e825f12e092647fa3a518c86b423a0c903c8073e11ed0f2a6f33141794ac650924e11208783f21e58ed47243371898bf85d42d31470a004c224711107a834819e0c8859c27812108d042c20a0fe07b83a01c40b6049823c0d606503101540a803301680a803a01c00c005802a00f005002000e0060018008002000 } : Fields).get c.val)
theorem record094_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record094.data.requiredEdges q = true := by decide +kernel
theorem record094_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record094_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record094) (record094.maps 1) (record094.inverseMaps 1) record094_frame001_indices (Fin.ofNat record094.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record094_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record094) (record094.maps 1)
      (record094.inverseMaps 1) record094_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record094_frame001_links_0000 record094_frame001_links_0064)
theorem record094_frame001_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) : Supported record094 1 :=
  of_group record094 1 (embedding record094) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record094_frame001_indices record094_frame001_graph record094_frame001_links
theorem record094_frames_supported (hcells : ∀ c, record094.data.cells c = FacetUniverses.FullSix0.cells (embedding record094 c)) :
    ∀ f : Fin record094.g, Supported record094 f :=
  (Fin.cases (record094_frame000_supported hcells) (Fin.cases (record094_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record094_frames_supported
theorem record095_frame000_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    Supported record095 0 :=
  of_identity record095 0 (by decide +kernel)
theorem record095_frames_supported (hcells : ∀ c, record095.data.cells c = FacetUniverses.FullSix0.cells (embedding record095 c)) :
    ∀ f : Fin record095.g, Supported record095 f :=
  (Fin.cases (record095_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record095_frames_supported
theorem record096_frame000_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    Supported record096 0 :=
  of_identity record096 0 (by decide +kernel)
def record096_frame001_indices (c : Fin record096.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xd0a64db14581bbf35e6eedb6b7b38599abd75d3ae0551ea5d524a6ad32e76d3a49c5cd9a59127693245d62d11078774365922c1758b2a6947497c4b6a3f11d28c34192078f687953ae9b8cbc456628311208723c81da8e3c5fc2ea140098449c24711c88a444421b0f887a83b81ba0d2067832e1910bd859c28613c097048423411208584141fc0f7074038811007f03581940c405502a014008e03301680a803a01c00c806002e01600a805002000f005002000e0060018008002000 } : Fields).get c.val)
theorem record096_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record096.data.requiredEdges q = true := by decide +kernel
theorem record096_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record096_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record096) (record096.maps 1) (record096.inverseMaps 1) record096_frame001_indices (Fin.ofNat record096.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record096_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record096) (record096.maps 1)
      (record096.inverseMaps 1) record096_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record096_frame001_links_0000 record096_frame001_links_0064)
theorem record096_frame001_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) : Supported record096 1 :=
  of_group record096 1 (embedding record096) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record096_frame001_indices record096_frame001_graph record096_frame001_links
theorem record096_frames_supported (hcells : ∀ c, record096.data.cells c = FacetUniverses.FullSix0.cells (embedding record096 c)) :
    ∀ f : Fin record096.g, Supported record096 f :=
  (Fin.cases (record096_frame000_supported hcells) (Fin.cases (record096_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00070

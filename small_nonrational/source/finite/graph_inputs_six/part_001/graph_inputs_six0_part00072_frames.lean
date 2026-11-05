module
prelude
public import GraphInputsSix0Part00072Data
public import RawFrameSupport
public import SharedFrameGroups035Checked
public import SharedFrameGroups036Checked
public import SharedFrameGroups037Checked
public import SharedFrameGroups038Checked
public import SharedFrameGroups039Checked
public import SharedFrameGroups040Checked
public import SharedFrameGroups096Checked
public import SharedFrameGroups099Checked
public import SharedFrameGroups100Checked
public import SharedFrameGroups101Checked
public import SharedFrameGroups102Checked
public import SharedFrameGroups103Checked
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
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open SharedGraphFramePairs RawFrameSupport FiniteChecks
theorem record000_frame000_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) :
    Supported record000 0 :=
  of_identity record000 0 (by decide +kernel)
def record000_frame001_indices (c : Fin record000.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x3edf9deebd939df17dd3b6f41e54c2b7eed9d90b1b626c1d80afd4ee91d18a2b23a3fc7b89f0e607be179aeadd33946f6ddda633b664c49842fe5eabc56c2c257eac54ca95514a05362674ba9612924d4808f118a2c3ee7ccf01cc3826c0d59a12ec598af94126a4ac929141f83b0720dd19a2ec548a20da16c2a85409a1181c83706a0a41282303a0700b01301c0280400700600800800 } : Fields).get c.val)
theorem record000_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record000.data.requiredEdges q = true := by decide +kernel
theorem record000_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record000_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record000) (record000.maps 1) (record000.inverseMaps 1) record000_frame001_indices (Fin.ofNat record000.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record000_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record000) (record000.maps 1)
      (record000.inverseMaps 1) record000_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record000_frame001_links_0000 record000_frame001_links_0064)
theorem record000_frame001_supported (hcells : ∀ c, record000.data.cells c = FacetUniverses.FullSix0.cells (embedding record000 c)) : Supported record000 1 :=
  of_group record000 1 (embedding record000) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record000_frame001_indices record000_frame001_graph record000_frame001_links
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
def record003_frame001_indices (c : Fin record003.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x312987dbe05eb2cb745da24cfce7ad36f9b44aee4e7263926c8d24471768ab44fe23f0b8851c265aa8d0f5882a79522a52513260d2b6906472236515e85740ca028fa67a63ca9770ad455d28f13c889e4271e90ec074a37b1918b945ac29f139098447e21410007543721900be05d02da16709e04b824e12108583f81de0e2050825012008503e01c00b605502a0134088038011807403801900b005002600f007002c0100070018008002000 } : Fields).get c.val)
theorem record003_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record003.data.requiredEdges q = true := by decide +kernel
theorem record003_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record003_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1) (record003.inverseMaps 1) record003_frame001_indices (Fin.ofNat record003.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record003_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record003) (record003.maps 1)
      (record003.inverseMaps 1) record003_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record003_frame001_links_0000 record003_frame001_links_0064)
theorem record003_frame001_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) : Supported record003 1 :=
  of_group record003 1 (embedding record003) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record003_frame001_indices record003_frame001_graph record003_frame001_links
theorem record003_frames_supported (hcells : ∀ c, record003.data.cells c = FacetUniverses.FullSix0.cells (embedding record003 c)) :
    ∀ f : Fin record003.g, Supported record003 f :=
  (Fin.cases (record003_frame000_supported hcells) (Fin.cases (record003_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record008_frame001_indices (c : Fin record008.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2e055a7aca4ee6431098843c1da08af767b6bd91e04ed96a1330192ac7e62aab754b6a3050ca7c12188e246e227d0a881f3cd9d80e966e435e1a48cfe6542fc16f0b5c5882a814e8a2a507271926c914469229110885e40f1f70f807a23891a68cfc6322e11658a98530274116086c3f41e30e9870034017f0b8858827411708503d81d20dd030816c0aa054026811808803901b80d40660290118074038014007002000e0050018008002000 } : Fields).get c.val)
theorem record008_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record008.data.requiredEdges q = true := by decide +kernel
theorem record008_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record008_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1) (record008.inverseMaps 1) record008_frame001_indices (Fin.ofNat record008.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record008_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record008) (record008.maps 1)
      (record008.inverseMaps 1) record008_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record008_frame001_links_0000 record008_frame001_links_0064)
theorem record008_frame001_supported (hcells : ∀ c, record008.data.cells c = FacetUniverses.FullSix0.cells (embedding record008 c)) : Supported record008 1 :=
  of_group record008 1 (embedding record008) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record008_frame001_indices record008_frame001_graph record008_frame001_links
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
theorem record010_frames_supported (hcells : ∀ c, record010.data.cells c = FacetUniverses.FullSix0.cells (embedding record010 c)) :
    ∀ f : Fin record010.g, Supported record010 f :=
  (Fin.cases (record010_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record010_frames_supported
theorem record011_frame000_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) :
    Supported record011 0 :=
  of_identity record011 0 (by decide +kernel)
def record011_frame001_indices (c : Fin record011.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x665314b822be15ebab815a0ac2d5828872bb939c98e49b234911c84a1710a384cb7d9a48cdf586aa854cea4f514a66130095e484a3851ac8b243520d50147f53d89e98f2a5d92b694cca364f523211308543d51d68e886fc3361808b5858227d13909844722220f1867830417c0b6859c29413509704842320fe077838817809f04902380fc07002d81540a804601c008c03a01c00c0054028011007002c0100070018008002000 } : Fields).get c.val)
theorem record011_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record011.data.requiredEdges q = true := by decide +kernel
theorem record011_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record011_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1) (record011.inverseMaps 1) record011_frame001_indices (Fin.ofNat record011.n i)) 64 103 :=
  interval_of_check _ 64 39 (by decide +kernel)
theorem record011_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record011) (record011.maps 1)
      (record011.inverseMaps 1) record011_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 103 record011_frame001_links_0000 record011_frame001_links_0064)
theorem record011_frame001_supported (hcells : ∀ c, record011.data.cells c = FacetUniverses.FullSix0.cells (embedding record011 c)) : Supported record011 1 :=
  of_group record011 1 (embedding record011) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record011_frame001_indices record011_frame001_graph record011_frame001_links
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
def record019_frame001_indices (c : Fin record019.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x18e8c6d632716778abbcd3a293f4559dfcde66c92c395dc9c64d51958bec5ca2a313a897b789aacb07547291d46a9934c1a4812228ce45f213105e8193f49f4cf4e5d32ad144ca0245f2278fb07ba39a1c50c605f62e515a8a7c4e623f11487fc34a1970c505ec2dc15109704a024211208604141d20b204f025c12809004601e80d206302d01580aa05402100c405602200f007403801900b005002000d004802000e0040018008002000 } : Fields).get c.val)
theorem record019_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record019.data.requiredEdges q = true := by decide +kernel
theorem record019_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record019_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1) (record019.inverseMaps 1) record019_frame001_indices (Fin.ofNat record019.n i)) 64 105 :=
  interval_of_check _ 64 41 (by decide +kernel)
theorem record019_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record019) (record019.maps 1)
      (record019.inverseMaps 1) record019_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 105 record019_frame001_links_0000 record019_frame001_links_0064)
theorem record019_frame001_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) : Supported record019 1 :=
  of_group record019 1 (embedding record019) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record019_frame001_indices record019_frame001_graph record019_frame001_links
theorem record019_frames_supported (hcells : ∀ c, record019.data.cells c = FacetUniverses.FullSix0.cells (embedding record019 c)) :
    ∀ f : Fin record019.g, Supported record019 f :=
  (Fin.cases (record019_frame000_supported hcells) (Fin.cases (record019_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record019_frames_supported
theorem record020_frame000_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    Supported record020 0 :=
  of_identity record020 0 (by decide +kernel)
def record020_frame001_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc72635ae39709975cb423b11bf8cac5f5a54c365ef2d4d608a9e545a985494a374c9a60121c8e5468a2b50cc82f4051fa4f6c7a73811aa8c3e5d02b5155ca5a516281917c8983da1d88e746f233217d8b5856a282139892048423a117089c4122030fe87bc3c41e00ec06f836c1ae0d4068432a18b0c285f42ee16f0b2055029a13a09c04c425212208e042420c0fb07903a81be0d806902300f6070034818c0b805a02b01540a804301c00c4056024011007803a01c } : Fields).get c.val)
theorem record020_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1) (record020.inverseMaps 1) record020_frame001_indices (Fin.ofNat record020.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record020_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record020) (record020.maps 1)
      (record020.inverseMaps 1) record020_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record020_frame001_links_0000 record020_frame001_links_0064)
theorem record020_frame001_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 1 :=
  of_group record020 1 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record020_frame001_indices record020_frame001_graph record020_frame001_links
def record020_frame002_indices (c : Fin record020.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0551.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0551.count (({ width := 11, code := 0x9712de4c4958810f613424841079e53ab72ee25bcb636c0d6daab51670ccd8eb1761ec0d79ae85b4b355e2b7532a1539a624969212123c47086d0b2003f47ccf41d839c704da9a634463cc49822ea5bcab95229c5189e13a2664848e919228440818fc1f03cc770eb1ca3746c8cd1983145f0b816429c5309d13024c468871081c0330610b615c2804e0941242403c06c0bc158240440780e81c } : Fields).get c.val)
theorem record020_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.graphBitCheck record020.data.requiredEdges q = true := by decide +kernel
theorem record020_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record020_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record020) (record020.maps 2) (record020.inverseMaps 2) record020_frame002_indices (Fin.ofNat record020.n i)) 64 112 :=
  interval_of_check _ 64 48 (by decide +kernel)
theorem record020_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0551.localPairCheck (embedding (N := 44310) record020) (record020.maps 2)
      (record020.inverseMaps 2) record020_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 112 record020_frame002_links_0000 record020_frame002_links_0064)
theorem record020_frame002_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) : Supported record020 2 :=
  of_group record020 2 (embedding record020) hcells Papers.RationalityTen.SharedFrameCatalogue.group0551
    Papers.RationalityTen.SharedFrameCatalogue.group0551_facts record020_frame002_indices record020_frame002_graph record020_frame002_links
theorem record020_frames_supported (hcells : ∀ c, record020.data.cells c = FacetUniverses.FullSix0.cells (embedding record020 c)) :
    ∀ f : Fin record020.g, Supported record020 f :=
  (Fin.cases (record020_frame000_supported hcells) (Fin.cases (record020_frame001_supported hcells) (Fin.cases (record020_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record022_frame001_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x346da14ce0e6531ed88cc3ae042fcd600aa4d4c2a3d4e8a04492e4652288bac5a220f0ee86cc2e21470996982da162ca8a52da72530091f47221950a883240e2030f687a63ca98d0bc455629392548983eb1d80cc46402fe1740b60500272130891c47e23911488884001f90e106e83641a40cb864430616d0b3854029414409e04d424211308583f81ec0f007403880f807103581840b605502a0110072033014808c03a01c00c806002c01500a003c01c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record022_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 1) (record022.inverseMaps 1) record022_frame001_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record022) (record022.maps 1)
      (record022.inverseMaps 1) record022_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame001_links_0000 record022_frame001_links_0064)
theorem record022_frame001_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 1 :=
  of_group record022 1 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record022_frame001_indices record022_frame001_graph record022_frame001_links
def record022_frame002_indices (c : Fin record022.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0557.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0557.count (({ width := 11, code := 0x294d23a294367d4f99f13be76cbb9572aa524a29111822fc5b8a914e2544988f1162244380ef3ddeb9871eda9acb41658c0d802f95e4bad682cb58ea3d3da5849c8a50b1ff3d6710e09ba3666b4c998f3165fcbc9752d85a0a81492484748c9122144187e0e61c4350690d11943205d0ae14a2684a89111a224340600b6150278490900f01a02f05008c0e81c0320600b01502803c0700c0140200380500600800800 } : Fields).get c.val)
theorem record022_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.graphBitCheck record022.data.requiredEdges q = true := by decide +kernel
theorem record022_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record022_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record022) (record022.maps 2) (record022.inverseMaps 2) record022_frame002_indices (Fin.ofNat record022.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record022_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0557.localPairCheck (embedding (N := 44310) record022) (record022.maps 2)
      (record022.inverseMaps 2) record022_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record022_frame002_links_0000 record022_frame002_links_0064)
theorem record022_frame002_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) : Supported record022 2 :=
  of_group record022 2 (embedding record022) hcells Papers.RationalityTen.SharedFrameCatalogue.group0557
    Papers.RationalityTen.SharedFrameCatalogue.group0557_facts record022_frame002_indices record022_frame002_graph record022_frame002_links
theorem record022_frames_supported (hcells : ∀ c, record022.data.cells c = FacetUniverses.FullSix0.cells (embedding record022 c)) :
    ∀ f : Fin record022.g, Supported record022 f :=
  (Fin.cases (record022_frame000_supported hcells) (Fin.cases (record022_frame001_supported hcells) (Fin.cases (record022_frame002_supported hcells) (fun j => Fin.elim0 j))))
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
def record024_frame001_indices (c : Fin record024.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x134598f4bf25ab28d931457a24b11987042b2102f4f7a13c31dfeecb75c3a5dd08e3e6e1b4d1986c5a60e30356dcb6456829c1492a354da260929e91d48623fd1ee85e428a0790227e73929c54d4069631f98d4c0a5f92f99600aa452b27e93b89d44b6234117087242d20d0f4073e3891b60cfc65230c1830bdc5e02a8132096c47a22a110880c3f41c40ca05dc2d215f0a304e025c12604201f80e206d02c01540a804a02200b80500240100074038012007002c0100070028008002000 } : Fields).get c.val)
theorem record024_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record024.data.requiredEdges q = true := by decide +kernel
theorem record024_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record024_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record024) (record024.maps 1) (record024.inverseMaps 1) record024_frame001_indices (Fin.ofNat record024.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record024_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record024) (record024.maps 1)
      (record024.inverseMaps 1) record024_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record024_frame001_links_0000 record024_frame001_links_0064)
theorem record024_frame001_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) : Supported record024 1 :=
  of_group record024 1 (embedding record024) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record024_frame001_indices record024_frame001_graph record024_frame001_links
theorem record024_frames_supported (hcells : ∀ c, record024.data.cells c = FacetUniverses.FullSix0.cells (embedding record024 c)) :
    ∀ f : Fin record024.g, Supported record024 f :=
  (Fin.cases (record024_frame000_supported hcells) (Fin.cases (record024_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record026_frames_supported (hcells : ∀ c, record026.data.cells c = FacetUniverses.FullSix0.cells (embedding record026 c)) :
    ∀ f : Fin record026.g, Supported record026 f :=
  (Fin.cases (record026_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record028_frame001_indices (c : Fin record028.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0543.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0543.count (({ width := 11, code := 0xe11c037d6f8debb3f616aed23a2743684cf79871b62ec3986308dfebf37c6f6dabb1d5669a517a0938e50c658b110e13c0e80ef59d5b93708dc1aa32a644c25822e55beb45622b6558a654b2824e09b52ca2b43683d041f93cc740e29b835068ccd98b3085a4a894a26e460899041fc3c8760e01b4334630c217a2e0590830d414c2904a09211c220390680a8140240420740e0120200380580800e00800800 } : Fields).get c.val)
theorem record028_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.graphBitCheck record028.data.requiredEdges q = true := by decide +kernel
theorem record028_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record028_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record028) (record028.maps 1) (record028.inverseMaps 1) record028_frame001_indices (Fin.ofNat record028.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record028_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0543.localPairCheck (embedding (N := 44310) record028) (record028.maps 1)
      (record028.inverseMaps 1) record028_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record028_frame001_links_0000 record028_frame001_links_0064)
theorem record028_frame001_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) : Supported record028 1 :=
  of_group record028 1 (embedding record028) hcells Papers.RationalityTen.SharedFrameCatalogue.group0543
    Papers.RationalityTen.SharedFrameCatalogue.group0543_facts record028_frame001_indices record028_frame001_graph record028_frame001_links
theorem record028_frames_supported (hcells : ∀ c, record028.data.cells c = FacetUniverses.FullSix0.cells (embedding record028 c)) :
    ∀ f : Fin record028.g, Supported record028 f :=
  (Fin.cases (record028_frame000_supported hcells) (Fin.cases (record028_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record032_frames_supported (hcells : ∀ c, record032.data.cells c = FacetUniverses.FullSix0.cells (embedding record032 c)) :
    ∀ f : Fin record032.g, Supported record032 f :=
  (Fin.cases (record032_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record032_frames_supported
theorem record033_frame000_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    Supported record033 0 :=
  of_identity record033 0 (by decide +kernel)
def record033_frame001_indices (c : Fin record033.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x4b424c52228fa46d21eb08281c3d81df2e39711b809bdedd96dc2fe1786b8c5ac29994229e14a6a50520c8ee465a2dd1287d23d41dfceda73f3859b90d1466532f9950c2c60d2f71780b825542a4943ca084e526c92e8906456217109880c3f61f48f747403781b68d886a03201898be05cc2cb13b89b44a2247118888c3e81e70db069c31a1840b505902ac14309704902300fa03601580aa05402380d0056028012007803a01c00c005402201000580240100070018008002000 } : Fields).get c.val)
theorem record033_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record033.data.requiredEdges q = true := by decide +kernel
theorem record033_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record033_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1) (record033.inverseMaps 1) record033_frame001_indices (Fin.ofNat record033.n i)) 64 115 :=
  interval_of_check _ 64 51 (by decide +kernel)
theorem record033_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record033) (record033.maps 1)
      (record033.inverseMaps 1) record033_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 115 record033_frame001_links_0000 record033_frame001_links_0064)
theorem record033_frame001_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) : Supported record033 1 :=
  of_group record033 1 (embedding record033) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record033_frame001_indices record033_frame001_graph record033_frame001_links
theorem record033_frames_supported (hcells : ∀ c, record033.data.cells c = FacetUniverses.FullSix0.cells (embedding record033 c)) :
    ∀ f : Fin record033.g, Supported record033 f :=
  (Fin.cases (record033_frame000_supported hcells) (Fin.cases (record033_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record035_frame001_indices (c : Fin record035.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc2860e6f777a7b745b2ecb745da054a8a50726392648ce4451e38e546d633b1858bb455227b13188343b61c50b8851c265ebed54687b07562aa91529260d2ae92048323991b286642ba064ff47d33e29e98f2a6e92f09574a3c44f2118fb07a43b21d28cc86462e51630a7c52227213088fc4542140ff87cc3d61b90cc06402da1670a8848422410c07f03bc1d20e2050825012006c03181800b605502a00d0056028011807403801900b004c02000e005802000e0040018008002000 } : Fields).get c.val)
theorem record035_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record035.data.requiredEdges q = true := by decide +kernel
theorem record035_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record035_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 1) (record035.inverseMaps 1) record035_frame001_indices (Fin.ofNat record035.n i)) 64 116 :=
  interval_of_check _ 64 52 (by decide +kernel)
theorem record035_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record035) (record035.maps 1)
      (record035.inverseMaps 1) record035_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 116 record035_frame001_links_0000 record035_frame001_links_0064)
theorem record035_frame001_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) : Supported record035 1 :=
  of_group record035 1 (embedding record035) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record035_frame001_indices record035_frame001_graph record035_frame001_links
theorem record035_frames_supported (hcells : ∀ c, record035.data.cells c = FacetUniverses.FullSix0.cells (embedding record035 c)) :
    ∀ f : Fin record035.g, Supported record035 f :=
  (Fin.cases (record035_frame000_supported hcells) (Fin.cases (record035_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record035_frames_supported
theorem record036_frame000_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    Supported record036 0 :=
  of_identity record036 0 (by decide +kernel)
def record036_frame001_indices (c : Fin record036.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x92a90e8fe8da8ab89f86a85e83d7e47d678b78878077c77977176a76776576376075e75a75675474e74a74874374173f6806716185c659f59053b51d4fe4c649147e47146c44c4193bf3a839738933d33231b3113052ff2d72d02ba2ae2a429f29729426924523e23020a2011fc1f21eb1b21ad19418f1851781661621441010f00e70dc0ca0c10ba06a06105e05905305204403903503402b02802301d01c01901601301000e00b008007004003002001000 } : Fields).get c.val)
theorem record036_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record036.data.requiredEdges q = true := by decide +kernel
theorem record036_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record036_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record036) (record036.maps 1) (record036.inverseMaps 1) record036_frame001_indices (Fin.ofNat record036.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record036_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record036) (record036.maps 1)
      (record036.inverseMaps 1) record036_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record036_frame001_links_0000 record036_frame001_links_0064)
theorem record036_frame001_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) : Supported record036 1 :=
  of_group record036 1 (embedding record036) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record036_frame001_indices record036_frame001_graph record036_frame001_links
theorem record036_frames_supported (hcells : ∀ c, record036.data.cells c = FacetUniverses.FullSix0.cells (embedding record036 c)) :
    ∀ f : Fin record036.g, Supported record036 f :=
  (Fin.cases (record036_frame000_supported hcells) (Fin.cases (record036_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record036_frames_supported
theorem record037_frame000_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) :
    Supported record037 0 :=
  of_identity record037 0 (by decide +kernel)
def record037_frame001_indices (c : Fin record037.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x32b193ec2660d6ddd6d1b2dd02a495231913c6d62110ef86d42e21470996aa343d83aa9f548a9814a49c94c9260d2b690647d23650ca8574192064ff07d33e39e98f2a6e92b59574a5851e24a917889e4271e90f1874a3311918bf85ca2c414f8a4c4e426111f88a84281ff0f987ac3741a40bd85d42da1670a8051027812f09384841fc0f0074038814209404801bc0ba05b02a815006e025011807403801900b004c02000e005002000e0050018008002000 } : Fields).get c.val)
theorem record037_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record037.data.requiredEdges q = true := by decide +kernel
theorem record037_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record037_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1) (record037.inverseMaps 1) record037_frame001_indices (Fin.ofNat record037.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record037_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record037) (record037.maps 1)
      (record037.inverseMaps 1) record037_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record037_frame001_links_0000 record037_frame001_links_0064)
theorem record037_frame001_supported (hcells : ∀ c, record037.data.cells c = FacetUniverses.FullSix0.cells (embedding record037 c)) : Supported record037 1 :=
  of_group record037 1 (embedding record037) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record037_frame001_indices record037_frame001_graph record037_frame001_links
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
theorem record040_frames_supported (hcells : ∀ c, record040.data.cells c = FacetUniverses.FullSix0.cells (embedding record040 c)) :
    ∀ f : Fin record040.g, Supported record040 f :=
  (Fin.cases (record040_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record040_frames_supported
theorem record041_frame000_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    Supported record041 0 :=
  of_identity record041 0 (by decide +kernel)
theorem record041_frames_supported (hcells : ∀ c, record041.data.cells c = FacetUniverses.FullSix0.cells (embedding record041 c)) :
    ∀ f : Fin record041.g, Supported record041 f :=
  (Fin.cases (record041_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record043_frame001_indices (c : Fin record043.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2beb5b4ac6d626ac1513a7b4dfa67332298a4a521af0c18544115eecf6d7b234fd99ac9563e31555b4a68518285d3e09974ac244d21a8f7478a3891b874d3691a48ca85f82e096c4b1055029b9454a144e324b11a488642f2010fb87c03d11c48d486843191708b2054c29b13a089c3f41d40e0064c2fe1710b104fc27412a092845c21c10a07b037414207e03281880bc05b02c01540a804401e80dc066023010007403800e005802000e0050018008002000 } : Fields).get c.val)
theorem record043_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record043.data.requiredEdges q = true := by decide +kernel
theorem record043_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record043_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1) (record043.inverseMaps 1) record043_frame001_indices (Fin.ofNat record043.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record043_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record043) (record043.maps 1)
      (record043.inverseMaps 1) record043_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record043_frame001_links_0000 record043_frame001_links_0064)
theorem record043_frame001_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) : Supported record043 1 :=
  of_group record043 1 (embedding record043) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record043_frame001_indices record043_frame001_graph record043_frame001_links
theorem record043_frames_supported (hcells : ∀ c, record043.data.cells c = FacetUniverses.FullSix0.cells (embedding record043 c)) :
    ∀ f : Fin record043.g, Supported record043 f :=
  (Fin.cases (record043_frame000_supported hcells) (Fin.cases (record043_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record043_frames_supported
theorem record044_frame000_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    Supported record044 0 :=
  of_identity record044 0 (by decide +kernel)
theorem record044_frames_supported (hcells : ∀ c, record044.data.cells c = FacetUniverses.FullSix0.cells (embedding record044 c)) :
    ∀ f : Fin record044.g, Supported record044 f :=
  (Fin.cases (record044_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record047_frame001_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x4de66af32e985cb965852188e645f5964c4960dac4d5c6ab6541a9594789e24d8a68d2fa94c49f246121a8fe44521450628113f89f9cf467573981b40d4069133818fcc6060f30217e4b585822b81560a5a51b28193e09de4a424991cc8d045122210e484441a1e70e7472036d19e8cc061a30517b0adc51a27812d893047c22110908103f41c60da06903221800bb85ac2c014f0a304e825e12602c01580aa05401680a804c02000f007403801900b004c01e00b004802000e0050018008002000 } : Fields).get c.val)
theorem record047_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record047) (record047.maps 1) (record047.inverseMaps 1) record047_frame001_indices (Fin.ofNat record047.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record047_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record047) (record047.maps 1)
      (record047.inverseMaps 1) record047_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record047_frame001_links_0000 record047_frame001_links_0064)
theorem record047_frame001_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 1 :=
  of_group record047 1 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record047_frame001_indices record047_frame001_graph record047_frame001_links
def record047_frame002_indices (c : Fin record047.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x13065e4b89672be5549d92b2360fc0a7faee1d439f71ce15bdb666acd51a633a670cc196324618bd172ad7590b0d5729c5229c52e25a4a88f51da354628ad099fe3f07ccef9d93a873ce51b8362684cd18c30e600b916f2bc534a41422684bc94927242454871081fc3e0798ec1cc3846f8d019832c628bf17c2e05a0b015e2a4528a30981282484805a0a81302003c0740e01902c04c0780b0120200380500600800800 } : Fields).get c.val)
theorem record047_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record047.data.requiredEdges q = true := by decide +kernel
theorem record047_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record047_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record047) (record047.maps 2) (record047.inverseMaps 2) record047_frame002_indices (Fin.ofNat record047.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record047_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record047) (record047.maps 2)
      (record047.inverseMaps 2) record047_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record047_frame002_links_0000 record047_frame002_links_0064)
theorem record047_frame002_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) : Supported record047 2 :=
  of_group record047 2 (embedding record047) hcells Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record047_frame002_indices record047_frame002_graph record047_frame002_links
theorem record047_frames_supported (hcells : ∀ c, record047.data.cells c = FacetUniverses.FullSix0.cells (embedding record047 c)) :
    ∀ f : Fin record047.g, Supported record047 f :=
  (Fin.cases (record047_frame000_supported hcells) (Fin.cases (record047_frame001_supported hcells) (Fin.cases (record047_frame002_supported hcells) (fun j => Fin.elim0 j))))
#print axioms record047_frames_supported
theorem record048_frame000_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    Supported record048 0 :=
  of_identity record048 0 (by decide +kernel)
def record048_frame001_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x131297ecb164452118da468e2f916c5972bed5b6a8b535a9994b6a1f508a7c13c29c04bd255129a94048023b91928b74492080fd87d23d59dfceda73f3859b90d1466532f9950c3660d2f71780b825812ae1550a9451328213a49b24be23210f084c4091f48f7475639e1c18dd86da36119d0c8c6262f51730b20510277136897c4a224711c88c444621310007d03ce1b30d3867031e1840bc85b02c81560a204c024811802c01580aa054010007803a01c00c806002c015009804401e00b004802000e0050018008002000 } : Fields).get c.val)
theorem record048_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record048) (record048.maps 1) (record048.inverseMaps 1) record048_frame001_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record048) (record048.maps 1)
      (record048.inverseMaps 1) record048_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame001_links_0000 record048_frame001_links_0064)
theorem record048_frame001_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 1 :=
  of_group record048 1 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record048_frame001_indices record048_frame001_graph record048_frame001_links
def record048_frame002_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1081.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1081.count (({ width := 13, code := 0x1445a16d05a6c935598d4c265a32c05e7ae656fab13571ab5956ca8353b2959494a3c4f126c534097d4a624ed23090c47f22290a28314089fc4fce7a33ab9cc0da06a034899c0c7e6303079810bf25ac2c115d0ab052d28f940c9f24ef24991a08a243921110687c43ce1d70e7471836d1a70cf465830d1820bd856e2a214689e04ce25b12608f845a22110908103f41c60db06903221820bb85ac2c01510a304e825e12602c01580aa054010007803a01c00c806002c015009804401e00b004802000e0050018008002000 } : Fields).get c.val)
theorem record048_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record048) (record048.maps 2) (record048.inverseMaps 2) record048_frame002_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1081.localPairCheck (embedding (N := 44310) record048) (record048.maps 2)
      (record048.inverseMaps 2) record048_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame002_links_0000 record048_frame002_links_0064)
theorem record048_frame002_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 2 :=
  of_group record048 2 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1081
    Papers.RationalityTen.SharedFrameCatalogue.group1081_facts record048_frame002_indices record048_frame002_graph record048_frame002_links
def record048_frame003_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1026.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1026.count (({ width := 11, code := 0x4ca99131a5f4bb96b2ca564a97ccf69e8bb8750e99cfb8e718e15c137b6ccd59a9b4c674cdd9832b648c317a2e55aeb2161aae538a4538a5c4b49511ea3b46a8c515a133fc7e4f99df3b4750e81ca362668c61802e45bcb195e2a4534a39422724d09712924c4848a91221c420810fe1f03cc780ec1cc3846f8d019a32c628c017c2e05a0b115e2a4528a3098128248480400780e81c0320600b0150260440780b0120200380500600800800 } : Fields).get c.val)
theorem record048_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record048) (record048.maps 3) (record048.inverseMaps 3) record048_frame003_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1026.localPairCheck (embedding (N := 44310) record048) (record048.maps 3)
      (record048.inverseMaps 3) record048_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame003_links_0000 record048_frame003_links_0064)
theorem record048_frame003_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 3 :=
  of_group record048 3 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1026
    Papers.RationalityTen.SharedFrameCatalogue.group1026_facts record048_frame003_indices record048_frame003_graph record048_frame003_links
def record048_frame004_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x1595aba554a9814a8a27d0ee83d40a658319184ab905abad21648aec56d2ac953ea7a51227ad3b89b84c025b928c933487234917a8af450a24d1188473ff1f18e7670837c9b64d4869333a1984c765e62d99690b0854f29f147ca184e6256125c91247c23811a885c4191f50f487743911b50d5867e3171810b6052e28913d09a84b424c11d88b443820e0ff87c83c81b40d3065c30e1770b48560294139095847021e10102c01580aa054010007803a01c00c806002c015009804401e00b004802000e0050018008002000 } : Fields).get c.val)
theorem record048_frame004_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame004_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame004_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record048) (record048.maps 4) (record048.inverseMaps 4) record048_frame004_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame004_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record048) (record048.maps 4)
      (record048.inverseMaps 4) record048_frame004_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame004_links_0000 record048_frame004_links_0064)
theorem record048_frame004_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 4 :=
  of_group record048 4 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record048_frame004_indices record048_frame004_graph record048_frame004_links
def record048_frame005_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x8e08dd8da8b68b08a089588b88563461f60d5da5cb5c85bc59b59257d57355c53e52c52651a4f94f04d94d14bc49347f47246745945343e4204093d13bc3b83ad38c37e36b35f34e3283133092fe2dd2cf2be2b029d27426125524a23d2372212182081ff1f81ee1dc1d11c61b41ab19917a17517216d16716315c15815314a13f13a13411811110d1061010fe0f90f60f10e80dd0d60d205605405305202001e01d01c01901801601501301100f00b009008007005003002001000 } : Fields).get c.val)
theorem record048_frame005_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame005_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame005_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record048) (record048.maps 5) (record048.inverseMaps 5) record048_frame005_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame005_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record048) (record048.maps 5)
      (record048.inverseMaps 5) record048_frame005_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame005_links_0000 record048_frame005_links_0064)
theorem record048_frame005_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 5 :=
  of_group record048 5 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record048_frame005_indices record048_frame005_graph record048_frame005_links
def record048_frame006_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1075.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1075.count (({ width := 12, code := 0xaf8aeeaeaacaac6aaeaa6a9ba9179b77f76a72b7076fb6e46c76c26ad6a669866d65164c6376136075f05e85da5b459f59158357556f54c52250a4c64a649c48446545c44543a42c3fd3e23d93c239e39437c37136333d32931c30e3012fb2e32d92bb2ac29c2802632542442282222151e91de1d21c51bb1b31ab1a319719018617e17715314813c12f12411d11310b1020fa0f20ea0e105805605505402001e01d01c01901801601501301100f00b009008007005003002001000 } : Fields).get c.val)
theorem record048_frame006_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame006_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 6) (record048.inverseMaps 6) record048_frame006_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame006_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 6) (record048.inverseMaps 6) record048_frame006_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame006_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1075.localPairCheck (embedding (N := 44310) record048) (record048.maps 6)
      (record048.inverseMaps 6) record048_frame006_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame006_links_0000 record048_frame006_links_0064)
theorem record048_frame006_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 6 :=
  of_group record048 6 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1075
    Papers.RationalityTen.SharedFrameCatalogue.group1075_facts record048_frame006_indices record048_frame006_graph record048_frame006_links
def record048_frame007_indices (c : Fin record048.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1024.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1024.count (({ width := 10, code := 0x22789a2588e2187e1d86e19769d272dc26f1bb6ddb06bdab6a5a56799865d936318b61d856057a5cd6e5a5645855451d3d4c92c4ad2647d1e465174490a411033f8f73d8f13bcea388db354d132cc830cc02f0b92d8b22b4aa29ca327c9b2589424c902348c22487214842047f1f87a1e0771d0711c06d1ac691a06518c620e8390e0370741b0681905c16050130440f03409020070180400c0200400 } : Fields).get c.val)
theorem record048_frame007_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.graphBitCheck record048.data.requiredEdges q = true := by decide +kernel
theorem record048_frame007_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (embedding (N := 44310) record048) (record048.maps 7) (record048.inverseMaps 7) record048_frame007_indices (Fin.ofNat record048.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record048_frame007_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (embedding (N := 44310) record048) (record048.maps 7) (record048.inverseMaps 7) record048_frame007_indices (Fin.ofNat record048.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record048_frame007_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1024.localPairCheck (embedding (N := 44310) record048) (record048.maps 7)
      (record048.inverseMaps 7) record048_frame007_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record048_frame007_links_0000 record048_frame007_links_0064)
theorem record048_frame007_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) : Supported record048 7 :=
  of_group record048 7 (embedding record048) hcells Papers.RationalityTen.SharedFrameCatalogue.group1024
    Papers.RationalityTen.SharedFrameCatalogue.group1024_facts record048_frame007_indices record048_frame007_graph record048_frame007_links
theorem record048_frames_supported (hcells : ∀ c, record048.data.cells c = FacetUniverses.FullSix0.cells (embedding record048 c)) :
    ∀ f : Fin record048.g, Supported record048 f :=
  (Fin.cases (record048_frame000_supported hcells) (Fin.cases (record048_frame001_supported hcells) (Fin.cases (record048_frame002_supported hcells) (Fin.cases (record048_frame003_supported hcells) (Fin.cases (record048_frame004_supported hcells) (Fin.cases (record048_frame005_supported hcells) (Fin.cases (record048_frame006_supported hcells) (Fin.cases (record048_frame007_supported hcells) (fun j => Fin.elim0 j)))))))))
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
def record051_frame001_indices (c : Fin record051.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1041.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1041.count (({ width := 12, code := 0x90d8d98cc8c58ad8a286c86183c83983683383082d82782381f81581180d7f57c67b57b27ab78b78878077c77977176b74374173f67666761b5c95a15965875495124a547e47146c44c4173bd38e38033c3333133032f32c42bc2ac29f29a29729426b24723d2312082021fc1f01dd1b019f19518f18316a1661621010fa0f00dc0d40ca0ba09f06a06306005905305204504203c03703403302d02a02301d01c01801501000e00b008007006003002001000 } : Fields).get c.val)
theorem record051_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.graphBitCheck record051.data.requiredEdges q = true := by decide +kernel
theorem record051_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record051_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record051) (record051.maps 1) (record051.inverseMaps 1) record051_frame001_indices (Fin.ofNat record051.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record051_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1041.localPairCheck (embedding (N := 44310) record051) (record051.maps 1)
      (record051.inverseMaps 1) record051_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record051_frame001_links_0000 record051_frame001_links_0064)
theorem record051_frame001_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) : Supported record051 1 :=
  of_group record051 1 (embedding record051) hcells Papers.RationalityTen.SharedFrameCatalogue.group1041
    Papers.RationalityTen.SharedFrameCatalogue.group1041_facts record051_frame001_indices record051_frame001_graph record051_frame001_links
theorem record051_frames_supported (hcells : ∀ c, record051.data.cells c = FacetUniverses.FullSix0.cells (embedding record051 c)) :
    ∀ f : Fin record051.g, Supported record051 f :=
  (Fin.cases (record051_frame000_supported hcells) (Fin.cases (record051_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record051_frames_supported
theorem record052_frame000_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    Supported record052 0 :=
  of_identity record052 0 (by decide +kernel)
def record052_frame001_indices (c : Fin record052.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x325f8feb78db52c01547a9754929b94429544a264cb24a918c89e4270ba852c24dadad2166fb081608ae0552296545299548ba4351de8b2434214d07081e3fa9f1cf627a43ca9bb0ba05ac2b814949ea4611f18f6477637e19a0c7c6082ea1608a4c4fa27013088883f21f30d9867831417b0b3858029212f08d04101fc0f707803841660a204902380d406202e81540a8032015009403a01c00c005402000e004802000e0060028008002000 } : Fields).get c.val)
theorem record052_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record052.data.requiredEdges q = true := by decide +kernel
theorem record052_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record052_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 1) (record052.inverseMaps 1) record052_frame001_indices (Fin.ofNat record052.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record052_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record052) (record052.maps 1)
      (record052.inverseMaps 1) record052_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record052_frame001_links_0000 record052_frame001_links_0064)
theorem record052_frame001_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) : Supported record052 1 :=
  of_group record052 1 (embedding record052) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record052_frame001_indices record052_frame001_graph record052_frame001_links
theorem record052_frames_supported (hcells : ∀ c, record052.data.cells c = FacetUniverses.FullSix0.cells (embedding record052 c)) :
    ∀ f : Fin record052.g, Supported record052 f :=
  (Fin.cases (record052_frame000_supported hcells) (Fin.cases (record052_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record052_frames_supported
theorem record053_frame000_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    Supported record053 0 :=
  of_identity record053 0 (by decide +kernel)
def record053_frame001_indices (c : Fin record053.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x24271a58c7457e2030f184741fa014fe77ec3efdf38f8d78f3addd34e8872738ddc42e0e6f6b75db88c03533a96d3e09c04bd255129c94047da32512482d3fc9f48f5477f3b69cfccbc6542f71704b0255c2a99528a1c4e925f10988324081f48f7473c3761b70d845ea2c813a897c49e23911888484001f40f386cc34a19c0c786082f216c0b204c024811808303ec12e09403f81740ac05502a011c07803901680a804a02100f007403801900b004c02000f004802000e0050018008002000 } : Fields).get c.val)
theorem record053_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record053.data.requiredEdges q = true := by decide +kernel
theorem record053_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record053_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record053) (record053.maps 1) (record053.inverseMaps 1) record053_frame001_indices (Fin.ofNat record053.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record053_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record053) (record053.maps 1)
      (record053.inverseMaps 1) record053_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record053_frame001_links_0000 record053_frame001_links_0064)
theorem record053_frame001_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) : Supported record053 1 :=
  of_group record053 1 (embedding record053) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record053_frame001_indices record053_frame001_graph record053_frame001_links
theorem record053_frames_supported (hcells : ∀ c, record053.data.cells c = FacetUniverses.FullSix0.cells (embedding record053 c)) :
    ∀ f : Fin record053.g, Supported record053 f :=
  (Fin.cases (record053_frame000_supported hcells) (Fin.cases (record053_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record053_frames_supported
theorem record054_frame000_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    Supported record054 0 :=
  of_identity record054 0 (by decide +kernel)
def record054_frame001_indices (c : Fin record054.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1050.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1050.count (({ width := 12, code := 0x81a80a7f57e27d47aa77475874870e6e66ab69d69569268b67c6756546536526296025a659257f5424f14de4c64ac49b47647146245944a42f42a41a4164063f53ef3e63df3ae37c37432c3122c72c22b128027526926625a23e2281fa1c21a61a117b17016415a14e13912911c10d1081000f70ef0e30d20cd0c80c30bb0b90b608a08306c06606305a05405103203102d02502301e01c01501000d008007006005001000 } : Fields).get c.val)
theorem record054_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.graphBitCheck record054.data.requiredEdges q = true := by decide +kernel
theorem record054_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record054_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record054) (record054.maps 1) (record054.inverseMaps 1) record054_frame001_indices (Fin.ofNat record054.n i)) 64 110 :=
  interval_of_check _ 64 46 (by decide +kernel)
theorem record054_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1050.localPairCheck (embedding (N := 44310) record054) (record054.maps 1)
      (record054.inverseMaps 1) record054_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 110 record054_frame001_links_0000 record054_frame001_links_0064)
theorem record054_frame001_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) : Supported record054 1 :=
  of_group record054 1 (embedding record054) hcells Papers.RationalityTen.SharedFrameCatalogue.group1050
    Papers.RationalityTen.SharedFrameCatalogue.group1050_facts record054_frame001_indices record054_frame001_graph record054_frame001_links
theorem record054_frames_supported (hcells : ∀ c, record054.data.cells c = FacetUniverses.FullSix0.cells (embedding record054 c)) :
    ∀ f : Fin record054.g, Supported record054 f :=
  (Fin.cases (record054_frame000_supported hcells) (Fin.cases (record054_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record054_frames_supported
theorem record055_frame000_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    Supported record055 0 :=
  of_identity record055 0 (by decide +kernel)
def record055_frame001_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a36d08671725f909bb85b9ad93664b005526a6151ea2ed02a545283931c9324672228f1c72a36b19d8c2c5da2a913d898c41a1db0e285c428e132c7f60eac555149804aba4811cc86642a2070ff47c53d31e54e966e92f095588984231f60ec86643201740b18522272130891c47e23211508884281ff0fc87cc3d61c90dc86c83301900c185b42ce1510a504d424211208603f81ec0ef07483880e206c03181800b605502a00e406802b014008c03a01c00c806002c015009804001c00c005802000e0040018008002000 } : Fields).get c.val)
theorem record055_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record055) (record055.maps 1) (record055.inverseMaps 1) record055_frame001_indices (Fin.ofNat record055.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record055_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record055) (record055.maps 1)
      (record055.inverseMaps 1) record055_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record055_frame001_links_0000 record055_frame001_links_0064)
theorem record055_frame001_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 1 :=
  of_group record055 1 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record055_frame001_indices record055_frame001_graph record055_frame001_links
def record055_frame002_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0545.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0545.count (({ width := 11, code := 0x57aad958aa6547a3742e854fe9f936e6ccd697f2e2424839011fa3e4798e91ca3846e8db1b2354698d119a32c638c31822f412816f9ded39b724e21b9b4567cc8d8aafd5daba16d2d0546a4d30a5a4a691512a1f4127f8f49de3b4714de9b535a69ccf18f316620c016b2ae5389912d23a420810f01d4364650be1722b85389f130240318610b21582884b0940dc1982b05008c0e81c0320600b0150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record055_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record055) (record055.maps 2) (record055.inverseMaps 2) record055_frame002_indices (Fin.ofNat record055.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record055_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0545.localPairCheck (embedding (N := 44310) record055) (record055.maps 2)
      (record055.inverseMaps 2) record055_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record055_frame002_links_0000 record055_frame002_links_0064)
theorem record055_frame002_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 2 :=
  of_group record055 2 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group0545
    Papers.RationalityTen.SharedFrameCatalogue.group0545_facts record055_frame002_indices record055_frame002_graph record055_frame002_links
def record055_frame003_indices (c : Fin record055.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0544.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0544.count (({ width := 11, code := 0x6e8dc1b6767ec9d41a4347e86d099a733e63ca392b0fe1ec3986b0be13c1982b04605c077fafc5f6be57b6f5de8bc778aefd3da513c66647a8df17e22c1882aff1f93d978ef01d439d6b4cd171ad5590add452824d696d22237464859061fd3e27a8ed9c637c6e0d618b2f45c8ac14f27a4848d10a2083cc718d61a23105f8b91682b4350660ba1682a84f09c0e01a02b05008c0e81c0320600b0150260400700c0160200380400600800800 } : Fields).get c.val)
theorem record055_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.graphBitCheck record055.data.requiredEdges q = true := by decide +kernel
theorem record055_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record055_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record055) (record055.maps 3) (record055.inverseMaps 3) record055_frame003_indices (Fin.ofNat record055.n i)) 64 125 :=
  interval_of_check _ 64 61 (by decide +kernel)
theorem record055_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0544.localPairCheck (embedding (N := 44310) record055) (record055.maps 3)
      (record055.inverseMaps 3) record055_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 125 record055_frame003_links_0000 record055_frame003_links_0064)
theorem record055_frame003_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) : Supported record055 3 :=
  of_group record055 3 (embedding record055) hcells Papers.RationalityTen.SharedFrameCatalogue.group0544
    Papers.RationalityTen.SharedFrameCatalogue.group0544_facts record055_frame003_indices record055_frame003_graph record055_frame003_links
theorem record055_frames_supported (hcells : ∀ c, record055.data.cells c = FacetUniverses.FullSix0.cells (embedding record055 c)) :
    ∀ f : Fin record055.g, Supported record055 f :=
  (Fin.cases (record055_frame000_supported hcells) (Fin.cases (record055_frame001_supported hcells) (Fin.cases (record055_frame002_supported hcells) (Fin.cases (record055_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record057_frame001_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0539.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0539.count (({ width := 11, code := 0x1fa7e8fbdf2be1bb3f5dea9b5751ea0d29946ec5d5b9d6cec858db1360ec057ea033c665cbc9272323fc5e89b11a1cc1d7e4fb1f0bda79aee5d5ba6728deda633b624c297f2d8588afd58a954d899d2ea5849a8f118a2c432845011f83e0780e49c23726c0c217b2e6598a213b26a4ac929112164147e0f71de3906e8bb16c2c0548a20dc1b42e85b0aa1501c83704a08c0e81c0320600b0150260400700c0140200380500600800800 } : Fields).get c.val)
theorem record057_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record057) (record057.maps 1) (record057.inverseMaps 1) record057_frame001_indices (Fin.ofNat record057.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record057_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0539.localPairCheck (embedding (N := 44310) record057) (record057.maps 1)
      (record057.inverseMaps 1) record057_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record057_frame001_links_0000 record057_frame001_links_0064)
theorem record057_frame001_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 1 :=
  of_group record057 1 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group0539
    Papers.RationalityTen.SharedFrameCatalogue.group0539_facts record057_frame001_indices record057_frame001_graph record057_frame001_links
def record057_frame002_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x68db4219c1c97e3db0b3824c085802a93530a8f502a495231913c6d62110ef86d42e214709963fb0756d0b2a54faa294c09c94c926012b68fa432a15106481c3fc1f1cf4c7953a59ba4c685f62b59558a5849522f113084e3c61988c805fc2e81620a4c4e426112388fc46422a11108503fe1f90f987ac3841ba0d9069030617b0ba85b42ce1500a50510278135097849c2420fe07b03c01d00e203881bc0ba05b02a8150072037012808c03a01c00c806002c015009804001c00c005002000e0050018008002000 } : Fields).get c.val)
theorem record057_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 2) (record057.inverseMaps 2) record057_frame002_indices (Fin.ofNat record057.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record057_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record057) (record057.maps 2)
      (record057.inverseMaps 2) record057_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record057_frame002_links_0000 record057_frame002_links_0064)
theorem record057_frame002_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 2 :=
  of_group record057 2 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record057_frame002_indices record057_frame002_graph record057_frame002_links
def record057_frame003_indices (c : Fin record057.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group0538.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group0538.count (({ width := 12, code := 0xb22b11b03ae5ad4ab6aaeaa4a1b9db9d89cd98e8fd8f88f28d38a68a289c89288e88a75d73e7056f36c66bf6a766664f6476346025a65a058757d56c54c53252750c4f64b349845544e4393f33d73ce3bc3a535a34e33d32e3172fb2e62dd2c12b82a729828f27925a24e24723b2071fa1f01db1ad1a219818b18116315915214613d13112511a0eb0e30dc0d20ca06e06c05a05805205103803602502301d01c01901801601501301000e00c00a008007005003002001000 } : Fields).get c.val)
theorem record057_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.graphBitCheck record057.data.requiredEdges q = true := by decide +kernel
theorem record057_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record057_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 3) (record057.inverseMaps 3) record057_frame003_indices (Fin.ofNat record057.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record057_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group0538.localPairCheck (embedding (N := 44310) record057) (record057.maps 3)
      (record057.inverseMaps 3) record057_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record057_frame003_links_0000 record057_frame003_links_0064)
theorem record057_frame003_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) : Supported record057 3 :=
  of_group record057 3 (embedding record057) hcells Papers.RationalityTen.SharedFrameCatalogue.group0538
    Papers.RationalityTen.SharedFrameCatalogue.group0538_facts record057_frame003_indices record057_frame003_graph record057_frame003_links
theorem record057_frames_supported (hcells : ∀ c, record057.data.cells c = FacetUniverses.FullSix0.cells (embedding record057 c)) :
    ∀ f : Fin record057.g, Supported record057 f :=
  (Fin.cases (record057_frame000_supported hcells) (Fin.cases (record057_frame001_supported hcells) (Fin.cases (record057_frame002_supported hcells) (Fin.cases (record057_frame003_supported hcells) (fun j => Fin.elim0 j)))))
#print axioms record057_frames_supported
theorem record058_frame000_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) :
    Supported record058 0 :=
  of_identity record058 0 (by decide +kernel)
def record058_frame001_indices (c : Fin record058.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x5882beb5a4ac8d6368974309d74be65c52dc94a435e1830a8822bdd9edaf6469fb335972c9562aab694d0a5451827c132e96e49f249d21a8f8478a3891b874d3691a48ca85f82e096c4b1055028a938c92c48d234913c88642f2010fb87c03d11c48d486843191708a984e822710f07e83c01d40e0064c2fe1710b104fc27412a092845c2140f6076837412807103281880b605902c01540a804401e80dc066023010007403800e005802000e0050018008002000 } : Fields).get c.val)
theorem record058_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record058.data.requiredEdges q = true := by decide +kernel
theorem record058_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record058_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record058) (record058.maps 1) (record058.inverseMaps 1) record058_frame001_indices (Fin.ofNat record058.n i)) 64 111 :=
  interval_of_check _ 64 47 (by decide +kernel)
theorem record058_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record058) (record058.maps 1)
      (record058.inverseMaps 1) record058_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 111 record058_frame001_links_0000 record058_frame001_links_0064)
theorem record058_frame001_supported (hcells : ∀ c, record058.data.cells c = FacetUniverses.FullSix0.cells (embedding record058 c)) : Supported record058 1 :=
  of_group record058 1 (embedding record058) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record058_frame001_indices record058_frame001_graph record058_frame001_links
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
def record060_frame001_indices (c : Fin record060.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x346da10ce2e4271ed886c37e166ee1703b3d5802a93530a8f5176541281939c5da2ad13f88fc2e214709963fac5553ca8a51327253249804ada47d1c88af42a207101a7c83d31e54e965e12b515589e449522f113084e3eb1d80dec6402e816c8a504e426112388fc46422a11108504001f90ea87243721b20cc064030617c0ba05b42ce1500a50510278135097849c24211308583f81ec0e203e01c40b605802a8150088039011808003a01c00c806002c015009803c01c00c005802000e0050018008002000 } : Fields).get c.val)
theorem record060_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record060.data.requiredEdges q = true := by decide +kernel
theorem record060_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record060_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1) (record060.inverseMaps 1) record060_frame001_indices (Fin.ofNat record060.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record060_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record060) (record060.maps 1)
      (record060.inverseMaps 1) record060_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record060_frame001_links_0000 record060_frame001_links_0064)
theorem record060_frame001_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) : Supported record060 1 :=
  of_group record060 1 (embedding record060) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record060_frame001_indices record060_frame001_graph record060_frame001_links
theorem record060_frames_supported (hcells : ∀ c, record060.data.cells c = FacetUniverses.FullSix0.cells (embedding record060 c)) :
    ∀ f : Fin record060.g, Supported record060 f :=
  (Fin.cases (record060_frame000_supported hcells) (Fin.cases (record060_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record060_frames_supported
theorem record061_frame000_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) :
    Supported record061 0 :=
  of_identity record061 0 (by decide +kernel)
def record061_frame001_indices (c : Fin record061.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x2b695a1ac754429e744aa17ceba74d3929bf4dc66bb34899acc7a6192f596f4a521af0c18544115eecf6d7b234fd99ac9562aab694d0a304f8265d2dc913486a3c51c48dc44f9d34da469232a17e0b825aa2c41540a7851527192588d245422190bc8043ee1f00f4471235219d8c645c22cd15309d044e1fa0f287503801930bf85c42c415609d049422e11008503d81de0dd03281880b605802a815008803d01b80cc05a02a011808003a01c00c005401c00b004001c00c0050018008002000 } : Fields).get c.val)
theorem record061_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record061.data.requiredEdges q = true := by decide +kernel
theorem record061_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record061_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1) (record061.inverseMaps 1) record061_frame001_indices (Fin.ofNat record061.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record061_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record061) (record061.maps 1)
      (record061.inverseMaps 1) record061_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record061_frame001_links_0000 record061_frame001_links_0064)
theorem record061_frame001_supported (hcells : ∀ c, record061.data.cells c = FacetUniverses.FullSix0.cells (embedding record061 c)) : Supported record061 1 :=
  of_group record061 1 (embedding record061) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record061_frame001_indices record061_frame001_graph record061_frame001_links
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
def record063_frame001_indices (c : Fin record063.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1046.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1046.count (({ width := 12, code := 0x8d88c48b98a989886f84482a8297e87c07a079d79878578077777276d76975573c73b73669f69566e65f6586496045dc59057252e4ef4cf4ac49d49948e48547a46e4674584523f13cf36934d3112bd29b27c26c26925924a24423c2362192001fa1ef19517817317216c16a15e14a1331161141080ff0fe0f80e80d50ca0c10bf0bd09407206806005805705605203b03803102d02802202001f01c00e00d00b009007005002001000 } : Fields).get c.val)
theorem record063_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.graphBitCheck record063.data.requiredEdges q = true := by decide +kernel
theorem record063_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record063_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record063) (record063.maps 1) (record063.inverseMaps 1) record063_frame001_indices (Fin.ofNat record063.n i)) 64 113 :=
  interval_of_check _ 64 49 (by decide +kernel)
theorem record063_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1046.localPairCheck (embedding (N := 44310) record063) (record063.maps 1)
      (record063.inverseMaps 1) record063_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 113 record063_frame001_links_0000 record063_frame001_links_0064)
theorem record063_frame001_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) : Supported record063 1 :=
  of_group record063 1 (embedding record063) hcells Papers.RationalityTen.SharedFrameCatalogue.group1046
    Papers.RationalityTen.SharedFrameCatalogue.group1046_facts record063_frame001_indices record063_frame001_graph record063_frame001_links
theorem record063_frames_supported (hcells : ∀ c, record063.data.cells c = FacetUniverses.FullSix0.cells (embedding record063 c)) :
    ∀ f : Fin record063.g, Supported record063 f :=
  (Fin.cases (record063_frame000_supported hcells) (Fin.cases (record063_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record063_frames_supported
theorem record064_frame000_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    Supported record064 0 :=
  of_identity record064 0 (by decide +kernel)
def record064_frame001_indices (c : Fin record064.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x2567249909c76e34b0f183f406de86edc74c3a19cc0e3a712b845be0ddb6e3b19975eb7b55fa7bd37e97a4aa253928088542120d90228023ee9eacefc76c39f9b34d8269933a1830bda5df2e01604ab85532a514049ac4b225291f48de45922390c48324091f40f7073c3761b70d845ec2c915f89e84bc25411c084c4021f30f306cc34a19c0c786082f216c0b2051020c0ea07003580ea05b02d01600a803d01680a8046022010808003801900b004c01c00d005802800e0050018008002000 } : Fields).get c.val)
theorem record064_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record064.data.requiredEdges q = true := by decide +kernel
theorem record064_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record064_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record064) (record064.maps 1) (record064.inverseMaps 1) record064_frame001_indices (Fin.ofNat record064.n i)) 64 118 :=
  interval_of_check _ 64 54 (by decide +kernel)
theorem record064_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record064) (record064.maps 1)
      (record064.inverseMaps 1) record064_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 118 record064_frame001_links_0000 record064_frame001_links_0064)
theorem record064_frame001_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) : Supported record064 1 :=
  of_group record064 1 (embedding record064) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record064_frame001_indices record064_frame001_graph record064_frame001_links
theorem record064_frames_supported (hcells : ∀ c, record064.data.cells c = FacetUniverses.FullSix0.cells (embedding record064 c)) :
    ∀ f : Fin record064.g, Supported record064 f :=
  (Fin.cases (record064_frame000_supported hcells) (Fin.cases (record064_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record064_frames_supported
theorem record065_frame000_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    Supported record065 0 :=
  of_identity record065 0 (by decide +kernel)
def record065_frame001_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x346da10c84e3db0d5859a4bd00a74d38d9b84a8250327392848de452c7f5e52e7d6d0b2d545298149ca254e4a64930095b44d21810a88324109ff4f907a63ca1d2cd2c66b31a17e4aac52c28d13c492a45e226109c6cc32c1900bf85da2c914a09c84c024711f88c845422210a07e43d61e40eb07403921c20d9069033a18f0c185f02ea16d0b3054029414409e04d425e127090844c1ec0e8071036c0ea05b02d01600a803d011808804001c00c806002c015009803801a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record065_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1) (record065.inverseMaps 1) record065_frame001_indices (Fin.ofNat record065.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record065_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record065) (record065.maps 1)
      (record065.inverseMaps 1) record065_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record065_frame001_links_0000 record065_frame001_links_0064)
theorem record065_frame001_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 1 :=
  of_group record065 1 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record065_frame001_indices record065_frame001_graph record065_frame001_links
def record065_frame002_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1052.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1052.count (({ width := 13, code := 0x26252fd91b48463911a37a1bb71d30e8673038e9c4ae116f8376db8eb2e5652afd530a7850827bd3c09bf4bd255129a940442a1090688114001f74f5677e3b61cfcd9a6c134c99d0c185ed2ef9700b0255c2aa152896447d23991648964312048fa07b83ab1cf0e0c6ec36d1b08c505ec2e71648afc56229d13b09784a0238112084c4021f30f306cc34e19c0c786102f216c0b205102100ea07003580ea05b02d01600a803d011808804001c00c806002c015009803801a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record065_frame002_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame002_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame002_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 2) (record065.inverseMaps 2) record065_frame002_indices (Fin.ofNat record065.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record065_frame002_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1052.localPairCheck (embedding (N := 44310) record065) (record065.maps 2)
      (record065.inverseMaps 2) record065_frame002_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record065_frame002_links_0000 record065_frame002_links_0064)
theorem record065_frame002_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 2 :=
  of_group record065 2 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1052
    Papers.RationalityTen.SharedFrameCatalogue.group1052_facts record065_frame002_indices record065_frame002_graph record065_frame002_links
def record065_frame003_indices (c : Fin record065.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1051.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1051.count (({ width := 12, code := 0x8558548388348268227b67a279278e78677977577176d7687646606236176045f15b95a659b58455d54553f5334c34a64a149348a47645b44743c4243e73db3c83b537c36535b3483203093032f728726a26425024823a21f2081ff1ec1e41d81d01cb1c51ad19d19518517f17d17916915b15314513e13a13512f12811811310d1060ff0f90f20ed0e60cd0c30bf0b907405a05905705303d02302202001c01901801601501300e00d00c00b00a007005003002001000 } : Fields).get c.val)
theorem record065_frame003_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.graphBitCheck record065.data.requiredEdges q = true := by decide +kernel
theorem record065_frame003_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record065) (record065.maps 3) (record065.inverseMaps 3) record065_frame003_indices (Fin.ofNat record065.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record065_frame003_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record065) (record065.maps 3) (record065.inverseMaps 3) record065_frame003_indices (Fin.ofNat record065.n i)) 64 122 :=
  interval_of_check _ 64 58 (by decide +kernel)
theorem record065_frame003_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1051.localPairCheck (embedding (N := 44310) record065) (record065.maps 3)
      (record065.inverseMaps 3) record065_frame003_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 122 record065_frame003_links_0000 record065_frame003_links_0064)
theorem record065_frame003_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) : Supported record065 3 :=
  of_group record065 3 (embedding record065) hcells Papers.RationalityTen.SharedFrameCatalogue.group1051
    Papers.RationalityTen.SharedFrameCatalogue.group1051_facts record065_frame003_indices record065_frame003_graph record065_frame003_links
theorem record065_frames_supported (hcells : ∀ c, record065.data.cells c = FacetUniverses.FullSix0.cells (embedding record065 c)) :
    ∀ f : Fin record065.g, Supported record065 f :=
  (Fin.cases (record065_frame000_supported hcells) (Fin.cases (record065_frame001_supported hcells) (Fin.cases (record065_frame002_supported hcells) (Fin.cases (record065_frame003_supported hcells) (fun j => Fin.elim0 j)))))
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
def record067_frame001_indices (c : Fin record067.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x3099835b525a3ecb94e09ddced6495231913c6de20f0ee86cc2e614909a6f035dda1eb0a56e2a694a49c94bc24692228e946ca1950ae83240c9fa0fa67c73da1e54bac5a82b3147892a4441f30f7476a3a51988c8c5fc2e515a0a7c52628013088fc42a1ea0dd06903221890bd859c2a014409e04bc21610507f03c01d00e2053825012007f035817c0ba05502a011c066027012807403801900b004802000f005002000e0050018008002000 } : Fields).get c.val)
theorem record067_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record067.data.requiredEdges q = true := by decide +kernel
theorem record067_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record067_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1) (record067.inverseMaps 1) record067_frame001_indices (Fin.ofNat record067.n i)) 64 106 :=
  interval_of_check _ 64 42 (by decide +kernel)
theorem record067_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record067) (record067.maps 1)
      (record067.inverseMaps 1) record067_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 106 record067_frame001_links_0000 record067_frame001_links_0064)
theorem record067_frame001_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) : Supported record067 1 :=
  of_group record067 1 (embedding record067) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record067_frame001_indices record067_frame001_graph record067_frame001_links
theorem record067_frames_supported (hcells : ∀ c, record067.data.cells c = FacetUniverses.FullSix0.cells (embedding record067 c)) :
    ∀ f : Fin record067.g, Supported record067 f :=
  (Fin.cases (record067_frame000_supported hcells) (Fin.cases (record067_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record070_frame001_indices (c : Fin record070.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x144fa1dd07a8154049f1cf325e72dc8db4692229107877c14e0790228083e7de88f3b79934757e8aef55c2a7d4d09834a624cd1f88dd45ea28513088c3fd9e64db06a23371984c545832a69464a184d524b92408f846a20d8d6062c3021628a544da25a12608b043820e0fe87c43c81b20c505dc2d214909c84ac23410e08083a013008e04201f80b005502a013008c04401e80cc05c024010007c03a01c00c0054024011007002c0100070028008002000 } : Fields).get c.val)
theorem record070_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record070.data.requiredEdges q = true := by decide +kernel
theorem record070_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record070_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record070) (record070.maps 1) (record070.inverseMaps 1) record070_frame001_indices (Fin.ofNat record070.n i)) 64 109 :=
  interval_of_check _ 64 45 (by decide +kernel)
theorem record070_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record070) (record070.maps 1)
      (record070.inverseMaps 1) record070_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 109 record070_frame001_links_0000 record070_frame001_links_0064)
theorem record070_frame001_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) : Supported record070 1 :=
  of_group record070 1 (embedding record070) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record070_frame001_indices record070_frame001_graph record070_frame001_links
theorem record070_frames_supported (hcells : ∀ c, record070.data.cells c = FacetUniverses.FullSix0.cells (embedding record070 c)) :
    ∀ f : Fin record070.g, Supported record070 f :=
  (Fin.cases (record070_frame000_supported hcells) (Fin.cases (record070_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record070_frames_supported
theorem record071_frame000_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    Supported record071 0 :=
  of_identity record071 0 (by decide +kernel)
theorem record071_frames_supported (hcells : ∀ c, record071.data.cells c = FacetUniverses.FullSix0.cells (embedding record071 c)) :
    ∀ f : Fin record071.g, Supported record071 f :=
  (Fin.cases (record071_frame000_supported hcells) (fun j => Fin.elim0 j))
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
def record073_frame001_indices (c : Fin record073.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x1a36c84e3db0d5859bcddbf2d7f627b0655d6ad34e0a004ed64a1237914c5ee2170f2869c2f615109c6ba2e796d0a9c52727252f691f474a2650c08544192084f907b43ca19a8c6856828d125488e3eb1da8d9465832017f0bb4528280130091c47e21510007a83c81d70e787243841b20d2067430617c0b3054029414409e04d425e11308584141ec0e8071036c108075035817c0b405802a013007a033013808804001c00c806002c015009003c01a00c005802800e0050018008002000 } : Fields).get c.val)
theorem record073_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record073.data.requiredEdges q = true := by decide +kernel
theorem record073_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record073_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1) (record073.inverseMaps 1) record073_frame001_indices (Fin.ofNat record073.n i)) 64 117 :=
  interval_of_check _ 64 53 (by decide +kernel)
theorem record073_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record073) (record073.maps 1)
      (record073.inverseMaps 1) record073_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 117 record073_frame001_links_0000 record073_frame001_links_0064)
theorem record073_frame001_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) : Supported record073 1 :=
  of_group record073 1 (embedding record073) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record073_frame001_indices record073_frame001_graph record073_frame001_links
theorem record073_frames_supported (hcells : ∀ c, record073.data.cells c = FacetUniverses.FullSix0.cells (embedding record073 c)) :
    ∀ f : Fin record073.g, Supported record073 f :=
  (Fin.cases (record073_frame000_supported hcells) (Fin.cases (record073_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record073_frames_supported
theorem record074_frame000_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    Supported record074 0 :=
  of_identity record074 0 (by decide +kernel)
def record074_frame001_indices (c : Fin record074.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0xc6062aaf1977bb31d09a8293bb9dac96247f22d8d8465e2ff168861c2ba13cde26862c1d4aca274e4a60d234911474a33918286542620b50327e93ee9ee4f265d329113cc92a44f1f30f7476a39a1c68cc46302f91728ad455228512f88fc3d41de0eb86e832218a0b985942a014409e04bc24210b08283c01d00d504f025c12807f03901740b405602a811c074025011007803a01900b004001e00d00500240100050018008002000 } : Fields).get c.val)
theorem record074_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record074.data.requiredEdges q = true := by decide +kernel
theorem record074_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record074_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record074) (record074.maps 1) (record074.inverseMaps 1) record074_frame001_indices (Fin.ofNat record074.n i)) 64 104 :=
  interval_of_check _ 64 40 (by decide +kernel)
theorem record074_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record074) (record074.maps 1)
      (record074.inverseMaps 1) record074_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 104 record074_frame001_links_0000 record074_frame001_links_0064)
theorem record074_frame001_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) : Supported record074 1 :=
  of_group record074 1 (embedding record074) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record074_frame001_indices record074_frame001_graph record074_frame001_links
theorem record074_frames_supported (hcells : ∀ c, record074.data.cells c = FacetUniverses.FullSix0.cells (embedding record074 c)) :
    ∀ f : Fin record074.g, Supported record074 f :=
  (Fin.cases (record074_frame000_supported hcells) (Fin.cases (record074_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
theorem record077_frames_supported (hcells : ∀ c, record077.data.cells c = FacetUniverses.FullSix0.cells (embedding record077 c)) :
    ∀ f : Fin record077.g, Supported record077 f :=
  (Fin.cases (record077_frame000_supported hcells) (fun j => Fin.elim0 j))
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
theorem record086_frames_supported (hcells : ∀ c, record086.data.cells c = FacetUniverses.FullSix0.cells (embedding record086 c)) :
    ∀ f : Fin record086.g, Supported record086 f :=
  (Fin.cases (record086_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record086_frames_supported
theorem record087_frame000_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    Supported record087 0 :=
  of_identity record087 0 (by decide +kernel)
def record087_frame001_indices (c : Fin record087.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1100.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1100.count (({ width := 13, code := 0x29bd4b9a3d513a84540b9d7cdee6612f495c4a921e90e985fc2d1f00f5d7a03c75c8ccab64c32057e8bb05a92c395a0ac055d2aad53a98c4bba56927e8d9462229d11884541fa0dd05e79c3ad1bc8d6066d3309960c9864531f9838ab85522989494a144cf262929093047d230916c8ae4512020e9c69633e1980c7061a2fe16e8aa853a28f13d89b04ba23c11508904382150f0872834814809d84b824810b07f03c41ce0d203101680aa04702200f407402a012008803e01d00c005402000e006802c0120080030008002000 } : Fields).get c.val)
theorem record087_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.graphBitCheck record087.data.requiredEdges q = true := by decide +kernel
theorem record087_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record087_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record087) (record087.maps 1) (record087.inverseMaps 1) record087_frame001_indices (Fin.ofNat record087.n i)) 64 126 :=
  interval_of_check _ 64 62 (by decide +kernel)
theorem record087_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1100.localPairCheck (embedding (N := 44310) record087) (record087.maps 1)
      (record087.inverseMaps 1) record087_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 126 record087_frame001_links_0000 record087_frame001_links_0064)
theorem record087_frame001_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) : Supported record087 1 :=
  of_group record087 1 (embedding record087) hcells Papers.RationalityTen.SharedFrameCatalogue.group1100
    Papers.RationalityTen.SharedFrameCatalogue.group1100_facts record087_frame001_indices record087_frame001_graph record087_frame001_links
theorem record087_frames_supported (hcells : ∀ c, record087.data.cells c = FacetUniverses.FullSix0.cells (embedding record087 c)) :
    ∀ f : Fin record087.g, Supported record087 f :=
  (Fin.cases (record087_frame000_supported hcells) (Fin.cases (record087_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record087_frames_supported
theorem record088_frame000_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    Supported record088 0 :=
  of_identity record088 0 (by decide +kernel)
def record088_frame001_indices (c : Fin record088.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1114.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1114.count (({ width := 13, code := 0x573ab754dfa674e7a71532f98c4a7253122590f48063d10bc851c1960a6ff97f334a198cc8b6282b0d4c2a264f5a6f536e99c4b9a5912b89544a6a4c925691848b241d2008f3473a3911b273a36c1a6cbf65aa2a41474a084f424f121c8c245421190047d63e11c60cec5b22ae14a8a1445e2180f907943681920be05c82ae14b0a004ec26a12b093046022210908303f81ea0f007503941b80d6068028812a08e04601fc0e406b03480c405a02a012808803c01d00e006002a0100068024010007 } : Fields).get c.val)
theorem record088_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.graphBitCheck record088.data.requiredEdges q = true := by decide +kernel
theorem record088_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record088_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record088) (record088.maps 1) (record088.inverseMaps 1) record088_frame001_indices (Fin.ofNat record088.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record088_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1114.localPairCheck (embedding (N := 44310) record088) (record088.maps 1)
      (record088.inverseMaps 1) record088_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record088_frame001_links_0000 record088_frame001_links_0064)
theorem record088_frame001_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) : Supported record088 1 :=
  of_group record088 1 (embedding record088) hcells Papers.RationalityTen.SharedFrameCatalogue.group1114
    Papers.RationalityTen.SharedFrameCatalogue.group1114_facts record088_frame001_indices record088_frame001_graph record088_frame001_links
theorem record088_frames_supported (hcells : ∀ c, record088.data.cells c = FacetUniverses.FullSix0.cells (embedding record088 c)) :
    ∀ f : Fin record088.g, Supported record088 f :=
  (Fin.cases (record088_frame000_supported hcells) (Fin.cases (record088_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record088_frames_supported
theorem record089_frame000_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    Supported record089 0 :=
  of_identity record089 0 (by decide +kernel)
def record089_frame001_indices (c : Fin record089.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1110.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1110.count (({ width := 13, code := 0x5312959453a1fce767112c094fc8ce433141896c41e1defc97d63e09ee0d636aeb511a40d0c68233d5726b44577aad5538a274ec260d292930477a38d1b08d3466a30d17c8b0454a2891388944459ce4df86a233818e4bc85a72a6946c9c84b825a12b49484a024c124491447d23a91c48d241b1e08d6063629514289e84d025612608b441c1fd0f906c83441970c285cc2d214a095846821e0f907803a81c40db06a01d00e206903281880b403d01d00cc06202e015809004400d0058024010007002800c004001 } : Fields).get c.val)
theorem record089_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.graphBitCheck record089.data.requiredEdges q = true := by decide +kernel
theorem record089_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record089_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record089) (record089.maps 1) (record089.inverseMaps 1) record089_frame001_indices (Fin.ofNat record089.n i)) 64 123 :=
  interval_of_check _ 64 59 (by decide +kernel)
theorem record089_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1110.localPairCheck (embedding (N := 44310) record089) (record089.maps 1)
      (record089.inverseMaps 1) record089_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 123 record089_frame001_links_0000 record089_frame001_links_0064)
theorem record089_frame001_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) : Supported record089 1 :=
  of_group record089 1 (embedding record089) hcells Papers.RationalityTen.SharedFrameCatalogue.group1110
    Papers.RationalityTen.SharedFrameCatalogue.group1110_facts record089_frame001_indices record089_frame001_graph record089_frame001_links
theorem record089_frames_supported (hcells : ∀ c, record089.data.cells c = FacetUniverses.FullSix0.cells (embedding record089 c)) :
    ∀ f : Fin record089.g, Supported record089 f :=
  (Fin.cases (record089_frame000_supported hcells) (Fin.cases (record089_frame001_supported hcells) (fun j => Fin.elim0 j)))
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
def record091_frame001_indices (c : Fin record091.n) : Fin Papers.RationalityTen.SharedFrameCatalogue.group1115.count :=
  Fin.ofNat Papers.RationalityTen.SharedFrameCatalogue.group1115.count (({ width := 13, code := 0x68db38b8f6c2ce05efcd79bb7e5ab6cf564eb1fd7f2ad355daa2545a83d40ca004efa3b11bf8d845ca23710286bad4d600a9e530a93138e98048ea39515a8454081fb0f967aa3c8187cb9856a296946092644c1f48ec46f231116e0ae052e27612e091c47e22210007a83c81d70e486e435a1a50cc062830617c0ba05b829414409a84bc25012108984141dc0e006c834c0e807103481980c605c02d00f007203101700ac04802200c806002c015007803401800b004802000e005002000c004001 } : Fields).get c.val)
theorem record091_frame001_graph : ∀ q,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.graphBitCheck record091.data.requiredEdges q = true := by decide +kernel
theorem record091_frame001_links_0000 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 0 64 :=
  interval_of_check _ 0 64 (by decide +kernel)
theorem record091_frame001_links_0064 : Interval (fun i => Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record091) (record091.maps 1) (record091.inverseMaps 1) record091_frame001_indices (Fin.ofNat record091.n i)) 64 119 :=
  interval_of_check _ 64 55 (by decide +kernel)
theorem record091_frame001_links : ∀ c,
    Papers.RationalityTen.SharedFrameCatalogue.group1115.localPairCheck (embedding (N := 44310) record091) (record091.maps 1)
      (record091.inverseMaps 1) record091_frame001_indices c = true :=
  fin_of_interval _ (interval_append _ 0 64 119 record091_frame001_links_0000 record091_frame001_links_0064)
theorem record091_frame001_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) : Supported record091 1 :=
  of_group record091 1 (embedding record091) hcells Papers.RationalityTen.SharedFrameCatalogue.group1115
    Papers.RationalityTen.SharedFrameCatalogue.group1115_facts record091_frame001_indices record091_frame001_graph record091_frame001_links
theorem record091_frames_supported (hcells : ∀ c, record091.data.cells c = FacetUniverses.FullSix0.cells (embedding record091 c)) :
    ∀ f : Fin record091.g, Supported record091 f :=
  (Fin.cases (record091_frame000_supported hcells) (Fin.cases (record091_frame001_supported hcells) (fun j => Fin.elim0 j)))
#print axioms record091_frames_supported
theorem record092_frame000_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    Supported record092 0 :=
  of_identity record092 0 (by decide +kernel)
theorem record092_frames_supported (hcells : ∀ c, record092.data.cells c = FacetUniverses.FullSix0.cells (embedding record092 c)) :
    ∀ f : Fin record092.g, Supported record092 f :=
  (Fin.cases (record092_frame000_supported hcells) (fun j => Fin.elim0 j))
#print axioms record092_frames_supported
end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00072

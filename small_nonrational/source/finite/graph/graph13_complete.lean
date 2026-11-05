module
prelude
public import Graph13Step00
public import Graph13Step01
public import Graph13Step02
public import Graph13Step03
public import Graph13Step04
public import Graph13Step05
public import Graph13Step06
public import Graph13Step07
public import Graph13Step08
public import Graph13Step09
public import Graph13Step10
public import Graph13Step11
public import Graph13Step12

@[expose] public section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13
open Papers.RationalityTen
open GraphCatalogueCore
theorem level00_complete : Covers TenGraphEdges.incidence 4 Frames.renamings
    (fun i => (Level00.entry i).edges) 0 :=
  covers_zero TenGraphEdges.incidence 4 Frames.renamings
    (fun i => (Level00.entry i).edges) 0 (by decide +kernel)
theorem level01_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level01.entry i).edges) 1 :=
  Step00.covers_step level00_complete
theorem level02_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level02.entry i).edges) 2 :=
  Step01.covers_step level01_complete
theorem level03_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level03.entry i).edges) 3 :=
  Step02.covers_step level02_complete
theorem level04_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level04.entry i).edges) 4 :=
  Step03.covers_step level03_complete
theorem level05_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level05.entry i).edges) 5 :=
  Step04.covers_step level04_complete
theorem level06_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level06.entry i).edges) 6 :=
  Step05.covers_step level05_complete
theorem level07_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level07.entry i).edges) 7 :=
  Step06.covers_step level06_complete
theorem level08_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level08.entry i).edges) 8 :=
  Step07.covers_step level07_complete
theorem level09_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level09.entry i).edges) 9 :=
  Step08.covers_step level08_complete
theorem level10_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level10.entry i).edges) 10 :=
  Step09.covers_step level09_complete
theorem level11_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level11.entry i).edges) 11 :=
  Step10.covers_step level10_complete
theorem level12_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level12.entry i).edges) 12 :=
  Step11.covers_step level11_complete
theorem level13_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level13.entry i).edges) 13 :=
  Step12.covers_step level12_complete
#print axioms level13_complete
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13

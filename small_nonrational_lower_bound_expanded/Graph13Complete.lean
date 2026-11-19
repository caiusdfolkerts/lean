module
prelude
public meta import LowerSchemas.FiniteGraph
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
cert_level_complete 01 1 00
cert_level_complete 02 2 01
cert_level_complete 03 3 02
cert_level_complete 04 4 03
cert_level_complete 05 5 04
cert_level_complete 06 6 05
cert_level_complete 07 7 06
cert_level_complete 08 8 07
cert_level_complete 09 9 08
cert_level_complete 10 10 09
cert_level_complete 11 11 10
cert_level_complete 12 12 11
cert_level_complete 13 13 12
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13

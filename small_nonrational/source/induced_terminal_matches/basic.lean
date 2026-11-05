module
prelude
public import RawBoundaryMatch
public import RawTargets

@[expose] public section
namespace Nonrational.InducedTerminalMatches
open Papers.RationalityTen.RawBoundaryMatch Nonrational.TerminalData

structure Entry where
  boundary : RawBoundary
  witness : Witness

noncomputable def check (e : Entry) : Bool :=
  witnessCheck targetCount (fun i => (targets i).facets)
    (fun i => (targets i).polygons) e.boundary.facets e.boundary.polygons e.witness

theorem check_eq (e : Entry) : check e =
    witnessCheck targetCount (fun i => (targets i).facets)
      (fun i => (targets i).polygons) e.boundary.facets e.boundary.polygons e.witness := rfl

end Nonrational.InducedTerminalMatches

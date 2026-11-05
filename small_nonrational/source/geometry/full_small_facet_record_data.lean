module
prelude
public import FullSmallFacetUniverse
public import RawSmallCellMetadata
public import FiniteChecks

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.FullSmall

    noncomputable def recordTest (i : Nat) : Bool :=
      let a := Fin.ofNat cellCount i
      RawSmallCellMetadata.check (cells a)
    end Papers.RationalityTen.FacetUniverses.FullSmall

module
public import RawTargets
public import Papers.FiniteProjectionData
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-! The semantic meaning of a literal boundary target. Both complete face
families are decoded; the plane cache is the proved canonical default. -/
namespace Nonrational.TerminalVerification

open Nonrational.TerminalData
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

def decodeMask (m : Nat) : Finset (Fin 10) :=
  Finset.univ.filter fun i => m.testBit i.val = true

def decode (B : RawBoundary) : Boundary 9 where
  facets := B.facets.toFinset.image decodeMask
  polygons := B.polygons.toFinset.image decodeMask

def Certifies (j : Nat) : Prop :=
  Nonempty (CertifiedRelabelling (decode (targets j)))

theorem certified_of_eq {B T : Boundary 9} {c : Nat}
    (C : ReconstructionCertificate T c) (h : B = T) :
    Nonempty (CertifiedRelabelling B) := by
  subst B
  exact ⟨{
    target := T
    heightRows := c
    certificate := C
    permutation := Equiv.refl _
    boundary_eq := Boundary.relabel_refl T }⟩

end Nonrational.TerminalVerification

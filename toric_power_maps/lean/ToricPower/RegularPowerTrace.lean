module

public import ToricPower.GeometricCore
public import ToricPower.FrobeniusTraceAdjunction
public import Mathlib.Data.Fin.Rev

/-!
# The perfect residue trace on every smooth affine power chart

For a polynomial--Laurent coordinate ring, the coefficient of the residue
whose coordinates are all `ell-1` is a Frobenius functional for the actual
power-map module. The complementary residue is `ell-1-u`; the matrix of
the multiplication pairing on the full residue basis is its permutation
matrix. All polynomial and invertible coordinates are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MonoidAlgebra Module
open scoped Classical

namespace ToricPower

section Coordinates

variable {k M L I : Type*} [Semiring k] [Monoid M] [Monoid L]

/-- The actual residue basis extracts exactly the specified monomial coordinate. -/
theorem monoidDecompositionBasis_repr_single
    (p : M →* L) (e : I × M ≃ L)
    (he : ∀ i m, e (i,m) = p m * e (i,1)) (i : I) (m : M) (r : k) :
    letI := (mapDomainRingHom k p).toModule
    (monoidDecompositionBasis (R := k) p e he).repr (single (e (i,m)) r) =
      Finsupp.single i (single m r) := by
  letI := (mapDomainRingHom k p).toModule
  rw [← monoidDecompositionAddEquiv_single_single e i m r]
  exact (monoidDecompositionLinearEquiv (R := k) p e he).symm_apply_apply _

/-- A monomial in a different residue has zero chosen coordinate. -/
theorem monoidDecompositionBasis_coord_single_of_ne
    (p : M →* L) (e : I × M ≃ L)
    (he : ∀ i m, e (i,m) = p m * e (i,1)) (i : I) (m : L) (r : k)
    (different : (e.symm m).1 ≠ i) :
    letI := (mapDomainRingHom k p).toModule
    (monoidDecompositionBasis (R := k) p e he).coord i (single m r) = 0 := by
  letI := (mapDomainRingHom k p).toModule
  have equality := monoidDecompositionBasis_repr_single p e he
    (e.symm m).1 (e.symm m).2 r
  rw [e.apply_symm_apply] at equality
  change (monoidDecompositionBasis (R := k) p e he).repr (single m r) i = 0
  rw [equality, Finsupp.single_eq_of_ne different.symm]

end Coordinates

variable (ell : ℕ) (α β : Type*) (positive : 0 < ell)

/-- The top residue in every polynomial and Laurent coordinate. -/
def regularTopResidue : RegularResidues ell α β :=
  (fun _ => ⟨ell-1, by omega⟩, fun _ => ⟨ell-1, by omega⟩)

/-- Complementation is a permutation of the full residue index set. -/
def regularComplementResidue : RegularResidues ell α β ≃ RegularResidues ell α β :=
  Equiv.prodCongr (Equiv.piCongrRight fun _ => Fin.revPerm)
    (Equiv.piCongrRight fun _ => Fin.revPerm)

/-- The actual exponent of one residue-basis monomial. -/
def regularResidueExponent (u : RegularResidues ell α β) : RegularExponents α β :=
  (fun j => (u.1 j : ℕ), fun j => (u.2 j : ℤ))

theorem regularMonoidDecomposition_residue (u : RegularResidues ell α β) :
    regularMonoidDecomposition ell α β positive (u,1) =
      Multiplicative.ofAdd (regularResidueExponent ell α β u) := by
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> funext j <;>
    simp [regularMonoidDecomposition, regularResidueEquiv_apply, regularResidueExponent]

theorem regularResidueExponent_add_complement (u : RegularResidues ell α β) :
    regularResidueExponent ell α β u +
        regularResidueExponent ell α β (regularComplementResidue ell α β u) =
      regularResidueExponent ell α β (regularTopResidue ell α β positive) := by
  apply Prod.ext
  · funext j
    change (u.1 j : ℕ) + (Fin.rev (u.1 j) : ℕ) = ell-1
    simp only [Fin.val_rev]
    omega
  · funext j
    change (u.2 j : ℤ) + ((Fin.rev (u.2 j) : ℕ) : ℤ) = ((ell-1 : ℕ) : ℤ)
    simp only [Fin.val_rev]
    have h := (u.2 j).isLt
    omega

/-- A sum of two residue vectors can have top residue only when the
two vectors are complementary. This includes every Laurent axis. -/
theorem regular_product_top_residue_implies_complement
    (u v : RegularResidues ell α β)
    (top : ((regularMonoidDecomposition ell α β positive).symm
      (Multiplicative.ofAdd (regularResidueExponent ell α β u +
        regularResidueExponent ell α β v))).1 = regularTopResidue ell α β positive) :
    v = regularComplementResidue ell α β u := by
  let e := regularMonoidDecomposition ell α β positive
  let w := Multiplicative.ofAdd
    (regularResidueExponent ell α β u + regularResidueExponent ell α β v)
  have identity := e.apply_symm_apply w
  apply Prod.ext
  · funext j
    apply Fin.ext
    have coordinate := congrArg (fun z => z.toAdd.1 j) identity
    change ((e.symm w).1.1 j : ℕ) + ell * (e.symm w).2.toAdd.1 j =
      (u.1 j : ℕ) + (v.1 j : ℕ) at coordinate
    rw [top] at coordinate
    change ell-1 + ell * (e.symm w).2.toAdd.1 j = _ at coordinate
    change (v.1 j : ℕ) = (Fin.rev (u.1 j) : ℕ)
    simp only [Fin.val_rev]
    have hu := (u.1 j).isLt
    have hv := (v.1 j).isLt
    have hq : (e.symm w).2.toAdd.1 j = 0 := by
      by_contra nonzero
      have bound : ell ≤ ell * (e.symm w).2.toAdd.1 j :=
        Nat.le_mul_of_pos_right ell (by omega)
      omega
    rw [hq, mul_zero, add_zero] at coordinate
    omega
  · funext j
    apply Fin.ext
    have coordinate := congrArg (fun z => z.toAdd.2 j) identity
    change ((e.symm w).1.2 j : ℤ) + (ell : ℤ) * (e.symm w).2.toAdd.2 j =
      (u.2 j : ℤ) + (v.2 j : ℤ) at coordinate
    rw [top] at coordinate
    change ((ell-1 : ℕ) : ℤ) + (ell : ℤ) * (e.symm w).2.toAdd.2 j = _ at coordinate
    change (v.2 j : ℕ) = (Fin.rev (u.2 j) : ℕ)
    simp only [Fin.val_rev]
    have hu := (u.2 j).isLt
    have hv := (v.2 j).isLt
    have hp : ((ell-1 : ℕ) : ℤ) = (ell : ℤ)-1 := by omega
    rw [hp] at coordinate
    have hell : (0 : ℤ) < ell := by exact_mod_cast positive
    have hu₀ : (0 : ℤ) ≤ (u.2 j : ℕ) := Int.natCast_nonneg _
    have hv₀ : (0 : ℤ) ≤ (v.2 j : ℕ) := Int.natCast_nonneg _
    have hu₁ : (u.2 j : ℤ) < ell := by exact_mod_cast hu
    have hv₁ : (v.2 j : ℤ) < ell := by exact_mod_cast hv
    have hq : (e.symm w).2.toAdd.2 j = 0 := by
      by_contra nonzero
      rcases lt_or_gt_of_ne nonzero with negative | pos
      · have bound : (e.symm w).2.toAdd.2 j ≤ -1 := by omega
        nlinarith
      · have bound : 1 ≤ (e.symm w).2.toAdd.2 j := by omega
        nlinarith
    rw [hq, mul_zero, add_zero] at coordinate
    omega

variable (k : Type*) [CommRing k]

local notation "S" => MonoidAlgebra k (Multiplicative (RegularExponents α β))
local notation "φ" => mapDomainRingHom k (exponentPower ell (RegularExponents α β))

/-- Extraction of the top residue is an actual linear map for the power action. -/
def regularPowerTrace :
    letI := (φ).toModule
    Module.Dual S S := by
  letI := (φ).toModule
  exact (regularPowerBasis k ell α β positive).coord (regularTopResidue ell α β positive)

theorem regularPowerBasis_monomial (u : RegularResidues ell α β) :
    letI := (φ).toModule
    regularPowerBasis k ell α β positive u =
      single (Multiplicative.ofAdd (regularResidueExponent ell α β u)) 1 := by
  letI := (φ).toModule
  rw [regularPowerBasis, monoidDecompositionBasis_apply,
    regularMonoidDecomposition_residue]

/-- The multiplication pairing has the actual complementary-residue matrix. -/
theorem regularPowerTrace_basis_pairing (u v : RegularResidues ell α β) :
    letI := (φ).toModule
    regularPowerTrace ell α β positive k
        (regularPowerBasis k ell α β positive u * regularPowerBasis k ell α β positive v) =
      if regularComplementResidue ell α β u = v then 1 else 0 := by
  letI := (φ).toModule
  by_cases equal : regularComplementResidue ell α β u = v
  · subst v
    have product : regularPowerBasis k ell α β positive u *
        regularPowerBasis k ell α β positive (regularComplementResidue ell α β u) =
        regularPowerBasis k ell α β positive (regularTopResidue ell α β positive) := by
      rw [regularPowerBasis_monomial, regularPowerBasis_monomial,
        regularPowerBasis_monomial, single_mul_single, mul_one]
      exact congrArg (fun z => single (Multiplicative.ofAdd z) (1 : k))
        (regularResidueExponent_add_complement ell α β positive u)
    rw [product]
    simp [regularPowerTrace, Basis.coord_apply]
  · rw [if_neg equal, regularPowerBasis_monomial, regularPowerBasis_monomial,
      single_mul_single, mul_one]
    apply monoidDecompositionBasis_coord_single_of_ne
    intro top
    exact equal (regular_product_top_residue_implies_complement ell α β positive u v top).symm

variable [Fintype α] [Fintype β]

/-- The actual multiplication trace pairing is bijective on the full power module. -/
theorem regularPowerTrace_perfect :
    letI : Algebra S S := (φ).toAlgebra
    Function.Bijective (multiplicationTracePairing
      (regularPowerTrace ell α β positive k)) := by
  letI : Algebra S S := (φ).toAlgebra
  let equivalence := multiplicationTraceEquivOfBasis
    (regularPowerBasis k ell α β positive) (regularComplementResidue ell α β)
    (regularPowerTrace ell α β positive k)
    (by
      intro u v
      by_cases equal : regularComplementResidue ell α β u = v
      · simpa only [if_pos equal] using regularPowerTrace_basis_pairing ell α β positive k u v
      · simpa only [if_neg equal] using regularPowerTrace_basis_pairing ell α β positive k u v)
  exact equivalence.bijective

end ToricPower

end

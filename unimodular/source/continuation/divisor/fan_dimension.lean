module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

/-! # The actual dimension of a smooth complete fan scheme

This independent module contains the exact coordinate-algebra and Krull-dimension
proofs formerly bundled with the intrinsic canonical calculation. No differential,
projectivity, canonical-sheaf, or dimension assumption is used.
-/

noncomputable section
section FanDimensionCoordinates
universe u
namespace PaperVerification.ToricCharacters
open AddMonoidAlgebra
open scoped BigOperators Classical
variable (k : Type*) [CommRing k]
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]
def fullCoordinateFunctionsEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι → ℕ) where
  toFun x i := (b.repr (x : E) i).toNat
  invFun x := ⟨b.equivFun.symm (fun i => (x i : ℤ)), by
    intro i hi
    change 0 ≤ b.equivFun (b.equivFun.symm _) i
    rw [b.equivFun.apply_symm_apply]
    exact Int.natCast_nonneg _⟩
  left_inv x := by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rw [b.equivFun.apply_symm_apply]
    exact Int.toNat_of_nonneg (x.property i (Finset.mem_univ i))
  right_inv x := by
    funext i
    change (b.equivFun (b.equivFun.symm _) i).toNat = x i
    rw [b.equivFun.apply_symm_apply, Int.toNat_natCast]
  map_add' x y := by
    funext i
    change (b.repr ((x : E) + (y : E)) i).toNat =
      (b.repr (x : E) i).toNat + (b.repr (y : E) i).toNat
    rw [map_add, Finsupp.add_apply, Int.toNat_add
      (x.property i (Finset.mem_univ i)) (y.property i (Finset.mem_univ i))]

def fullCoordinateFinsuppEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι →₀ ℕ) :=
  (fullCoordinateFunctionsEquiv b).trans (naturalFunctionFinsuppEquiv ι)

theorem basis_mem_fullCoordinateCone (b : Module.Basis ι ℤ E) (i : ι) :
    b i ∈ coordinateConeMonoid b Finset.univ := by
  intro j hj
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem fullCoordinateFinsuppEquiv_basis (b : Module.Basis ι ℤ E) (i : ι) :
    fullCoordinateFinsuppEquiv b ⟨b i, basis_mem_fullCoordinateCone b i⟩ =
      Finsupp.single i 1 := by
  ext j
  simp [fullCoordinateFinsuppEquiv, fullCoordinateFunctionsEquiv,
    naturalFunctionFinsuppEquiv, Module.Basis.repr_self_apply]
  by_cases hij : i = j <;> simp [Finsupp.single_apply, hij]

def fullChartPolynomialEquiv (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) ≃ₐ[k] MvPolynomial ι k :=
  (monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)).symm.trans
    (AddMonoidAlgebra.domCongr k k (fullCoordinateFinsuppEquiv b))

@[simp] theorem fullChartPolynomialEquiv_character (b : Module.Basis ι ℤ E) (i : ι) :
    fullChartPolynomialEquiv k b
      (chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i)) = MvPolynomial.X i := by
  have hchar : monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)
      (single ⟨b i, basis_mem_fullCoordinateCone b i⟩ 1) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) := by
    apply Subtype.ext
    exact monoidChartMap_single k _ _ _
  rw [fullChartPolynomialEquiv, AlgEquiv.trans_apply, ← hchar,
    AlgEquiv.symm_apply_apply, AddMonoidAlgebra.domCongr_single,
    fullCoordinateFinsuppEquiv_basis]
  rfl

@[simp] theorem fullChartPolynomialEquiv_symm_X (b : Module.Basis ι ℤ E) (i : ι) :
    (fullChartPolynomialEquiv k b).symm (MvPolynomial.X i) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) :=
  (fullChartPolynomialEquiv k b).symm_apply_eq.mpr
    (fullChartPolynomialEquiv_character k b i).symm


end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan
open AlgebraicGeometry CategoryTheory AddMonoidAlgebra
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical
variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
def fullCharacterBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℤ (Lattice n) :=
  integralDualBasis («Σ».fullConeBasis s)

theorem fullChart_semigroup_eq (s : «Σ».fullCones) :
    dualConeMonoid s.val = coordinateConeMonoid («Σ».fullCharacterBasis s) Finset.univ := by
  rw [«Σ».fullConeBasis_ray_set s, dualConeMonoid_basis_eq]
  rfl

def fullChartCoordinate (s : «Σ».fullCones) (i : Fin n) :
    monoidChartAlgebra k (dualConeMonoid s.val) :=
  chartCharacter k _ («Σ».fullCharacterBasis s i) (by
    rw [«Σ».fullChart_semigroup_eq]
    exact basis_mem_fullCoordinateCone _ i)

def fullChartPolynomialPresentation (s : «Σ».fullCones) :
    MvPolynomial (Fin n) k ≃ₐ[k] monoidChartAlgebra k (dualConeMonoid s.val) :=
  (fullChartPolynomialEquiv k («Σ».fullCharacterBasis s)).symm.trans
    (Subalgebra.equivOfEq _ _
      (congrArg (monoidChartAlgebra k) («Σ».fullChart_semigroup_eq s)).symm)

@[simp] theorem fullChartPolynomialPresentation_X (s : «Σ».fullCones) (i : Fin n) :
    «Σ».fullChartPolynomialPresentation k s (MvPolynomial.X i) =
      «Σ».fullChartCoordinate k s i := by
  apply Subtype.ext
  rw [fullChartPolynomialPresentation, AlgEquiv.trans_apply,
    fullChartPolynomialEquiv_symm_X]
  rfl


end PaperVerification.ToricGeometry.SmoothCompleteFan
end FanDimensionCoordinates

section Source_ToricFanDimension

/-!
# The actual dimension of a smooth complete fan scheme

Full cones give actual open affine charts with polynomial coordinate
rings in `n` variables. Their union is the whole scheme. The upper
dimension bound follows from preservation of point coheight under open
immersions; the lower bound follows from any one of those open charts.
Thus the rank parameter is identified with ordinary topological Krull
dimension, including rank zero.
-/


universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry TopologicalSpace

theorem scheme_topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X := by
  change Order.krullDim (IrreducibleCloseds X) = Order.krullDim X
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fullChart_ringKrullDim (s : «Σ».fullCones) :
    ringKrullDim (monoidChartAlgebra k (dualConeMonoid s.val)) = n := by
  rw [← ringKrullDim_eq_of_ringEquiv
    («Σ».fullChartPolynomialPresentation k s).toRingEquiv]
  simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add]

theorem fullChart_topologicalKrullDim (s : «Σ».fullCones) :
    topologicalKrullDim (coneChart k s.val) = n := by
  change topologicalKrullDim
    (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val))) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    «Σ».fullChart_ringKrullDim k s]

theorem fanScheme_orderKrullDim_le (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) ≤ n := by
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨s, y, rfl⟩ := «Σ».fullChartOpen_cover k hpure x
  rw [coheight_eq_of_isOpenImmersion]
  erw [← idealHeight_eq_coheight (CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid s.val)))
      (show Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))) from y)]
  have h := Ideal.height_le_ringKrullDim_of_ne_top y.isPrime.ne_top
  have hd : ringKrullDim
      (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val)) = n :=
    «Σ».fullChart_ringKrullDim k s
  rw [hd] at h
  exact h

/-- Dimension means chains of actual irreducible closed subsets of the
glued scheme, rather than a separately assigned lattice-rank invariant. -/
theorem fanScheme_topologicalKrullDim (hpure : «Σ».IsPure) :
    topologicalKrullDim («Σ».fanScheme k) = n := by
  apply le_antisymm
  · rw [scheme_topologicalKrullDim_eq_orderKrullDim]
    exact «Σ».fanScheme_orderKrullDim_le k hpure
  · obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
    let s' : «Σ».fullCones := ⟨s, hs⟩
    have h := ((«Σ».fanChartMap k («Σ».fullConeIndex s')).isOpenEmbedding.isEmbedding.isInducing).topologicalKrullDim_le
    change topologicalKrullDim (coneChart k s'.val) ≤
      topologicalKrullDim («Σ».fanScheme k) at h
    simpa only [«Σ».fullChart_topologicalKrullDim k s'] using h

theorem fanScheme_orderKrullDim (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) = n := by
  rw [← scheme_topologicalKrullDim_eq_orderKrullDim,
    «Σ».fanScheme_topologicalKrullDim k hpure]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_topologicalKrullDim

end Source_ToricFanDimension

end

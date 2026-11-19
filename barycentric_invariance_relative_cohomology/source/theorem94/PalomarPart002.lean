module

public import theorem94.PalomarPart001
import all theorem94.PalomarPart001
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega
public meta import Mathlib.Tactic.Ring.Basic

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


-- Restore the original anonymous enclosing source scopes at this boundary.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
/- BEGIN FourPapers/Universal/CyclicFixedFaceRestriction.lean -/
section

section
/-! # Naturality of the actual fixed-face quotient

Restriction to a union of full prime orbits is the existing Boolean face
restriction.  Its square with the fixed-face quotient commutes on literal
monomial coefficients, and consequently restricts the actual kernel.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime]
variable {W U : Type*} [Fintype W] [Fintype U]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq U := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × U) := Classical.decEq _

theorem primeFixedFaceEmbedding_embedding (i : U ↪ W) (F : BooleanFace U) :
    booleanFaceEmbedding (primeOrbitEmbedding p i) (primeFixedFaceEmbedding p F) =
      primeFixedFaceEmbedding p (booleanFaceEmbedding i F) := by
  apply Subtype.ext
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hv
    apply (mem_primeFixedFaceEmbedding p (booleanFaceEmbedding i F) v.1 v.2).mpr
    refine Finset.mem_map.mpr ⟨u.2, (mem_primeFixedFaceEmbedding p F u.1 u.2).mp hu, ?_⟩
    exact congrArg (fun z : ZMod p × W => z.2) he
  · intro hv
    have hw := (mem_primeFixedFaceEmbedding p (booleanFaceEmbedding i F) v.1 v.2).mp hv
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hw
    exact Finset.mem_map.mpr ⟨(v.1, u),
      (mem_primeFixedFaceEmbedding p F v.1 u).mpr hu, Prod.ext rfl he⟩

theorem primeFixedFaceQuotient_restriction (i : U ↪ W)
    (x : BooleanBarycentricRing (ZMod p × W) K) :
    primeFixedFaceQuotient p K (booleanRestriction (primeOrbitEmbedding p i) x) =
      booleanRestriction i (primeFixedFaceQuotient p K x) := by
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  rw [primeFixedFaceQuotient_coefficient, booleanRestriction_coefficient,
    booleanRestriction_coefficient, primeFixedFaceQuotient_coefficient]
  congr 1
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding (primeOrbitEmbedding p i))
      (a.val.mapDomain (primeFixedFaceEmbedding p)) =
    Finsupp.mapDomain (primeFixedFaceEmbedding p)
      (a.val.mapDomain (booleanFaceEmbedding i))
  rw [← Finsupp.mapDomain_fun_comp, ← Finsupp.mapDomain_fun_comp]
  apply Finsupp.mapDomain_congr
  intro F hF
  exact primeFixedFaceEmbedding_embedding p i F

def primeFixedFaceKernelRestriction (i : U ↪ W) :
    PrimeFixedFaceKernel (W := W) p K →ₗ[K] PrimeFixedFaceKernel (W := U) p K where
  toFun x := ⟨booleanRestriction (primeOrbitEmbedding p i) x.val, by
    change primeFixedFaceQuotient p K (booleanRestriction (primeOrbitEmbedding p i) x.val) = 0
    rw [primeFixedFaceQuotient_restriction]
    have hx : primeFixedFaceQuotient p K x.val = 0 := x.property
    rw [hx, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicControlledKernel.lean -/
section

section
/-! # The simultaneous boundary and fixed-face kernel

Multiplication by the top face identifies the fixed-face kernel with the
kernel of both the proper boundary map and the fixed-face quotient. The
proof uses the actual quotient and regularity of the top variable in its
target, over an arbitrary commutative coefficient ring.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical

section OrdinaryTopDegree
variable {V K : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [CommRing K]

theorem booleanTopOrdinary_shift_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem booleanTopOrdinary_degree_shift (a : BooleanFace V →₀ ℕ) :
    booleanOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      booleanOrdinaryDegree a + Fintype.card V := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])]
  simp [booleanTopFace]

theorem booleanTopOrdinary_predecessor_degree (m : ℕ) (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (m + Fintype.card V)) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ m + Fintype.card V := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [booleanTopOrdinary_degree_shift]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [booleanTopOrdinary_shift_coefficient] at hh

theorem booleanTopOrdinary_homogeneous_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ n := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [booleanTopOrdinary_degree_shift]
    omega
  have hh := hx b hb
  rw [booleanTopOrdinary_shift_coefficient] at hh
  exact hh

theorem booleanTopOrdinary_mul_degree (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (n + Fintype.card V) := by
  intro b hb
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
    (monomialCoordinate IsChainExponent booleanTopFace * x) b = 0
  rw [monomialCoordinate_mul_repr IsChainExponent isChainExponent_divisorClosed
    booleanTopFace booleanTop_isFreeCoordinate]
  by_cases hr : b ∈ Set.range
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate)
  · obtain ⟨a, rfl⟩ := hr
    rw [Finsupp.mapDomain_apply_of_injective
      (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate)]
    apply hx a
    intro ha
    change booleanOrdinaryDegree a.val = n at ha
    apply hb
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) = _
    rw [booleanTopOrdinary_degree_shift, ha]
  · exact Finsupp.mapDomain_of_notMem_range _ _ hr

end OrdinaryTopDegree

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

theorem primeFixedFaceEmbedding_top :
    primeFixedFaceEmbedding (W := W) p booleanTopFace = booleanTopFace := by
  apply Subtype.ext
  ext x
  simp only [primeFixedFaceEmbedding_val, booleanTopFace_val, Finset.mem_product,
    Finset.mem_univ, and_self]

@[simp] theorem primeFixedFaceQuotient_top :
    primeFixedFaceQuotient (W := W) p K booleanTop = booleanTop := by
  have h := primeFixedFaceQuotient_face (W := W) p K booleanTopFace
  rw [primeFixedFaceEmbedding_top] at h
  exact h

/-- Both equations are literal kernels of the two algebra maps. -/
def PrimeControlledKernel : Submodule K (BooleanBarycentricRing (ZMod p × W) K) :=
  LinearMap.ker (booleanBoundaryMap (V := ZMod p × W) (K := K)).toLinearMap ⊓
    PrimeFixedFaceKernel p K

theorem mem_primeControlledKernel_iff (x : BooleanBarycentricRing (ZMod p × W) K) :
    x ∈ PrimeControlledKernel p K ↔
      booleanBoundaryMap x = 0 ∧ primeFixedFaceQuotient p K x = 0 := Iff.rfl

theorem primeControlledKernel_eq_top_kernel
    (x : BooleanBarycentricRing (ZMod p × W) K) :
    x ∈ PrimeControlledKernel p K ↔
      ∃ y : PrimeFixedFaceKernel (W := W) p K, booleanTop * y.val = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hx.1
    have hπ : primeFixedFaceQuotient p K y = 0 := by
      apply (booleanTop_mul_injective (V := W) (K := K))
      change booleanTop * primeFixedFaceQuotient p K y = booleanTop * (0 : BooleanBarycentricRing W K)
      rw [mul_zero]
      calc
        booleanTop * primeFixedFaceQuotient p K y =
            primeFixedFaceQuotient p K (booleanTop * y) := by
          rw [map_mul, primeFixedFaceQuotient_top]
        _ = 0 := by rw [hy]; exact hx.2
    exact ⟨⟨y, hπ⟩, hy⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(booleanBoundaryMap_eq_zero_iff _).mpr ⟨y.val, rfl⟩, ?_⟩
    change primeFixedFaceQuotient p K (booleanTop * y.val) = 0
    rw [map_mul, show primeFixedFaceQuotient p K y.val = 0 from y.property, mul_zero]

def primeControlledKernelTopMap : PrimeFixedFaceKernel (W := W) p K →ₗ[K]
    PrimeControlledKernel (W := W) p K where
  toFun y := ⟨booleanTop * y.val, (primeControlledKernel_eq_top_kernel p K _).mpr ⟨y, rfl⟩⟩
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' c y := by
    apply Subtype.ext
    change booleanTop * (c • y.val) = c • (booleanTop * y.val)
    rw [mul_smul_comm]

theorem primeControlledKernelTopMap_bijective :
    Function.Bijective (primeControlledKernelTopMap (W := W) p K) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact booleanTop_mul_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := (primeControlledKernel_eq_top_kernel p K x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩

def primeControlledKernelTopEquiv : PrimeFixedFaceKernel (W := W) p K ≃ₗ[K]
    PrimeControlledKernel (W := W) p K :=
  LinearEquiv.ofBijective (primeControlledKernelTopMap p K)
    (primeControlledKernelTopMap_bijective p K)

@[simp] theorem primeControlledKernelTopEquiv_apply (y : PrimeFixedFaceKernel (W := W) p K) :
    (primeControlledKernelTopEquiv p K y).val = booleanTop * y.val := rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOneDegreeLift.lean -/
section


section

/-! # The equivariant correction in one homogeneous degree

This is the exact extension step in Lemma 8.1.  It keeps both the prescribed
quotient map and the already constructed map on a split subspace.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

/-- Restriction of a representation to an invariant submodule. -/
def invariantSubmoduleRepresentation (ρ : CyclicRepresentation K G M)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U) :
    CyclicRepresentation K G U where
  toFun g :=
    { toFun := fun x => ⟨ρ g x.val, hU g x.val x.property⟩
      map_add' := by intros; apply Subtype.ext; simp
      map_smul' := by intros; apply Subtype.ext; simp }
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    exact congrArg (fun f : M →ₗ[K] M => f x.val) (ρ.map_mul g h)

@[simp] theorem invariantSubmoduleRepresentation_apply
    (ρ : CyclicRepresentation K G M) (U : Submodule K M)
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (g : G) (x : U) :
    (invariantSubmoduleRepresentation ρ U hU g x).val = ρ g x.val := rfl

theorem kernel_invariant_of_intertwines
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (f : M →ₗ[K] N) (hf : RepresentationIntertwines ρ τ f) :
    ∀ g x, x ∈ LinearMap.ker f → ρ g x ∈ LinearMap.ker f := by
  intro g x hx
  change f (ρ g x) = 0
  rw [hf, LinearMap.mem_ker.mp hx, map_zero]

/-- Correct an equivariant preliminary lift by a map into its kernel.  The
kernel's regular-orbit coordinates supply the relative-injectivity step. -/
theorem equivariant_lift_extend_subspace
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (U : Submodule K M) (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (s : M →ₗ[K] U) (hs : s.comp U.subtype = LinearMap.id)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (β : M →ₗ[K] N)
    (hβ : RepresentationIntertwines ρ τ β) (hqβ : q.comp β = a)
    (f : U →ₗ[K] N)
    (hf : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU) τ f)
    (hqf : q.comp f = a.comp U.subtype)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ L : M →ₗ[K] N,
      RepresentationIntertwines ρ τ L ∧ L.comp U.subtype = f ∧ q.comp L = a := by
  let δ : U →ₗ[K] LinearMap.ker q :=
    LinearMap.codRestrict (LinearMap.ker q) (f - β.comp U.subtype) (by
      intro x
      change q (f x - β x.val) = 0
      rw [map_sub]
      have h1 := congrArg (fun z : U →ₗ[K] Q => z x) hqf
      have h2 := congrArg (fun z : M →ₗ[K] Q => z x.val) hqβ
      exact sub_eq_zero.mpr (h1.trans h2.symm))
  have hδ : RepresentationIntertwines (invariantSubmoduleRepresentation ρ U hU)
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) δ := by
    intro g x
    apply Subtype.ext
    change f (invariantSubmoduleRepresentation ρ U hU g x) - β (ρ g x.val) =
      τ g (f x - β x.val)
    rw [hf, hβ, map_sub]
  have hi : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρ U hU) ρ U.subtype := by
    intro g x
    rfl
  obtain ⟨D, hD, hDi⟩ := exists_equivariantExtension_of_coinduced
    (invariantSubmoduleRepresentation ρ U hU) ρ
    (invariantSubmoduleRepresentation τ (LinearMap.ker q)
      (kernel_invariant_of_intertwines τ υ q hq)) e he U.subtype s hi hs δ hδ
  refine ⟨β + (LinearMap.ker q).subtype.comp D, ?_, ?_, ?_⟩
  · intro g x
    change β (ρ g x) + (D (ρ g x)).val = τ g (β x + (D x).val)
    rw [hβ, hD, map_add]
    rfl
  · ext x
    have hd := congrArg (fun z : U →ₗ[K] LinearMap.ker q => (z x).val) hDi
    change β x.val + (D x.val).val = f x
    change (D x.val).val = f x - β x.val at hd
    rw [hd, ← add_sub_assoc, add_comm (β x.val) (f x)]
    exact add_sub_cancel_right (f x) (β x.val)
  · ext x
    have hx := (D x).property
    change q (D x).val = 0 at hx
    change q (β x + (D x).val) = a x
    rw [map_add, hx, add_zero]
    exact congrArg (fun z : M →ₗ[K] Q => z x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousBasisCoinduction.lean -/
section


section

/-! # Coinduced coordinates on actual homogeneous basis pieces

The homogeneous module is the submodule defined by vanishing of all basis
coefficients outside its stated degree. A free permutation action on the
finite degree-index set therefore identifies that genuine submodule with a
product of regular function modules. These coordinates apply in particular
to the original chain-monomial basis of a fixed-face quotient kernel.
-/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

universe uK uM uI uG

variable {K : Type uK} {M : Type uM} {I : Type uI} [CommRing K] [AddCommGroup M] [Module K M]
variable (b : Module.Basis I K M) (degree : I → ℕ)

abbrev BasisDegreeIndex (n : ℕ) := {i : I // degree i = n}

def basisDegreeSupportedEquiv (n : ℕ) :
    basisOrdinaryDegreePiece b degree n ≃ₗ[K] Finsupp.supported K K {i | degree i = n} where
  toFun x := ⟨b.repr x.val, by
    rw [Finsupp.mem_supported']
    exact x.property⟩
  invFun x := ⟨b.repr.symm x.val, by
    intro i hi
    rw [LinearEquiv.apply_symm_apply]
    exact (Finsupp.mem_supported' K x.val).mp x.property i hi⟩
  left_inv x := by apply Subtype.ext; exact b.repr.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact b.repr.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact b.repr.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact b.repr.map_smul c x.val

def basisDegreeFunctionCoordinates (n : ℕ) [Finite (BasisDegreeIndex degree n)] :
    basisOrdinaryDegreePiece b degree n ≃ₗ[K] (BasisDegreeIndex degree n → K) :=
  (basisDegreeSupportedEquiv b degree n).trans
    ((Finsupp.supportedEquivFinsupp {i | degree i = n}).trans
      (Finsupp.linearEquivFunOnFinite K K (BasisDegreeIndex degree n)))

@[simp] theorem basisDegreeFunctionCoordinates_apply (n : ℕ)
    [Finite (BasisDegreeIndex degree n)]
    (x : basisOrdinaryDegreePiece b degree n) (i : BasisDegreeIndex degree n) :
    basisDegreeFunctionCoordinates b degree n x i = b.repr x.val i.val := rfl

section Action
variable {G : Type uG} [Group G] [MulAction G I]
variable (ρ : CyclicRepresentation K G M)
variable (hdegree : ∀ (g : G) i, degree (g • i) = degree i)
variable (hcoeff : ∀ (g : G) x i, b.repr (ρ g x) i = b.repr x (g⁻¹ • i))

include hdegree hcoeff in
theorem basisDegreePiece_invariant (n : ℕ) (g : G) (x : M)
    (hx : x ∈ basisOrdinaryDegreePiece b degree n) :
    ρ g x ∈ basisOrdinaryDegreePiece b degree n := by
  intro i hi
  rw [hcoeff]
  exact hx (g⁻¹ • i) (by rwa [hdegree])

def basisDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (basisOrdinaryDegreePiece b degree n) :=
  invariantSubmoduleRepresentation ρ (basisOrdinaryDegreePiece b degree n)
    (basisDegreePiece_invariant b degree ρ hdegree hcoeff n)

def basisDegreeIndexMulAction (n : ℕ) : MulAction G (BasisDegreeIndex degree n) where
  smul g i := ⟨g • i.val, (hdegree g i.val).trans i.property⟩
  one_smul i := Subtype.ext (one_smul G i.val)
  mul_smul g h i := Subtype.ext (mul_smul g h i.val)

theorem basisDegreeFunctionCoordinates_equivariant (n : ℕ)
    [Finite (BasisDegreeIndex degree n)] :
    letI := basisDegreeIndexMulAction degree hdegree n
    RepresentationIntertwines (basisDegreeRepresentation b degree ρ hdegree hcoeff n)
      permutationFunctionRepresentation (basisDegreeFunctionCoordinates b degree n).toLinearMap := by
  letI := basisDegreeIndexMulAction degree hdegree n
  intro g x
  funext i
  exact hcoeff g x.val i.val

/-- No semisimplicity is used: the degree piece is a product of regular
modules because its actual basis action is free. -/
theorem basisDegreePiece_isCoinduced (n : ℕ)
    [Finite (BasisDegreeIndex degree n)]
    (hfree : ∀ (g : G) (i : I), degree i = n → g • i = i → g = 1) :
    ∃ J : Type uI, ∃ e : basisOrdinaryDegreePiece b degree n ≃ₗ[K] (G → J → K),
      RepresentationIntertwines (basisDegreeRepresentation b degree ρ hdegree hcoeff n)
        coinducedRepresentation e.toLinearMap := by
  letI := basisDegreeIndexMulAction degree hdegree n
  have hf : ∀ (g : G) (i : BasisDegreeIndex degree n), g • i = i → g = 1 := by
    intro g i hi
    exact hfree g i.val i.property (congrArg Subtype.val hi)
  let e := (basisDegreeFunctionCoordinates b degree n).trans
    (freePermutationCoinducedEquiv (K := K) hf)
  refine ⟨MulAction.orbitRel.Quotient G (BasisDegreeIndex degree n), e, ?_⟩
  intro g x
  change freePermutationCoinducedEquiv hf
      (basisDegreeFunctionCoordinates b degree n
        (basisDegreeRepresentation b degree ρ hdegree hcoeff n g x)) = _
  exact (congrArg (freePermutationCoinducedEquiv hf)
    (basisDegreeFunctionCoordinates_equivariant b degree ρ hdegree hcoeff n g x)).trans
    (freePermutationCoinducedEquiv_equivariant hf g
      (basisDegreeFunctionCoordinates b degree n x))

end Action
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedKernelHomogeneous.lean -/
section


section

/-! # Homogeneous coordinates in the genuine fixed-face kernel

The fixed-face kernel uses the original chain monomials. Its degree pieces
are finite because every nonempty face has positive rank. The homogeneous
projection below is the already defined literal coefficient projection,
restricted to the actual ordinary-degree submodule.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

section FiniteDegree
variable {V : Type*} [Fintype V]

local instance (priority := 2000) : DecidableEq V := Classical.decEq _

theorem chainExponent_degree_le_ordinary (a : BooleanFace V →₀ ℕ) :
    a.degree ≤ booleanOrdinaryDegree a := by
  change a.sum (fun _ m => m) ≤ a.sum (fun F m => m * F.val.card)
  apply Finsupp.sum_le_sum
  intro F hF
  exact Nat.le_mul_of_pos_right (a F) (Finset.card_pos.mpr F.property)

noncomputable instance booleanHomogeneousChainFinite (n : ℕ) :
    Finite {a : BooleanChainExponent V // booleanOrdinaryDegree a.val = n} := by
  letI : Fintype {a : BooleanFace V →₀ ℕ // a.degree ≤ n} :=
    (Finsupp.finite_of_degree_le n).fintype
  let f : {a : BooleanChainExponent V // booleanOrdinaryDegree a.val = n} →
      {a : BooleanFace V →₀ ℕ // a.degree ≤ n} := fun a =>
    ⟨a.val.val, (chainExponent_degree_le_ordinary a.val.val).trans_eq a.property⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh)

end FiniteDegree

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

def primeFixedKernelDegree (a : PrimeFixedFaceKernelIndex (W := W) p) : ℕ :=
  booleanOrdinaryDegree a.val.val

noncomputable instance primeFixedKernelDegreeFinite (n : ℕ) :
    Finite (BasisDegreeIndex (primeFixedKernelDegree (W := W) p) n) := by
  let f : BasisDegreeIndex (primeFixedKernelDegree (W := W) p) n →
      {a : BooleanChainExponent (ZMod p × W) // booleanOrdinaryDegree a.val = n} :=
    fun a => ⟨a.val.val, a.property⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh)

@[simp] theorem primeFixedFaceKernelBasis_repr
    (x : PrimeFixedFaceKernel (W := W) p K) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    (primeFixedFaceKernelBasis p K).repr x a =
      (booleanChainBasis (K := K)).repr x.val a.val := by
  change (primeFixedFaceKernelCoordinates p K x) a = _
  exact primeFixedFaceKernelCoordinates_apply p K x a

/-- This is the ordinary homogeneous piece of the actual quotient kernel. -/
abbrev PrimeFixedKernelDegreePiece (n : ℕ) :=
  basisOrdinaryDegreePiece (primeFixedFaceKernelBasis (W := W) p K)
    (primeFixedKernelDegree p) n

theorem mem_primeFixedKernelDegreePiece_iff (n : ℕ)
    (x : PrimeFixedFaceKernel (W := W) p K) :
    x ∈ PrimeFixedKernelDegreePiece p K n ↔
      x.val ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n := by
  constructor
  · intro hx a ha
    by_cases hr : a ∈ Set.range (primeFixedChainEmbedding (W := W) p)
    · exact (primeFixedFaceKernel_mem_iff_range p K x.val).mp x.property a hr
    · have hh := hx ⟨a, hr⟩ ha
      exact (primeFixedFaceKernelBasis_repr p K x ⟨a, hr⟩).symm.trans hh
  · intro hx a ha
    rw [primeFixedFaceKernelBasis_repr]
    exact hx a.val ha

def primeFixedKernelDegreeProjection (n : ℕ) :
    basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n →ₗ[K] PrimeFixedKernelDegreePiece (W := W) p K n where
  toFun x := ⟨primeFixedFaceKernelProjection p K x.val,
    (mem_primeFixedKernelDegreePiece_iff p K n _).mpr
      (primeFixedFaceKernelProjection_degree p K n x.val x.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact (primeFixedFaceKernelProjection p K).map_add x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact (primeFixedFaceKernelProjection p K).map_smul c x.val

@[simp] theorem primeFixedKernelDegreeProjection_retract (n : ℕ)
    (x : PrimeFixedKernelDegreePiece (W := W) p K n) :
    primeFixedKernelDegreeProjection p K n
      ⟨x.val.val, (mem_primeFixedKernelDegreePiece_iff p K n x.val).mp x.property⟩ = x := by
  apply Subtype.ext
  exact primeFixedFaceKernelProjection_retract p K x.val

/-- Finite coordinates for the genuine homogeneous kernel, ready for the
free-orbit regular-module equivalence. -/
def primeFixedKernelDegreeCoordinates (n : ℕ) :
    PrimeFixedKernelDegreePiece (W := W) p K n ≃ₗ[K]
      (BasisDegreeIndex (primeFixedKernelDegree (W := W) p) n → K) :=
  basisDegreeFunctionCoordinates (primeFixedFaceKernelBasis p K) (primeFixedKernelDegree p) n

@[simp] theorem primeFixedKernelDegreeCoordinates_apply (n : ℕ)
    (x : PrimeFixedKernelDegreePiece (W := W) p K n)
    (a : BasisDegreeIndex (primeFixedKernelDegree (W := W) p) n) :
    primeFixedKernelDegreeCoordinates p K n x a =
      (booleanChainBasis (K := K)).repr x.val.val a.val.val := by
  rw [primeFixedKernelDegreeCoordinates, basisDegreeFunctionCoordinates_apply,
    primeFixedFaceKernelBasis_repr]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeOrbitCoordinates.lean -/
section

section
/-! # Prime-orbit coordinates and the actual quotient action

The second coordinate is the literal subgroup orbit, not a separate chosen
label action. Consequently the action on labels in the moment retraction
agrees with the free quotient-group action used by induction.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

variable {G V : Type*} [CommGroup G] [MulAction G V]
variable (Z : Subgroup G)
variable (hf : ∀ (g : G) (v : V), g • v = v → g = 1)

theorem subgroupOrbitCoordinates_class (z : Z) (q : SubgroupOrbit (V := V) Z) :
    (Quotient.mk'' (subgroupOrbitCoordinates Z hf (z, q)) : SubgroupOrbit Z) = q := by
  change (Quotient.mk'' (z • q.out) : SubgroupOrbit Z) = q
  calc
    _ = Quotient.mk'' q.out := MulAction.orbitRel.Quotient.quotient_smul_eq
    _ = q := Quotient.out_eq' q

theorem subgroupOrbitCoordinates_symm_snd (v : V) :
    ((subgroupOrbitCoordinates Z hf).symm v).2 =
      (Quotient.mk'' v : SubgroupOrbit Z) := by
  have h := subgroupOrbitCoordinates_class Z hf
    ((subgroupOrbitCoordinates Z hf).symm v).1
    ((subgroupOrbitCoordinates Z hf).symm v).2
  rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

variable (p : ℕ) [Fact p.Prime] [Fintype V]
variable (eZ : Multiplicative (ZMod p) ≃* Z)

def primeOrbitCoordinates : (ZMod p × SubgroupOrbit (V := V) Z) ≃ V :=
  (Equiv.prodCongr eZ.toEquiv (Equiv.refl _)).trans (subgroupOrbitCoordinates Z hf)

@[simp] theorem primeOrbitCoordinates_apply (x : ZMod p) (q : SubgroupOrbit (V := V) Z) :
    primeOrbitCoordinates Z hf p eZ (x, q) = (eZ (Multiplicative.ofAdd x)).val • q.out := rfl

theorem primeOrbitCoordinates_class (x : ZMod p) (q : SubgroupOrbit (V := V) Z) :
    (Quotient.mk'' (primeOrbitCoordinates Z hf p eZ (x, q)) : SubgroupOrbit Z) = q :=
  subgroupOrbitCoordinates_class Z hf (eZ (Multiplicative.ofAdd x)) q

theorem primeOrbitCoordinates_symm_snd (v : V) :
    ((primeOrbitCoordinates Z hf p eZ).symm v).2 =
      (Quotient.mk'' v : SubgroupOrbit Z) :=
  subgroupOrbitCoordinates_symm_snd Z hf v

theorem primeOrbitCoordinates_translate (t : ZMod p)
    (v : ZMod p × SubgroupOrbit (V := V) Z) :
    primeOrbitCoordinates Z hf p eZ (t + v.1, v.2) =
      (eZ (Multiplicative.ofAdd t)).val • primeOrbitCoordinates Z hf p eZ v := by
  change (eZ (Multiplicative.ofAdd t * Multiplicative.ofAdd v.1)).val • v.2.out = _
  rw [eZ.map_mul, Subgroup.coe_mul, mul_smul]
  rfl

def primeOrbitCoordinatePermutation : G →* Equiv.Perm (ZMod p × SubgroupOrbit (V := V) Z) :=
  (primeOrbitCoordinates Z hf p eZ).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom G V)

@[simp] theorem primeOrbitCoordinatePermutation_apply (g : G)
    (v : ZMod p × SubgroupOrbit (V := V) Z) :
    primeOrbitCoordinatePermutation Z hf p eZ g v =
      (primeOrbitCoordinates Z hf p eZ).symm (g • primeOrbitCoordinates Z hf p eZ v) := rfl

/-- The prime subgroup acts in these coordinates by the literal translations
used in the fixed-face quotient and its free kernel basis. -/
theorem primeOrbitCoordinatePermutation_translation (t : ZMod p) :
    primeOrbitCoordinatePermutation Z hf p eZ (eZ (Multiplicative.ofAdd t)).val =
      primeOrbitRelabel p (Equiv.refl (SubgroupOrbit (V := V) Z)) (fun _ => t) := by
  apply Equiv.ext
  intro v
  apply (primeOrbitCoordinates Z hf p eZ).injective
  rw [primeOrbitCoordinatePermutation_apply, Equiv.apply_symm_apply]
  change (eZ (Multiplicative.ofAdd t)).val • primeOrbitCoordinates Z hf p eZ v =
    primeOrbitCoordinates Z hf p eZ (t + v.1, v.2)
  exact (primeOrbitCoordinates_translate Z hf p eZ t v).symm

theorem primeOrbitCoordinatePermutation_hasTranslations :
    ∀ t : ZMod p, ∃ z : Z,
      primeOrbitCoordinatePermutation Z hf p eZ z.val =
        primeOrbitRelabel p (Equiv.refl (SubgroupOrbit (V := V) Z)) (fun _ => t) := by
  intro t
  exact ⟨eZ (Multiplicative.ofAdd t),
    primeOrbitCoordinatePermutation_translation Z hf p eZ t⟩

theorem primeOrbitCoordinatePermutation_commutes (g : G) :
    CommutesPrimeTranslations p (primeOrbitCoordinatePermutation Z hf p eZ g) := by
  intro t v
  apply (primeOrbitCoordinates Z hf p eZ).injective
  rw [primeOrbitCoordinatePermutation_apply, Equiv.apply_symm_apply]
  rw [primeOrbitCoordinates_translate, primeOrbitCoordinates_translate,
    primeOrbitCoordinatePermutation_apply, Equiv.apply_symm_apply]
  rw [smul_smul, smul_smul, mul_comm]

/-- The label action extracted from the centralizer normal form is exactly
the action of the quotient group on the actual subgroup orbit set. -/
theorem primeOrbitCoordinatePermutation_label (g : G) (q : SubgroupOrbit (V := V) Z) :
    letI := quotientOrbitAction (V := V) Z
    primeOrbitParentAction p (primeOrbitCoordinatePermutation Z hf p eZ)
      (primeOrbitCoordinatePermutation_commutes Z hf p eZ) g q =
        (QuotientGroup.mk g : G ⧸ Z) • q := by
  letI := quotientOrbitAction (V := V) Z
  change (primeOrbitCoordinatePermutation Z hf p eZ g (0, q)).2 = _
  rw [primeOrbitCoordinatePermutation_apply, primeOrbitCoordinates_symm_snd]
  rw [← quotientOrbitAction_mk, primeOrbitCoordinates_class]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedBasis.lean -/
section


section

/-! # Homogeneous free bases for equivariant lifting

The two bases below are the parameter basis and the coefficient basis of a
graded free module.  In the application they are `booleanColorBasis` and
`booleanParameterBasis`.  The degree properties express positivity of the
parameters, and are proved from their actual color multidegrees.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable (K A M I J : Type*) [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

structure ScalarGradedBasis where
  parameterBasis : Module.Basis I A M
  coefficientBasis : Module.Basis J K M
  generatorDegree : I → ℕ
  degree : J → ℕ
  parent : J → I
  multiplier : J → A
  coefficient_eq : ∀ j, coefficientBasis j = multiplier j • parameterBasis (parent j)
  parent_degree_le : ∀ j, generatorDegree (parent j) ≤ degree j
  equal_degree_eq : ∀ j, degree j = generatorDegree (parent j) →
    coefficientBasis j = parameterBasis (parent j)
  generator_homogeneous : ∀ i j, degree j ≠ generatorDegree i →
    coefficientBasis.repr (parameterBasis i) j = 0

namespace ScalarGradedBasis

variable {K A M I J}
variable (s : ScalarGradedBasis K A M I J)

def piece (n : ℕ) : Submodule K M :=
  basisOrdinaryDegreePiece s.coefficientBasis s.degree n

def cut (n : ℕ) : Submodule A M :=
  Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n})

theorem generator_mem_piece (i : I) :
    s.parameterBasis i ∈ s.piece (s.generatorDegree i) :=
  s.generator_homogeneous i

theorem coefficient_mem_piece (j : J) : s.coefficientBasis j ∈ s.piece (s.degree j) := by
  intro k hk
  rw [Module.Basis.repr_self]
  have hne : j ≠ k := by
    intro h
    subst k
    exact hk rfl
  simp [Finsupp.single_apply, hne]

theorem generator_mem_cut {n : ℕ} (i : I) (hi : s.generatorDegree i < n) :
    s.parameterBasis i ∈ s.cut n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem coefficient_mem_cut {n : ℕ} (j : J)
    (hj : s.generatorDegree (s.parent j) < n) :
    s.coefficientBasis j ∈ s.cut n := by
  rw [s.coefficient_eq]
  exact (s.cut n).smul_mem _ (s.generator_mem_cut _ hj)

def projection (n : ℕ) : M →ₗ[K] s.piece n :=
  LinearMap.codRestrict (s.piece n)
    (basisDegreeProjection s.coefficientBasis s.degree n) (by
      intro x j hj
      simp only [basisDegreeProjection_repr, if_neg hj])

@[simp] theorem projection_coefficient (n : ℕ) (j : J) (hj : s.degree j = n) :
    s.projection n (s.coefficientBasis j) =
      ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_pos hj)

@[simp] theorem projection_coefficient_of_ne (n : ℕ) (j : J) (hj : s.degree j ≠ n) :
    s.projection n (s.coefficientBasis j) = 0 := by
  apply Subtype.ext
  exact (basisDegreeProjection_basis s.coefficientBasis s.degree n j).trans (if_neg hj)

@[simp] theorem projection_subtype (n : ℕ) (x : s.piece n) :
    s.projection n x.val = x := by
  apply Subtype.ext
  apply s.coefficientBasis.repr.injective
  ext j
  change s.coefficientBasis.repr
    (basisDegreeProjection s.coefficientBasis s.degree n x.val) j = _
  rw [basisDegreeProjection_repr]
  by_cases hj : s.degree j = n
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact (x.property j hj).symm

variable {N : Type*} [AddCommGroup N] [Module K N]

theorem maps_eq_on_piece (n : ℕ) (f : M →ₗ[K] N) (g : s.piece n →ₗ[K] N)
    (h : ∀ j (hj : s.degree j = n),
      f (s.coefficientBasis j) = g ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩)
    (x : s.piece n) : f x.val = g x := by
  have he : f.comp ((s.piece n).subtype.comp (s.projection n)) =
      g.comp (s.projection n) := by
    apply s.coefficientBasis.ext
    intro j
    by_cases hj : s.degree j = n
    · simp only [LinearMap.comp_apply, s.projection_coefficient n j hj,
        Submodule.subtype_apply]
      exact h j hj
    · simp only [LinearMap.comp_apply, s.projection_coefficient_of_ne n j hj,
        map_zero]
  have hx := congrArg (fun z : M →ₗ[K] N => z x.val) he
  simpa using hx

theorem homogeneous_mem_cut {m n : ℕ} (hmn : m < n) (x : M)
    (hx : x ∈ s.piece m) : x ∈ s.cut n := by
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply ((s.cut n).restrictScalars K).sum_mem
  intro j hj
  apply ((s.cut n).restrictScalars K).smul_mem
  have hdeg : s.degree j = m := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  apply s.coefficient_mem_cut j
  calc
    s.generatorDegree (s.parent j) ≤ s.degree j := s.parent_degree_le j
    _ = m := hdeg
    _ < n := hmn

variable [Module A N] [IsScalarTower K A N]

theorem maps_eq_on_cut (n : ℕ) (f g : M →ₗ[A] N)
    (h : ∀ i, s.generatorDegree i < n → f (s.parameterBasis i) = g (s.parameterBasis i))
    (x : M) (hx : x ∈ s.cut n) : f x = g x := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact h i hi
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

theorem graded_of_generators (T : ℕ → Submodule K N)
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (f : M →ₗ[A] N) (hf : ∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i))
    (n : ℕ) (x : M) (hx : x ∈ s.piece n) : f x ∈ T n := by
  let fk : M →ₗ[K] N := f.restrictScalars K
  change fk x ∈ T n
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : s.degree j = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hj (hx j hn)
  change f (s.coefficientBasis j) ∈ T n
  rw [s.coefficient_eq, map_smul]
  exact hdeg ▸ hmult j _ (hf (s.parent j))

variable {G : Type*} [Group G]

def restrictRepresentation (ρ : CyclicRepresentation A G M) : CyclicRepresentation K G M where
  toFun g := (ρ g).restrictScalars K
  map_one' := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) ρ.map_one
  map_mul' g h := by ext x; exact congrArg (fun f : M →ₗ[A] M => f x) (ρ.map_mul g h)

theorem cut_invariant (ρ : CyclicRepresentation A G M)
    (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
    (n : ℕ) (g : G) (x : M) (hx : x ∈ s.cut n) : ρ g x ∈ s.cut n := by
  change x ∈ Submodule.span A (s.parameterBasis '' {i | s.generatorDegree i < n}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact s.homogeneous_mem_cut hi _ (hρ g _ _ (s.generator_mem_piece i))
  | zero => simpa using (s.cut n).zero_mem
  | add x y hx hy ihx ihy => simpa using (s.cut n).add_mem ihx ihy
  | smul a x hx ih => simpa using (s.cut n).smul_mem a ih

end ScalarGradedBasis

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicControlledOrdinaryLift.lean -/
section


section

/-! # Ordinary correction to the fixed-face prescription

A homogeneous discrepancy whose fixed-face boundary vanishes is lifted by
its top-coordinate cofactor and the literal fixed-face section. This lift
has zero original boundary and the original, unscaled degree. Extending
these corrections on a genuine graded parameter basis gives the ordinary
simultaneous lift needed by the integral equivariant construction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical

section ActualCorrection
variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- An actual degree-n correction with zero proper boundary and prescribed
fixed-face image. All divisibility here concerns integer degrees only. -/
theorem exists_fixedFace_boundary_correction (n : ℕ)
    (δ : BooleanBarycentricRing W K)
    (hδ : booleanBoundaryMap δ = 0)
    (hdegree : δ ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (n / p))
    (hzero : ¬ p ∣ n → δ = 0) :
    ∃ y : BooleanBarycentricRing (ZMod p × W) K,
      y ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n ∧
      booleanBoundaryMap y = 0 ∧ primeFixedFaceQuotient p K y = δ := by
  by_cases hd : p ∣ n
  · obtain ⟨z, hz⟩ := (booleanBoundaryMap_eq_zero_iff δ).mp hδ
    by_cases ht : Fintype.card W ≤ n / p
    · let m := n / p - Fintype.card W
      have hzg : z ∈ basisOrdinaryDegreePiece booleanChainBasis
          (fun a => booleanOrdinaryDegree a.val) m := by
        apply booleanTopOrdinary_predecessor_degree m z
        simpa only [m, Nat.sub_add_cancel ht, hz] using hdegree
      let y : BooleanBarycentricRing (ZMod p × W) K :=
        booleanTop * primeFixedFaceSection p K z
      have hn : p * m + Fintype.card (ZMod p × W) = n := by
        calc
          p * m + Fintype.card (ZMod p × W) = p * (m + Fintype.card W) := by
            simp only [Fintype.card_prod, ZMod.card, Nat.mul_add]
          _ = p * (n / p) := by rw [show m + Fintype.card W = n / p from Nat.sub_add_cancel ht]
          _ = n := Nat.mul_div_cancel' hd
      refine ⟨y, ?_, ?_, ?_⟩
      · simpa only [hn] using booleanTopOrdinary_mul_degree (p * m)
          (primeFixedFaceSection p K z) (primeFixedFaceSection_degree p K m z hzg)
      · exact (booleanBoundaryMap_eq_zero_iff y).mpr ⟨primeFixedFaceSection p K z, rfl⟩
      · change primeFixedFaceQuotient p K (booleanTop * primeFixedFaceSection p K z) = δ
        rw [map_mul, primeFixedFaceQuotient_top, primeFixedFaceQuotient_section]
        exact hz
    · have hz0 : z = 0 := booleanTopOrdinary_homogeneous_zero_below (n / p)
        (Nat.lt_of_not_ge ht) z (by simpa only [hz] using hdegree)
      have hδ0 : δ = 0 := by rw [← hz, hz0, mul_zero]
      exact ⟨0, Submodule.zero_mem _, map_zero _, (map_zero _).trans hδ0.symm⟩
  · exact ⟨0, Submodule.zero_mem _, map_zero _, (map_zero _).trans (hzero hd).symm⟩

end ActualCorrection

namespace ScalarGradedBasis
variable {K A M N B Q I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
  [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
  [AddCommGroup B] [Module A B] [AddCommGroup Q] [Module A Q]

/-- Extend actual homogeneous generator corrections A-linearly. Both quotient
identities are proved on the full parameter basis, not merely on its span in
a selected degree. -/
theorem exists_graded_boundary_quotient_lift
    (s : ScalarGradedBasis K A M I J) (T : ℕ → Submodule K N)
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (b : N →ₗ[A] B) (π : N →ₗ[A] Q) (f₀ : M →ₗ[A] N) (a : M →ₗ[A] Q)
    (hgrade : ∀ n x, x ∈ s.piece n → f₀ x ∈ T n)
    (hcorr : ∀ i, ∃ y : N, y ∈ T (s.generatorDegree i) ∧ b y = 0 ∧
      π y = a (s.parameterBasis i) - π (f₀ (s.parameterBasis i))) :
    ∃ f : M →ₗ[A] N, (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧
      b.comp f = b.comp f₀ ∧ π.comp f = a := by
  choose y hyg hyb hyπ using hcorr
  let c : M →ₗ[A] N := s.parameterBasis.constr A y
  have hc (i : I) : c (s.parameterBasis i) = y i := s.parameterBasis.constr_basis A y i
  let f := f₀ + c
  refine ⟨f, ?_, ?_, ?_⟩
  · intro n x hx
    exact (T n).add_mem (hgrade n x hx)
      (s.graded_of_generators T hmult c (fun i => (hc i).symm ▸ hyg i) n x hx)
  · apply s.parameterBasis.ext
    intro i
    change b (f₀ (s.parameterBasis i) + c (s.parameterBasis i)) = b (f₀ (s.parameterBasis i))
    rw [map_add, hc, hyb, add_zero]
  · apply s.parameterBasis.ext
    intro i
    change π (f₀ (s.parameterBasis i) + c (s.parameterBasis i)) = a (s.parameterBasis i)
    rw [map_add, hc, hyπ, add_comm, sub_add_cancel]

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerKernelAction.lean -/
section


section

/-! # The actual regular chain kernel for cyclic prime-power actions

A centralizing permutation of a union of free prime orbits acts on the
literal chain-monomial kernel of the fixed-face quotient. In a cyclic
prime-power group containing those translations, this basis action is
free. Its finite homogeneous pieces are therefore genuine coinduced
modules over every commutative coefficient ring.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
universe uW uG uK
open Classical Finset

section VertexActions
variable {V U T G : Type*} [Fintype V] [Fintype U] [Fintype T] [Group G]

@[simp] theorem booleanChainVertexEquiv_refl (a : BooleanChainExponent V) :
    booleanChainVertexEquiv (Equiv.refl V) a = a := by
  apply Subtype.ext
  change a.val.mapDomain (booleanFaceEmbedding (Function.Embedding.refl V)) = a.val
  simp only [booleanFaceEmbedding_refl]
  exact Finsupp.mapDomain_id

theorem booleanChainVertexEquiv_trans (e : V ≃ U) (f : U ≃ T)
    (a : BooleanChainExponent V) :
    booleanChainVertexEquiv f (booleanChainVertexEquiv e a) =
      booleanChainVertexEquiv (e.trans f) a := by
  apply Subtype.ext
  change (a.val.mapDomain (booleanFaceEmbedding e.toEmbedding)).mapDomain
      (booleanFaceEmbedding f.toEmbedding) =
    a.val.mapDomain (booleanFaceEmbedding (e.trans f).toEmbedding)
  rw [← Finsupp.mapDomain_fun_comp]
  apply Finsupp.mapDomain_congr
  intro F hF
  exact booleanFaceEmbedding_trans e.toEmbedding f.toEmbedding F

/-- The face action is the actual map of finite vertex subsets. -/
def booleanFaceVertexMulAction (ρ : G →* Equiv.Perm V) : MulAction G (BooleanFace V) where
  smul g F := booleanFaceEmbedding (ρ g).toEmbedding F
  one_smul F := by
    change booleanFaceEmbedding (ρ 1).toEmbedding F = F
    rw [ρ.map_one]
    exact booleanFaceEmbedding_refl F
  mul_smul g h F := by
    change booleanFaceEmbedding (ρ (g * h)).toEmbedding F =
      booleanFaceEmbedding (ρ g).toEmbedding (booleanFaceEmbedding (ρ h).toEmbedding F)
    rw [ρ.map_mul, booleanFaceEmbedding_trans]
    rfl

theorem booleanFace_card_strictMono : StrictMono (fun F : BooleanFace V => F.val.card) := by
  intro F H h
  exact Finset.card_lt_card h

theorem booleanChainVertexEquiv_degree (e : V ≃ U) (a : BooleanChainExponent V) :
    booleanOrdinaryDegree (booleanChainVertexEquiv e a).val = booleanOrdinaryDegree a.val := by
  change booleanOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e.toEmbedding)) = _
  exact chainOrdinaryDegree_map_vertexEmbedding e.toEmbedding a.val

end VertexActions

variable (p : ℕ) [Fact p.Prime]
variable {W : Type uW} {G : Type uG} [Fintype W] [Group G]
variable (K : Type uK) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- The kernel index action is induced by the original vertex permutation. -/
def primeFixedKernelIndexMulAction : MulAction G (PrimeFixedFaceKernelIndex (W := W) p) where
  smul g a := primeFixedFaceKernelIndexEquiv p (primeOrbitParentAction p ρ hρ g)
    (fun w => (ρ g (0, w)).1) a
  one_smul a := by
    apply Subtype.ext
    change booleanChainVertexEquiv
      (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ 1) (fun w => (ρ 1 (0,w)).1)) a.val = a.val
    rw [← primeOrbitParentAction_normalForm, ρ.map_one]
    exact booleanChainVertexEquiv_refl a.val
  mul_smul g h a := by
    apply Subtype.ext
    change booleanChainVertexEquiv
      (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ (g*h)) (fun w => (ρ (g*h) (0,w)).1)) a.val =
      booleanChainVertexEquiv
        (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ g) (fun w => (ρ g (0,w)).1))
        (booleanChainVertexEquiv
          (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ h) (fun w => (ρ h (0,w)).1)) a.val)
    rw [← primeOrbitParentAction_normalForm, ← primeOrbitParentAction_normalForm,
      ← primeOrbitParentAction_normalForm, booleanChainVertexEquiv_trans, ρ.map_mul]
    rfl

def primeFixedKernelIndexAction (g : G) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    PrimeFixedFaceKernelIndex (W := W) p :=
  primeFixedFaceKernelIndexEquiv p (primeOrbitParentAction p ρ hρ g)
    (fun w => (ρ g (0,w)).1) a

@[simp] theorem primeFixedKernelIndex_smul_val (g : G)
    (a : PrimeFixedFaceKernelIndex (W := W) p) :
    (primeFixedKernelIndexAction p ρ hρ g a).val = booleanChainVertexEquiv (ρ g) a.val := by
  change booleanChainVertexEquiv
    (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ g) (fun w => (ρ g (0,w)).1)) a.val = _
  rw [← primeOrbitParentAction_normalForm]

theorem primeFixedKernelIndex_degree (g : G) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    primeFixedKernelDegree p (primeFixedKernelIndexAction p ρ hρ g a) = primeFixedKernelDegree p a := by
  unfold primeFixedKernelDegree
  rw [primeFixedKernelIndex_smul_val]
  exact booleanChainVertexEquiv_degree (ρ g) a.val

/-- This representation restricts the literal quotient-ring relabeling. -/
def primeFixedKernelRepresentation : CyclicRepresentation K G (PrimeFixedFaceKernel (W := W) p K) where
  toFun g := primeFixedFaceKernelRelabel p K (primeOrbitParentAction p ρ hρ g)
    (fun w => (ρ g (0,w)).1)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change booleanVertexRelabelEquiv
      (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ 1) (fun w => (ρ 1 (0,w)).1)) x.val = x.val
    rw [← primeOrbitParentAction_normalForm, ρ.map_one]
    exact booleanVertexRelabelEquiv_refl x.val
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change booleanVertexRelabelEquiv
      (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ (g*h)) (fun w => (ρ (g*h) (0,w)).1)) x.val =
      booleanVertexRelabelEquiv
        (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ g) (fun w => (ρ g (0,w)).1))
        (booleanVertexRelabelEquiv
          (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ h) (fun w => (ρ h (0,w)).1)) x.val)
    rw [← primeOrbitParentAction_normalForm, ← primeOrbitParentAction_normalForm,
      ← primeOrbitParentAction_normalForm, ← booleanVertexRelabelEquiv_trans, ρ.map_mul]
    rfl

@[simp] theorem primeFixedKernelRepresentation_val (g : G)
    (x : PrimeFixedFaceKernel (W := W) p K) :
    (primeFixedKernelRepresentation p K ρ hρ g x).val = booleanVertexRelabelEquiv (ρ g) x.val := by
  change booleanVertexRelabelEquiv
    (primeOrbitRelabel p (primeOrbitParentAction p ρ hρ g) (fun w => (ρ g (0,w)).1)) x.val = _
  rw [← primeOrbitParentAction_normalForm]

theorem primeFixedKernelRepresentation_coefficient (g : G)
    (x : PrimeFixedFaceKernel (W := W) p K) (a : PrimeFixedFaceKernelIndex (W := W) p) :
    (primeFixedFaceKernelBasis p K).repr (primeFixedKernelRepresentation p K ρ hρ g x) a =
      (primeFixedFaceKernelBasis p K).repr x (primeFixedKernelIndexAction p ρ hρ g⁻¹ a) := by
  rw [primeFixedFaceKernelBasis_repr, primeFixedKernelRepresentation_val,
    booleanVertexRelabelEquiv_coefficient, primeFixedFaceKernelBasis_repr,
    primeFixedKernelIndex_smul_val]
  have h : booleanChainVertexEquiv (ρ g⁻¹) a.val = (booleanChainVertexEquiv (ρ g)).symm a.val := by
    apply (booleanChainVertexEquiv (ρ g)).injective
    rw [booleanChainVertexEquiv_trans, Equiv.apply_symm_apply]
    have he : (ρ g⁻¹).trans (ρ g) = Equiv.refl (ZMod p × W) := by
      apply Equiv.ext
      intro v
      change (ρ g * ρ g⁻¹) v = v
      rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
      rfl
    rw [he, booleanChainVertexEquiv_refl]
  rw [h]

/-- Restriction of the genuine kernel representation to ordinary degree n. -/
def primeFixedKernelHomogeneousRepresentation (n : ℕ) :
    CyclicRepresentation K G (PrimeFixedKernelDegreePiece (W := W) p K n) := by
  letI := primeFixedKernelIndexMulAction p ρ hρ
  exact basisDegreeRepresentation (primeFixedFaceKernelBasis p K) (primeFixedKernelDegree p)
    (primeFixedKernelRepresentation p K ρ hρ) (primeFixedKernelIndex_degree p ρ hρ)
    (primeFixedKernelRepresentation_coefficient p K ρ hρ) n

section Free
variable [Finite G] [IsCyclic G]
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))

include hG hZ htranslations in
/-- The full kernel basis, not merely selected degree pieces, has trivial
stabilizers under the cyclic prime-power group. -/
theorem primeFixedKernelIndex_free (g : G) (a : PrimeFixedFaceKernelIndex (W := W) p)
    (hfix : primeFixedKernelIndexAction p ρ hρ g a = a) : g = 1 := by
  letI : MulAction G (BooleanFace (ZMod p × W)) := booleanFaceVertexMulAction ρ
  have hnon : ∃ F ∈ a.val.val.support, ∃ z : Z, z.val • F ≠ F := by
    obtain ⟨F, hF, t, ht⟩ := (primeFixedChainEmbedding_nonfixed_iff p a.val).mp a.property
    obtain ⟨z, hz⟩ := htranslations t
    refine ⟨F, hF, z, ?_⟩
    change booleanFaceEmbedding (ρ z.val).toEmbedding F ≠ F
    rw [hz]
    intro he
    apply ht
    have hh := congrArg Subtype.val he
    change F.val.map (primeOrbitRelabel p (Equiv.refl W) (fun _ => t)).toEmbedding = F.val at hh
    rw [Finset.map_eq_image] at hh
    exact hh
  have hmap : Finsupp.mapDomain (fun F : BooleanFace (ZMod p × W) => g • F) a.val.val = a.val.val := by
    have hh := congrArg (fun b : PrimeFixedFaceKernelIndex (W := W) p => b.val.val) hfix
    change a.val.val.mapDomain (booleanFaceEmbedding (ρ g).toEmbedding) = a.val.val
    simpa only [primeFixedKernelIndex_smul_val, booleanChainVertexEquiv_val] using hh
  exact nonfixedChainExponent_stabilizer_trivial (fun F : BooleanFace (ZMod p × W) => F.val.card)
    booleanFace_card_strictMono (fun h F => booleanFaceEmbedding_card (ρ h).toEmbedding F)
    hG Z hZ a.val.val a.val.property hnon g hmap

include hG hZ htranslations

/-- The actual homogeneous fixed-face kernel is coinduced over K. -/
theorem primeFixedKernelDegree_isCoinduced (n : ℕ) :
    ∃ J : Type uW, ∃ e : PrimeFixedKernelDegreePiece (W := W) p K n ≃ₗ[K] (G → J → K),
      RepresentationIntertwines (primeFixedKernelHomogeneousRepresentation p K ρ hρ n)
        coinducedRepresentation e.toLinearMap := by
  letI := primeFixedKernelIndexMulAction p ρ hρ
  exact basisDegreePiece_isCoinduced (primeFixedFaceKernelBasis p K) (primeFixedKernelDegree p)
    (primeFixedKernelRepresentation p K ρ hρ) (primeFixedKernelIndex_degree p ρ hρ)
    (primeFixedKernelRepresentation_coefficient p K ρ hρ) n
    (fun g a _ hfix => primeFixedKernelIndex_free p ρ hρ hG Z hZ htranslations g a hfix)

end Free
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicControlledProjection.lean -/
section

section
/-! # A graded coefficient retraction onto the simultaneous kernel

The retraction retains exactly those original chain monomials which contain
the top face and contain a face not fixed by the prime subgroup. It splits
the actual simultaneous kernel over the coefficient ring in every degree.
Equivariance of this splitting is not assumed or needed.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical

section TopProjection
variable {V K : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [CommRing K]

theorem booleanBoundaryMap_eq_zero_iff_coeff (x : BooleanBarycentricRing V K) :
    booleanBoundaryMap x = 0 ↔ ∀ a : BooleanChainExponent V,
      a.val booleanTopFace = 0 → booleanChainBasis.repr x a = 0 := by
  constructor
  · intro hx a ha
    change coordinateBoundaryMap IsChainExponent booleanTopFace x = 0 at hx
    have h := coordinateBoundaryMap_coefficient IsChainExponent
      isChainExponent_divisorClosed booleanTopFace x ⟨a.val, a.property, ha⟩
    rw [hx, map_zero, Finsupp.zero_apply] at h
    exact h.symm
  · intro hx
    apply (standardMonomialBasis (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr.injective
    ext a
    rw [map_zero, Finsupp.zero_apply]
    change (standardMonomialBasis (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr (coordinateBoundaryMap IsChainExponent booleanTopFace x) a = 0
    rw [coordinateBoundaryMap_coefficient]
    exact hx ⟨a.val, a.property.1⟩ a.property.2

def booleanTopPartProjection : BooleanBarycentricRing V K →ₗ[K] BooleanBarycentricRing V K where
  toFun x := booleanChainBasis.repr.symm
    ((booleanChainBasis.repr x).filter (fun a => a.val booleanTopFace ≠ 0))
  map_add' x y := by
    apply booleanChainBasis.repr.injective
    simp only [LinearEquiv.apply_symm_apply, map_add, Finsupp.filter_add]
  map_smul' c x := by
    apply booleanChainBasis.repr.injective
    simp only [LinearEquiv.apply_symm_apply, map_smul, Finsupp.filter_smul, RingHom.id_apply]

theorem booleanTopPartProjection_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    booleanChainBasis.repr (booleanTopPartProjection x) a =
      if a.val booleanTopFace ≠ 0 then booleanChainBasis.repr x a else 0 := by
  change booleanChainBasis.repr (booleanChainBasis.repr.symm _) a = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.filter_apply]

theorem booleanTopPartProjection_boundary (x : BooleanBarycentricRing V K) :
    booleanBoundaryMap (booleanTopPartProjection x) = 0 := by
  apply (booleanBoundaryMap_eq_zero_iff_coeff _).mpr
  intro a ha
  rw [booleanTopPartProjection_coefficient, if_neg (not_not_intro ha)]

theorem booleanTopPartProjection_retract (x : BooleanBarycentricRing V K)
    (hx : booleanBoundaryMap x = 0) : booleanTopPartProjection x = x := by
  apply booleanChainBasis.repr.injective
  ext a
  rw [booleanTopPartProjection_coefficient]
  by_cases ha : a.val booleanTopFace = 0
  · rw [if_neg (not_not_intro ha), (booleanBoundaryMap_eq_zero_iff_coeff x).mp hx a ha]
  · rw [if_pos ha]

theorem booleanTopPartProjection_degree (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    booleanTopPartProjection x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  rw [booleanTopPartProjection_coefficient]
  split_ifs
  · exact hx a ha
  · rfl

end TopProjection

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

theorem primeFixedFaceKernelProjection_boundary
    (x : BooleanBarycentricRing (ZMod p × W) K) (hx : booleanBoundaryMap x = 0) :
    booleanBoundaryMap (primeFixedFaceKernelProjection p K x).val = 0 := by
  apply (booleanBoundaryMap_eq_zero_iff_coeff _).mpr
  intro a ha
  rw [primeFixedFaceKernelProjection_coefficient]
  split_ifs
  · rfl
  · exact (booleanBoundaryMap_eq_zero_iff_coeff x).mp hx a ha

def primeControlledKernelProjection : BooleanBarycentricRing (ZMod p × W) K →ₗ[K]
    PrimeControlledKernel (W := W) p K where
  toFun x := ⟨(primeFixedFaceKernelProjection p K (booleanTopPartProjection x)).val,
    primeFixedFaceKernelProjection_boundary p K _ (booleanTopPartProjection_boundary x),
    (primeFixedFaceKernelProjection p K (booleanTopPartProjection x)).property⟩
  map_add' x y := by
    apply Subtype.ext
    change (primeFixedFaceKernelProjection p K (booleanTopPartProjection (x + y))).val = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change (primeFixedFaceKernelProjection p K (booleanTopPartProjection (c • x))).val = _
    rw [map_smul, map_smul]
    rfl

theorem primeControlledKernelProjection_retract (x : PrimeControlledKernel (W := W) p K) :
    primeControlledKernelProjection p K x.val = x := by
  apply Subtype.ext
  change (primeFixedFaceKernelProjection p K (booleanTopPartProjection x.val)).val = x.val
  rw [booleanTopPartProjection_retract x.val x.property.1]
  exact congrArg Subtype.val
    (primeFixedFaceKernelProjection_retract p K ⟨x.val, x.property.2⟩)

theorem primeControlledKernelProjection_degree (n : ℕ)
    (x : BooleanBarycentricRing (ZMod p × W) K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    (primeControlledKernelProjection p K x).val ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n :=
  primeFixedFaceKernelProjection_degree p K n _ (booleanTopPartProjection_degree n x hx)

def PrimeControlledKernelDegreePiece (n : ℕ) : Submodule K (PrimeControlledKernel (W := W) p K) :=
  (basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n).comap
    (PrimeControlledKernel (W := W) p K).subtype

def primeControlledDegreeInclusion (n : ℕ) : PrimeControlledKernelDegreePiece (W := W) p K n →ₗ[K]
    basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n where
  toFun x := ⟨x.val.val, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeControlledDegreeProjection (n : ℕ) :
    basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n →ₗ[K]
        PrimeControlledKernelDegreePiece (W := W) p K n where
  toFun x := ⟨primeControlledKernelProjection p K x.val,
    primeControlledKernelProjection_degree p K n x.val x.property⟩
  map_add' x y := by apply Subtype.ext; exact (primeControlledKernelProjection p K).map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact (primeControlledKernelProjection p K).map_smul c x.val

theorem primeControlledDegreeProjection_inclusion (n : ℕ) :
    (primeControlledDegreeProjection (W := W) p K n).comp (primeControlledDegreeInclusion p K n) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact primeControlledKernelProjection_retract p K x.val

def primeControlledDegreeTopMap (n : ℕ) : PrimeFixedKernelDegreePiece (W := W) p K n →ₗ[K]
    PrimeControlledKernelDegreePiece (W := W) p K (n + Fintype.card (ZMod p × W)) where
  toFun y := ⟨primeControlledKernelTopEquiv p K y.val, by
    change (primeControlledKernelTopEquiv p K y.val).val ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val)
        (n + Fintype.card (ZMod p × W))
    rw [primeControlledKernelTopEquiv_apply]
    exact booleanTopOrdinary_mul_degree n y.val.val
      ((mem_primeFixedKernelDegreePiece_iff p K n y.val).mp y.property)⟩
  map_add' x y := by apply Subtype.ext; exact (primeControlledKernelTopEquiv p K).map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact (primeControlledKernelTopEquiv p K).map_smul c x.val

theorem primeControlledDegreeTopMap_bijective (n : ℕ) :
    Function.Bijective (primeControlledDegreeTopMap (W := W) p K n) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have hh := congrArg (fun z : PrimeControlledKernelDegreePiece (W := W) p K
      (n + Fintype.card (ZMod p × W)) => z.val) h
    change primeControlledKernelTopEquiv p K x.val = primeControlledKernelTopEquiv p K y.val at hh
    exact (primeControlledKernelTopEquiv p K).injective hh
  · intro x
    let a := (primeControlledKernelTopEquiv p K).symm x.val
    have ha : a ∈ PrimeFixedKernelDegreePiece (W := W) p K n := by
      apply (mem_primeFixedKernelDegreePiece_iff p K n a).mpr
      apply booleanTopOrdinary_predecessor_degree n a.val
      have he : booleanTop * a.val = x.val.val :=
        congrArg Subtype.val ((primeControlledKernelTopEquiv p K).apply_symm_apply x.val)
      rw [he]
      exact x.property
    exact ⟨⟨a, ha⟩, Subtype.ext ((primeControlledKernelTopEquiv p K).apply_symm_apply x.val)⟩

def primeControlledDegreeTopEquiv (n : ℕ) : PrimeFixedKernelDegreePiece (W := W) p K n ≃ₗ[K]
    PrimeControlledKernelDegreePiece (W := W) p K (n + Fintype.card (ZMod p × W)) :=
  LinearEquiv.ofBijective (primeControlledDegreeTopMap p K n)
    (primeControlledDegreeTopMap_bijective p K n)

theorem primeControlledDegree_zero_below (n : ℕ) (hn : n < Fintype.card (ZMod p × W))
    (x : PrimeControlledKernelDegreePiece (W := W) p K n) : x = 0 := by
  obtain ⟨a, ha⟩ := (primeControlledKernel_eq_top_kernel p K x.val.val).mp x.val.property
  have hz : a.val = 0 := booleanTopOrdinary_homogeneous_zero_below n hn a.val (by
    rw [ha]
    exact x.property)
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = 0
  rw [← ha, hz, mul_zero]

/-- The same homogeneous kernel, now literally a submodule of the ambient
Boolean degree piece, for the parameter-quotient lifting theorem. -/
def primeControlledHomogeneousKernel (n : ℕ) :
    Submodule K (basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n) :=
  (PrimeControlledKernel p K).comap
    (basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n).subtype

def primeControlledDegreeSwap (n : ℕ) : PrimeControlledKernelDegreePiece (W := W) p K n ≃ₗ[K]
    primeControlledHomogeneousKernel (W := W) p K n where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeControlledHomogeneousProjection (n : ℕ) :
    basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n →ₗ[K]
        primeControlledHomogeneousKernel (W := W) p K n :=
  (primeControlledDegreeSwap p K n).toLinearMap.comp (primeControlledDegreeProjection p K n)

theorem primeControlledHomogeneousProjection_retract (n : ℕ) :
    (primeControlledHomogeneousProjection (W := W) p K n).comp
      (primeControlledHomogeneousKernel p K n).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change (primeControlledKernelProjection p K x.val.val).val = x.val.val
  have h := congrArg (fun y : PrimeControlledKernel (W := W) p K => y.val)
    (primeControlledKernelProjection_retract p K ⟨x.val.val, x.property⟩)
  exact h

def primeControlledHomogeneousTopEquiv (n : ℕ) : PrimeFixedKernelDegreePiece (W := W) p K n ≃ₗ[K]
    primeControlledHomogeneousKernel (W := W) p K (n + Fintype.card (ZMod p × W)) :=
  (primeControlledDegreeTopEquiv p K n).trans
    (primeControlledDegreeSwap p K (n + Fintype.card (ZMod p × W)))

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedLift.lean -/
section


section

/-! # The finite degree induction for equivariant lifting

This file separates the finite induction from the one-degree kernel calculation.
No map on the generators is assumed to intertwine the group action.  The lower
generator span is stable because the action preserves degree, and agreement on
its intersection with the next degree is imposed explicitly.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)

/-- The induction invariant is stated on all parameter-basis generators of
degree below `n`.  A-linearity extends the last two conditions to `cut n`. -/
def LiftStage (n : ℕ) (f : M →ₗ[A] N) : Prop :=
  (∀ i, f (s.parameterBasis i) ∈ T (s.generatorDegree i)) ∧
  (∀ i, s.generatorDegree i < n → q (f (s.parameterBasis i)) = a (s.parameterBasis i)) ∧
  (∀ g i, s.generatorDegree i < n →
    f (ρ g (s.parameterBasis i)) = τ g (f (s.parameterBasis i)))

theorem LiftStage.quotient_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (x : M) (hx : x ∈ s.cut n) :
    q (f x) = a x :=
  s.maps_eq_on_cut n (q.comp f) a hf.2.1 x hx

theorem LiftStage.equivariant_on_cut {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f) (g : G) (x : M) (hx : x ∈ s.cut n) :
    f (ρ g x) = τ g (f x) :=
  s.maps_eq_on_cut n (f.comp (ρ g)) ((τ g).comp f) (hf.2.2 g) x hx

variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)

/-- A one-degree lift, with the previously fixed lower-generator values. -/
def DegreeLift (n : ℕ) (f : M →ₗ[A] N) (L : s.piece n →ₗ[K] N) : Prop :=
  (∀ x, L x ∈ T n) ∧
  (∀ g x, L ⟨ρ g x.val, hρ g n x.val x.property⟩ = τ g (L x)) ∧
  (∀ x, q (L x) = a x.val) ∧
  (∀ x, x.val ∈ s.cut n → L x = f x.val)

/-- The induction step.  Its only input beyond the preceding stage is a lift on
the actual homogeneous component, compatible on the actual intersection. -/
theorem liftStage_succ {n : ℕ} {f : M →ₗ[A] N}
    (hf : s.LiftStage ρ τ T q a n f)
    (L : s.piece n →ₗ[K] N) (hL : s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ F : M →ₗ[A] N, s.LiftStage ρ τ T q a (n + 1) F := by
  let v : I → N := fun i =>
    if hi : s.generatorDegree i = n then
      L ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    else f (s.parameterBasis i)
  let F : M →ₗ[A] N := s.parameterBasis.constr A v
  have hF (i : I) : F (s.parameterBasis i) = v i :=
    s.parameterBasis.constr_basis A v i
  have hFcut (x : M) (hx : x ∈ s.cut n) : F x = f x := by
    apply s.maps_eq_on_cut n F f _ x hx
    intro i hi
    rw [hF]
    exact dif_neg (Nat.ne_of_lt hi)
  have hFpiece (x : s.piece n) : F x.val = L x := by
    apply s.maps_eq_on_piece n (F.restrictScalars K) L _ x
    intro j hj
    have hp : s.generatorDegree (s.parent j) ≤ n := by
      simpa only [hj] using s.parent_degree_le j
    by_cases he : s.generatorDegree (s.parent j) = n
    · have hc : s.coefficientBasis j = s.parameterBasis (s.parent j) :=
        s.equal_degree_eq j (hj.trans he.symm)
      change F (s.coefficientBasis j) = _
      calc
        F (s.coefficientBasis j) = F (s.parameterBasis (s.parent j)) := congrArg F hc
        _ = L ⟨s.parameterBasis (s.parent j), he ▸ s.generator_mem_piece (s.parent j)⟩ := by
          rw [hF]
          exact dif_pos he
        _ = L ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ :=
          congrArg L (Subtype.ext hc.symm)
    · have hlt : s.generatorDegree (s.parent j) < n := lt_of_le_of_ne hp he
      have hcut := s.coefficient_mem_cut j hlt
      change F (s.coefficientBasis j) = _
      rw [hFcut _ hcut]
      exact (hL.2.2.2 ⟨s.coefficientBasis j, hj ▸ s.coefficient_mem_piece j⟩ hcut).symm
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    rw [hF]
    dsimp only [v]
    split_ifs with hi
    · simpa only [hi] using hL.1
        ⟨s.parameterBasis i, hi ▸ s.generator_mem_piece i⟩
    · exact hf.1 i
  · intro i hi
    by_cases hlt : s.generatorDegree i < n
    · rw [hFcut _ (s.generator_mem_cut i hlt)]
      exact hf.2.1 i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      rw [hFpiece x]
      exact hL.2.2.1 x
  · intro g i hi
    by_cases hlt : s.generatorDegree i < n
    · have hbi : s.parameterBasis i ∈ s.cut n := s.generator_mem_cut i hlt
      rw [hFcut _ (s.cut_invariant ρ hρ n g _ hbi), hFcut _ hbi]
      exact hf.2.2 g i hlt
    · have he : s.generatorDegree i = n := by omega
      let x : s.piece n := ⟨s.parameterBasis i, he ▸ s.generator_mem_piece i⟩
      let gx : s.piece n := ⟨ρ g x.val, hρ g n x.val x.property⟩
      change F gx.val = τ g (F x.val)
      rw [hFpiece gx, hFpiece x]
      exact hL.2.1 g x

/-- The full finite induction.  The one-degree extension premise is discharged
by the relative-injectivity theorem in the next construction, not postulated as
a property of the paper's face rings. -/
theorem exists_equivariantGradedLift_of_degreeExtensions [Fintype I]
    (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j))
    (hstep : ∀ n f, s.LiftStage ρ τ T q a n f →
      ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have stages : ∀ n, ∃ f : M →ₗ[A] N, s.LiftStage ρ τ T q a n f := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, ?_, ?_, ?_⟩
        · intro i
          exact (T (s.generatorDegree i)).zero_mem
        · intro i hi
          exact False.elim (Nat.not_lt_zero _ hi)
        · intro g i hi
          exact False.elim (Nat.not_lt_zero _ hi)
    | succ n ih =>
        obtain ⟨f, hf⟩ := ih
        obtain ⟨L, hL⟩ := hstep n f hf
        exact s.liftStage_succ ρ τ T q a hρ hf L hL
  let n : ℕ := Finset.univ.sup s.generatorDegree + 1
  obtain ⟨f, hf⟩ := stages n
  have hbound (i : I) : s.generatorDegree i < n :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  refine ⟨f, s.graded_of_generators T hmult f hf.1, ?_, ?_⟩
  · apply s.parameterBasis.ext
    intro i
    exact hf.2.1 i (hbound i)
  · intro g x
    have he : f.comp (ρ g) = (τ g).comp f := by
      apply s.parameterBasis.ext
      intro i
      exact hf.2.2 g i (hbound i)
    exact congrArg (fun F : M →ₗ[A] N => F x) he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicSplitKernelLift.lean -/
section


section

/-! # An ordinary lift can be made equivariant

An equivariant kernel with regular-orbit coordinates is relatively injective.
Over a field its inclusion splits as an ordinary linear map, hence also
equivariantly.  Consequently an ordinary lift of an equivariant quotient map
can be corrected to an equivariant lift.  This removes any assumption of an
already equivariant preliminary section from the graded construction.
-/

noncomputable section

namespace FourPapers.Universal

variable {K G M N Q C : Type*} [Field K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

theorem exists_equivariantLift_of_coinduced_kernel
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (ha : RepresentationIntertwines ρ υ a)
    (β : M →ₗ[K] N) (hqβ : q.comp β = a)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ F : M →ₗ[K] N, RepresentationIntertwines ρ τ F ∧ q.comp F = a := by
  let H := LinearMap.ker q
  let ρH := invariantSubmoduleRepresentation τ H
    (kernel_invariant_of_intertwines τ υ q hq)
  obtain ⟨s, hs⟩ := H.subtype.exists_leftInverse_of_injective H.ker_subtype
  have hi : RepresentationIntertwines ρH τ H.subtype := by
    intro g x
    rfl
  have hid : RepresentationIntertwines ρH ρH (LinearMap.id : H →ₗ[K] H) := by
    intro g x
    rfl
  obtain ⟨r, hre, hri⟩ := exists_equivariantExtension_of_coinduced
    ρH τ ρH e he H.subtype s hi hs LinearMap.id hid
  let P : N →ₗ[K] N := LinearMap.id - H.subtype.comp r
  have hP : RepresentationIntertwines τ τ P := by
    intro g x
    change τ g x - (r (τ g x)).val = τ g (x - (r x).val)
    rw [hre, map_sub]
    rfl
  have hPH (x : H) : P x.val = 0 := by
    have hrx := congrArg (fun F : H →ₗ[K] H => (F x).val) hri
    change x.val - (r x.val).val = 0
    change (r x.val).val = x.val at hrx
    rw [hrx, sub_self]
  have hqP (x : N) : q (P x) = q x := by
    change q (x - (r x).val) = q x
    rw [map_sub, show q (r x).val = 0 from (r x).property, sub_zero]
  refine ⟨P.comp β, ?_, ?_⟩
  · intro g x
    have hx : β (ρ g x) - τ g (β x) ∈ H := by
      change q (β (ρ g x) - τ g (β x)) = 0
      rw [map_sub, hq]
      have hb1 := congrArg (fun F : M →ₗ[K] Q => F (ρ g x)) hqβ
      have hb2 := congrArg (fun F : M →ₗ[K] Q => F x) hqβ
      change q (β (ρ g x)) = a (ρ g x) at hb1
      change q (β x) = a x at hb2
      rw [hb1, hb2, ha, sub_self]
    have hz := hPH ⟨β (ρ g x) - τ g (β x), hx⟩
    rw [map_sub] at hz
    change P (β (ρ g x)) = τ g (P (β x))
    exact (sub_eq_zero.mp hz).trans (hP g (β x))
  · ext x
    change q (P (β x)) = a x
    rw [hqP]
    exact congrArg (fun F : M →ₗ[K] Q => F x) hqβ

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedKernelLift.lean -/
section


section

/-! # Graded equivariant lifting from regular-orbit kernels

The hypotheses here are explicit linear maps and explicit equivariant coordinate
equivalences for homogeneous kernels.  They are the objects supplied by the
prime-cyclic polynomial calculation.  The finite induction of
`CyclicGradedLift` then produces one parameter-linear lift in every degree.
-/

noncomputable section

namespace FourPapers.Universal
namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (υ : CyclicRepresentation A G Q)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)
variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
variable (hτ : ∀ g n x, x ∈ T n → τ g x ∈ T n)
variable (hq : RepresentationIntertwines τ υ q)

def sourceDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (s.piece n) :=
  invariantSubmoduleRepresentation (restrictRepresentation ρ) (s.piece n)
    (fun g x hx => hρ g n x hx)

def targetDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (T n) :=
  invariantSubmoduleRepresentation (restrictRepresentation τ) (T n)
    (fun g x hx => hτ g n x hx)

def degreeQuotient (n : ℕ) : T n →ₗ[K] Q :=
  (q.restrictScalars K).comp (T n).subtype

def degreeTarget (n : ℕ) : s.piece n →ₗ[K] Q :=
  (a.restrictScalars K).comp (s.piece n).subtype

include hq in
theorem degreeQuotient_intertwines (n : ℕ) :
    RepresentationIntertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n) := by
  intro g x
  exact hq g x.val

def kernelDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (LinearMap.ker (degreeQuotient T q n)) :=
  invariantSubmoduleRepresentation (targetDegreeRepresentation τ T hτ n)
    (LinearMap.ker (degreeQuotient T q n))
    (kernel_invariant_of_intertwines (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n))

variable
  (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
    s.multiplier j • y ∈ T (s.degree j))

include hρ hmult

/-- The full one-degree step, including construction of the lower subspace and
its ordinary linear retraction.  The field assumption is used only to split
that subspace; it is not used to average the group action. -/
theorem degreeLift_of_coinduced_kernel
    {n : ℕ} {f : M →ₗ[A] N} (hf : s.LiftStage ρ τ T q a n f)
    (β : s.piece n →ₗ[K] T n)
    (hβ : RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) β)
    (hqβ : (degreeQuotient T q n).comp β = s.degreeTarget a n)
    {C : Type*} [AddCommGroup C] [Module K C]
    (e : LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation e.toLinearMap) :
    ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L := by
  let ρn := s.sourceDegreeRepresentation ρ hρ n
  let τn := targetDegreeRepresentation τ T hτ n
  let υK := restrictRepresentation (K := K) υ
  let qn := degreeQuotient T q n
  let an := s.degreeTarget a n
  let U : Submodule K (s.piece n) :=
    ((s.cut n).restrictScalars K).comap (s.piece n).subtype
  have hU : ∀ g x, x ∈ U → ρn g x ∈ U := by
    intro g x hx
    change ρ g x.val ∈ s.cut n
    exact s.cut_invariant ρ hρ n g x.val hx
  obtain ⟨r, hr⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  let fU : U →ₗ[K] T n :=
    LinearMap.codRestrict (T n)
      ((f.restrictScalars K).comp ((s.piece n).subtype.comp U.subtype)) (by
        intro x
        exact s.graded_of_generators T hmult f hf.1 n x.val.val x.val.property)
  have hfU : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρn U hU) τn fU := by
    intro g x
    apply Subtype.ext
    exact LiftStage.equivariant_on_cut s ρ τ T q a hf g x.val.val x.property
  have hqfU : qn.comp fU = an.comp U.subtype := by
    ext x
    exact LiftStage.quotient_on_cut s ρ τ T q a hf x.val.val x.property
  have hqn : RepresentationIntertwines τn υK qn :=
    degreeQuotient_intertwines τ υ T q hτ hq n
  obtain ⟨L, hLeq, hLU, hqL⟩ := equivariant_lift_extend_subspace
    ρn τn υK U hU r hr qn hqn an β hβ hqβ fU hfU hqfU e he
  refine ⟨(T n).subtype.comp L, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (L x).property
  · intro g x
    exact congrArg Subtype.val (hLeq g x)
  · intro x
    exact congrArg (fun F : s.piece n →ₗ[K] Q => F x) hqL
  · intro x hx
    let ux : U := ⟨x, hx⟩
    exact congrArg (fun F : U →ₗ[K] T n => (F ux).val) hLU

/-- Graded parameter-linear equivariant lifting, with every one-degree
extension proved from regular-orbit coordinates for its actual kernel. -/
theorem exists_equivariantGradedLift_of_coinduced_kernels [Fintype I]
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hβ : ∀ n, RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
      (targetDegreeRepresentation τ T hτ n) (β n))
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  apply s.exists_equivariantGradedLift_of_degreeExtensions ρ τ T q a hρ hmult
  intro n f hf
  exact s.degreeLift_of_coinduced_kernel ρ τ υ T q a hρ hτ hq hmult hf
    (β n) (hβ n) (hqβ n) (e n) (he n)

/-- The form used for the actual face rings: the preliminary lift is required
only to preserve degree and the prescribed quotient map.  All equivariance is
constructed from the explicit regular-orbit kernels. -/
theorem exists_equivariantGradedLift_of_ordinary_lifts [Fintype I]
    (ha : RepresentationIntertwines ρ υ a)
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hqβ : ∀ n, (degreeQuotient T q n).comp (β n) = s.degreeTarget a n)
    (e : ∀ n, LinearMap.ker (degreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (kernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have hβeq : ∀ n, ∃ F : s.piece n →ₗ[K] T n,
      RepresentationIntertwines (s.sourceDegreeRepresentation ρ hρ n)
        (targetDegreeRepresentation τ T hτ n) F ∧
      (degreeQuotient T q n).comp F = s.degreeTarget a n := by
    intro n
    apply exists_equivariantLift_of_coinduced_kernel
      (s.sourceDegreeRepresentation ρ hρ n) (targetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (degreeQuotient T q n)
      (degreeQuotient_intertwines τ υ T q hτ hq n) (s.degreeTarget a n)
      (fun g x => ha g x.val) (β n) (hqβ n) (e n) (he n)
  choose F hF hqF using hβeq
  exact s.exists_equivariantGradedLift_of_coinduced_kernels
    ρ τ υ T q a hρ hτ hq hmult C F hF hqF e he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanGrading.lean -/
section


section

/-! # The actual Boolean descent basis satisfies the lifting hypotheses

The scalar basis and parameter basis are the already proved bases of the
actual barycentric face ring.  Its homogeneous pieces agree with ordinary
rank-weighted polynomial degree, not a grading chosen to make lifting easier.
-/

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem colorOrdinaryDegree_eq_zero_iff (m : ColorExponent V) :
    colorOrdinaryDegree m = 0 ↔ m = 0 := by
  constructor
  · intro hm
    apply Finsupp.ext
    intro c
    have hc : m c ≤ colorOrdinaryDegree m := by
      rw [colorOrdinaryDegree_fintype]
      calc
        m c = m c * 1 := (Nat.mul_one _).symm
        _ ≤ m c * (c.val + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
        _ ≤ ∑ i : Fin (Fintype.card V), m i * (i.val + 1) :=
          Finset.single_le_sum (f := fun i : Fin (Fintype.card V) => m i * (i.val + 1))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    change m c = 0
    omega
  · rintro rfl
    simp [colorOrdinaryDegree]

@[simp] theorem booleanParameterBasis_zero_parameter
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanParameterBasis (K := K) (σ, 0) = booleanColorBasis (K := K) σ := by
  simp [parameterDescentVector, colorPower]

/-- The exact positive graded free-basis structure of the Boolean barycentric
ring used in the prime-rank lift. -/
def booleanScalarGradedBasis :
    ScalarGradedBasis K (MvPolynomial (Fin (Fintype.card V)) K)
      (BooleanBarycentricRing V K)
      (VertexOrdering (Fintype.card V) V)
      (VertexOrdering (Fintype.card V) V × ColorExponent V) where
  parameterBasis := booleanColorBasis
  coefficientBasis := booleanParameterBasis
  generatorDegree σ := colorOrdinaryDegree (descentColorExponent σ)
  degree p := colorOrdinaryDegree p.2 + colorOrdinaryDegree (descentColorExponent p.1)
  parent := Prod.fst
  multiplier p := MvPolynomial.monomial p.2 1
  coefficient_eq p := by
    rw [booleanParameterBasis_apply, booleanColorBasis_apply]
    exact parameterDescentVector_eq_monomial_smul p
  parent_degree_le p := Nat.le_add_left _ _
  equal_degree_eq p hp := by
    obtain ⟨σ, m⟩ := p
    change colorOrdinaryDegree m + colorOrdinaryDegree (descentColorExponent σ) =
      colorOrdinaryDegree (descentColorExponent σ) at hp
    have hm : colorOrdinaryDegree m = 0 := by omega
    have hm0 := (colorOrdinaryDegree_eq_zero_iff m).mp hm
    subst m
    exact booleanParameterBasis_zero_parameter σ
  generator_homogeneous σ p hp := by
    rw [← booleanParameterBasis_zero_parameter, Module.Basis.repr_self]
    have hne : (σ, (0 : ColorExponent V)) ≠ p := by
      intro he
      subst p
      exact hp (by simp [colorOrdinaryDegree])
    simp [Finsupp.single_apply, hne]

theorem basisDegreeProjection_eq_self_iff_mem
    {I M : Type*} [AddCommGroup M] [Module K M]
    (b : Module.Basis I K M) (degree : I → ℕ) (n : ℕ) (x : M) :
    basisDegreeProjection b degree n x = x ↔
      x ∈ basisOrdinaryDegreePiece b degree n := by
  constructor
  · intro hx i hi
    have h := congrArg (fun y => b.repr y i) hx
    rw [basisDegreeProjection_repr, if_neg hi] at h
    exact h.symm
  · intro hx
    apply b.repr.injective
    ext i
    rw [basisDegreeProjection_repr]
    by_cases hi : degree i = n
    · rw [if_pos hi]
    · rw [if_neg hi, hx i hi]

theorem booleanParameterDegreeProjection_eq (n : ℕ) :
    basisDegreeProjection (booleanChainBasis (V := V) (K := K))
      (fun a => chainOrdinaryDegree a.val) n =
    basisDegreeProjection (booleanParameterBasis (V := V) (K := K))
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n := by
  apply basisDegreeProjection_eq_of_homogeneous
  intro a p hp
  rw [booleanParameterBasis_apply]
  apply parameterDescentVector_repr_color
  intro he
  apply hp
  rw [← colorOrdinaryDegree_chainColorDegree, he, colorOrdinaryDegree_add]

/-- Faithfulness of the homogeneous pieces in the lifting construction: they
are exactly the standard chain-monomial components of ordinary degree `n`. -/
theorem booleanScalarGradedBasis_piece_eq (n : ℕ) :
    (booleanScalarGradedBasis (V := V) (K := K)).piece n =
      basisOrdinaryDegreePiece (booleanChainBasis (V := V) (K := K))
        (fun a => chainOrdinaryDegree a.val) n := by
  ext x
  change x ∈ basisOrdinaryDegreePiece booleanParameterBasis
      (fun p => colorOrdinaryDegree p.2 +
        colorOrdinaryDegree (descentColorExponent p.1)) n ↔ _
  rw [← basisDegreeProjection_eq_self_iff_mem,
    ← basisDegreeProjection_eq_self_iff_mem,
    booleanParameterDegreeProjection_eq]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimeRetraction.lean -/
section


section

/-! # The prime-rank orbit retraction in characteristic `p`

The map first identifies all vertex variables with one variable, retains
only exponents divisible by `p`, and divides those exponents by `p`.  Its
target variable has internal degree `p`.  These are actual polynomial maps,
and parameter compatibility is proved from the binomial coefficients.
-/

noncomputable section

namespace FourPapers.Universal

open Classical
open scoped BigOperators Polynomial

variable {K V : Type*} [CommRing K]

def coefficientCompression (p : ℕ) : K[X] →ₗ[K] K[X] :=
  Polynomial.lsum fun n => if p ∣ n then Polynomial.monomial (n / p) else 0

@[simp] theorem coefficientCompression_monomial (p n : ℕ) (a : K) :
    coefficientCompression p (Polynomial.monomial n a) =
      if p ∣ n then Polynomial.monomial (n / p) a else 0 := by
  by_cases h : p ∣ n <;> simp [coefficientCompression, Polynomial.lsum_apply, h]

@[simp] theorem coefficientCompression_one (p : ℕ) :
    coefficientCompression (K := K) p 1 = 1 := by
  simpa using coefficientCompression_monomial p 0 (1 : K)

theorem coefficientCompression_X_pow_mul (p : ℕ) (hp : 0 < p) (f : K[X]) :
    coefficientCompression p (Polynomial.X ^ p * f) =
      Polynomial.X * coefficientCompression p f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [mul_add, hf, hg]
  | monomial n a =>
      have hdiv : p ∣ n + p ↔ p ∣ n := by
        simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_self,
          add_zero, Nat.mod_mod]
      rw [Polynomial.X_pow_mul_monomial, coefficientCompression_monomial,
        coefficientCompression_monomial]
      by_cases hn : p ∣ n
      · rw [if_pos (hdiv.mpr hn), if_pos hn, Nat.add_div_right n hp]
        simpa using (Polynomial.X_pow_mul_monomial 1 (n / p) a).symm
      · rw [if_neg (fun h => hn (hdiv.mp h)), if_neg hn, mul_zero]

/-- Diagonal evaluation is invariant under every relabeling of the vertices. -/
def diagonalEvaluation : MvPolynomial V K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun _ => Polynomial.X

@[simp] theorem diagonalEvaluation_rename (e : V → V) (f : MvPolynomial V K) :
    diagonalEvaluation (MvPolynomial.rename e f) = diagonalEvaluation f := by
  unfold diagonalEvaluation
  rw [MvPolynomial.aeval_rename]
  rfl

theorem diagonalEvaluation_monomial (a : V →₀ ℕ) (c : K) :
    diagonalEvaluation (MvPolynomial.monomial a c) =
      Polynomial.monomial (a.sum fun _ n => n) c := by
  rw [diagonalEvaluation, MvPolynomial.aeval_monomial]
  change Polynomial.C c * (∏ v ∈ a.support, Polynomial.X ^ a v) = _
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.C_mul_X_pow_eq_monomial]
  rfl

variable [Fintype V]

theorem diagonalEvaluation_esymm (i : ℕ) :
    diagonalEvaluation (MvPolynomial.esymm V K i) =
      (Fintype.card V).choose i • (Polynomial.X : K[X]) ^ i := by
  unfold diagonalEvaluation MvPolynomial.esymm
  rw [map_sum]
  calc
    ∑ t ∈ Finset.univ.powersetCard i,
        (MvPolynomial.aeval (fun _ : V => (Polynomial.X : K[X])))
          (∏ v ∈ t, MvPolynomial.X v) =
        ∑ _t ∈ Finset.univ.powersetCard i, (Polynomial.X : K[X]) ^ i := by
      apply Finset.sum_congr rfl
      intro t ht
      have hcard : t.card = i := (Finset.mem_powersetCard.mp ht).2
      simp only [map_prod, MvPolynomial.aeval_X, Finset.prod_const, hcard]
    _ = _ := by simp

def primeOrbitRetraction (p : ℕ) : MvPolynomial V K →ₗ[K] K[X] :=
  (coefficientCompression p).comp diagonalEvaluation.toLinearMap

@[simp] theorem primeOrbitRetraction_monomial (p : ℕ) (a : V →₀ ℕ) (c : K) :
    primeOrbitRetraction p (MvPolynomial.monomial a c) =
      if p ∣ a.sum (fun _ n => n) then
        Polynomial.monomial ((a.sum fun _ n => n) / p) c else 0 := by
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    diagonalEvaluation_monomial, coefficientCompression_monomial]

@[simp] theorem primeOrbitRetraction_one (p : ℕ) :
    primeOrbitRetraction (V := V) (K := K) p 1 = 1 := by
  simp [primeOrbitRetraction]

@[simp] theorem primeOrbitRetraction_rename (p : ℕ) (e : V → V)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.rename e f) = primeOrbitRetraction p f := by
  simp [primeOrbitRetraction]

variable (p : ℕ) [CharP K p]

private theorem prime_dvd_interior_binomial (hp : p.Prime) {i : ℕ}
    (hi : 0 < i) (hip : i < p) : p ∣ p.choose i := by
  have hmul := Nat.add_one_mul_choose_eq (p - 1) (i - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p),
    Nat.sub_add_cancel (by omega : 1 ≤ i)] at hmul
  have hdiv : p ∣ p.choose i * i := by
    rw [← hmul]
    exact dvd_mul_right _ _
  exact (hp.dvd_mul.mp hdiv).resolve_right (Nat.not_dvd_of_pos_of_lt hi hip)

theorem primeOrbitRetraction_lower_parameter (hp : p.Prime)
    (hcard : Fintype.card V = p) {i : ℕ} (hi : 0 < i) (hip : i < p)
    (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K i * f) = 0 := by
  have hc : (p.choose i : K[X]) = 0 :=
    (CharP.cast_eq_zero_iff (K[X]) p _).mpr (prime_dvd_interior_binomial p hp hi hip)
  have he : diagonalEvaluation (MvPolynomial.esymm V K i) = 0 := by
    rw [diagonalEvaluation_esymm, hcard, nsmul_eq_mul, hc, zero_mul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, zero_mul, map_zero]

theorem primeOrbitRetraction_top_parameter (hp : 0 < p)
    (hcard : Fintype.card V = p) (f : MvPolynomial V K) :
    primeOrbitRetraction p (MvPolynomial.esymm V K p * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  have he : diagonalEvaluation (MvPolynomial.esymm V K p) =
      (Polynomial.X : K[X]) ^ p := by
    rw [diagonalEvaluation_esymm, hcard, Nat.choose_self, one_smul]
  simp only [primeOrbitRetraction, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, he, coefficientCompression_X_pow_mul p hp]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicAugmentationKernel.lean -/
section

section
/-! # An explicit basis of an augmentation kernel

For a finite permutation basis with a distinguished fixed vector δ, the
augmentation kernel has basis e_i − e_δ, i ≠ δ. The construction is valid
over every commutative coefficient ring and carries the expected permutation
action. It is used degreewise in the exceptional prime-rank lifting argument.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset

variable {I K : Type*} [Fintype I] [CommRing K]

theorem sum_eq_pivot_add_sum_complement {M : Type*} [AddCommMonoid M]
    (i₀ : I) (f : I → M) :
    (∑ i, f i) = f i₀ + ∑ i : {i : I // i ≠ i₀}, f i.val := by
  have he : (∑ i : {i : I // i ≠ i₀}, f i.val) =
      ∑ i ∈ Finset.univ.erase i₀, f i :=
    (Finset.sum_subtype (Finset.univ.erase i₀) (fun i => by simp) f).symm
  rw [he]
  calc
    (∑ i, f i) = (∑ i ∈ Finset.univ.erase i₀, f i) + f i₀ :=
      (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i₀)).symm
    _ = f i₀ + ∑ i ∈ Finset.univ.erase i₀, f i := add_comm _ _

def finiteAugmentation (K : Type*) [CommRing K] : (I → K) →ₗ[K] K where
  toFun x := ∑ i, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

def augmentedVector (i₀ : I) (x : {i : I // i ≠ i₀} → K) : I → K :=
  fun i => if h : i = i₀ then -(∑ j, x j) else x ⟨i, h⟩

theorem augmentedVector_sum (i₀ : I) (x : {i : I // i ≠ i₀} → K) :
    (∑ i, augmentedVector i₀ x i) = 0 := by
  rw [sum_eq_pivot_add_sum_complement i₀]
  have hrest : (∑ i : {i : I // i ≠ i₀}, augmentedVector i₀ x i.val) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [augmentedVector, dif_neg i.property]
  rw [hrest]
  simp [augmentedVector]

def augmentationKernelEquiv (K : Type*) [CommRing K] (i₀ : I) :
    ({i : I // i ≠ i₀} → K) ≃ₗ[K] LinearMap.ker (finiteAugmentation (I := I) K) where
  toFun x := ⟨augmentedVector i₀ x, augmentedVector_sum i₀ x⟩
  invFun x := fun i => x.val i.val
  left_inv x := by
    funext i
    simp only [augmentedVector, dif_neg i.property]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      simp only [augmentedVector, dif_pos rfl]
      have hx : x.val i₀ + ∑ j : {i : I // i ≠ i₀}, x.val j.val = 0 := by
        rw [← sum_eq_pivot_add_sum_complement]
        exact x.property
      exact (eq_neg_iff_add_eq_zero.mpr hx).symm
    · simp only [augmentedVector, dif_neg hi]
  map_add' x y := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.sum_add_distrib, neg_add, add_comm]
  map_smul' c x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀ <;>
      simp [augmentedVector, hi, Finset.mul_sum, smul_eq_mul]

def augmentationKernelBasis (K : Type*) [CommRing K] (i₀ : I) :
    Module.Basis {i : I // i ≠ i₀} K (LinearMap.ker (finiteAugmentation (I := I) K)) :=
  (Pi.basisFun K {i : I // i ≠ i₀}).map (augmentationKernelEquiv K i₀)

/-- These really are the difference vectors in the original finite module. -/
theorem augmentationKernelBasis_apply (i₀ : I) (j : {i : I // i ≠ i₀}) (i : I) :
    (augmentationKernelBasis K i₀ j).val i =
      (if i = j.val then 1 else 0) - (if i = i₀ then 1 else 0) := by
  by_cases hi : i = i₀
  · subst i
    have hj : i₀ ≠ j.val := Ne.symm j.property
    simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hj]
  · simp [augmentationKernelBasis, Module.Basis.map_apply, augmentationKernelEquiv,
      augmentedVector, Pi.basisFun_apply, Pi.single_apply, hi, Subtype.ext_iff, eq_comm]

/-- A permutation fixing the pivot permutes the difference-basis vectors.
The equation is in the original function space, so it applies immediately
after any equivariant monomial-basis identification. -/
theorem augmentationKernelBasis_covariant (i₀ : I) (e : Equiv.Perm I) (he : e i₀ = i₀)
    (j : {i : I // i ≠ i₀}) :
    (fun i => (augmentationKernelBasis K i₀ j).val (e.symm i)) =
      (augmentationKernelBasis K i₀
        ⟨e j.val, by
          intro h
          apply j.property
          exact e.injective (h.trans he.symm)⟩).val := by
  funext i
  rw [augmentationKernelBasis_apply, augmentationKernelBasis_apply]
  have h₁ : e.symm i = j.val ↔ i = e j.val := by
    constructor
    · intro h
      simpa using congrArg e h
    · intro h
      rw [h, Equiv.symm_apply_apply]
  have h₀ : e.symm i = i₀ ↔ i = i₀ := by
    constructor
    · intro h
      have hh := congrArg e h
      simpa only [Equiv.apply_symm_apply, he] using hh
    · intro h
      subst i
      exact e.symm_apply_eq.mpr he.symm
  simp only [h₁, h₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousCoordinates.lean -/
section

section
/-! # Actual homogeneous polynomial coordinates for cyclic lifting

The homogeneous component is the existing `polynomialDegreePiece` submodule
of the ordinary multivariate polynomial ring. Evaluation at all variables
equal to one becomes the finite coefficient sum in its monomial coordinates.
Consequently its actual kernel has the difference-monomial basis used by the
prime-cyclic lifting construction.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

abbrev CyclicPolynomialPiece (n : ℕ) :=
  polynomialDegreePiece (V := ZMod p) (K := K) n

theorem cyclicPolynomialPiece_mem_iff_supported (n : ℕ) (f : MvPolynomial (ZMod p) K) :
    f ∈ CyclicPolynomialPiece p K n ↔
      f.coeff ∈ Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} := by
  rw [Finsupp.mem_supported']
  change (∀ a : ZMod p →₀ ℕ, vertexDegree (fun x => a x) ≠ n → f.coeff a = 0) ↔ _
  simp only [vertexDegree, ← Finsupp.degree_eq_sum, Set.mem_setOf_eq]

def cyclicPolynomialSupportedEquiv (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K]
      Finsupp.supported K K {a : ZMod p →₀ ℕ | a.degree = n} where
  toFun f := ⟨f.val.coeff,
    (cyclicPolynomialPiece_mem_iff_supported p K n f.val).mp f.property⟩
  invFun f := ⟨(MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val, by
    apply (cyclicPolynomialPiece_mem_iff_supported p K n _).mpr
    change (MvPolynomial.basisMonomials (ZMod p) K).repr
      ((MvPolynomial.basisMonomials (ZMod p) K).repr.symm f.val) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.symm_apply_apply f.val
  right_inv f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.apply_symm_apply f.val
  map_add' f g := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (MvPolynomial.basisMonomials (ZMod p) K).repr.map_smul c f.val

def cyclicPolynomialCoordinates (n : ℕ) :
    CyclicPolynomialPiece p K n ≃ₗ[K] (CyclicHomogeneousExponent p n → K) :=
  (cyclicPolynomialSupportedEquiv p K n).trans
    ((Finsupp.supportedEquivFinsupp {a : ZMod p →₀ ℕ | a.degree = n}).trans
      (Finsupp.linearEquivFunOnFinite K K (CyclicHomogeneousExponent p n)))

@[simp] theorem cyclicPolynomialCoordinates_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n f a = f.val.coeff a.val := rfl

def cyclicHomogeneousMonomial (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    CyclicPolynomialPiece p K n :=
  ⟨MvPolynomial.monomial a.val 1, by
    have hd : vertexDegree (fun x => a.val x) = n := by
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact a.property
    intro b hb
    have hne : a.val ≠ b := by
      intro he
      subst b
      exact hb hd
    simp only [MvPolynomial.coeff_monomial, if_neg hne]⟩

@[simp] theorem cyclicPolynomialCoordinates_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) = Pi.single a 1 := by
  funext b
  rw [cyclicPolynomialCoordinates_apply]
  simp [cyclicHomogeneousMonomial, MvPolynomial.coeff_monomial,
    Pi.single_apply, Subtype.ext_iff, eq_comm]

def cyclicHomogeneousMonomialBasis (n : ℕ) :
    Module.Basis (CyclicHomogeneousExponent p n) K (CyclicPolynomialPiece p K n) :=
  (Pi.basisFun K (CyclicHomogeneousExponent p n)).map (cyclicPolynomialCoordinates p K n).symm

theorem cyclicHomogeneousMonomialBasis_apply (n : ℕ) (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousMonomialBasis p K n a = cyclicHomogeneousMonomial p K n a := by
  apply (cyclicPolynomialCoordinates p K n).injective
  simp only [cyclicHomogeneousMonomialBasis, Module.Basis.map_apply,
    LinearEquiv.apply_symm_apply, Pi.basisFun_apply, cyclicPolynomialCoordinates_monomial]

theorem rename_equiv_coefficient (e : Equiv.Perm (ZMod p))
    (f : MvPolynomial (ZMod p) K) (a : ZMod p →₀ ℕ) :
    (MvPolynomial.rename e f).coeff a = f.coeff (a.mapDomain e.symm) := by
  have he : (a.mapDomain e.symm).mapDomain e = a := by
    rw [← Finsupp.mapDomain_comp]
    have hh : (e : ZMod p → ZMod p) ∘ e.symm = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hh, Finsupp.mapDomain_id]
  simpa only [he] using
    MvPolynomial.coeff_rename_mapDomain e e.injective f (a.mapDomain e.symm)

def cyclicHomogeneousRename (n : ℕ) (e : Equiv.Perm (ZMod p)) :
    Module.End K (CyclicPolynomialPiece p K n) where
  toFun f := ⟨MvPolynomial.rename e f.val, by
    intro a ha
    rw [rename_equiv_coefficient]
    apply f.property
    have hd : vertexDegree (fun x => (a.mapDomain e.symm) x) = vertexDegree (fun x => a x) := by
      simp only [vertexDegree, ← Finsupp.degree_eq_sum, Finsupp.degree_mapDomain]
    rwa [hd]⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

theorem cyclicPolynomialCoordinates_rename (n : ℕ) (e : Equiv.Perm (ZMod p))
    (f : CyclicPolynomialPiece p K n) (a : CyclicHomogeneousExponent p n) :
    cyclicPolynomialCoordinates p K n (cyclicHomogeneousRename p K n e f) a =
      cyclicPolynomialCoordinates p K n f
        ⟨a.val.mapDomain e.symm, by rw [Finsupp.degree_mapDomain]; exact a.property⟩ := by
  exact rename_equiv_coefficient p K e f.val a.val

/-- Literal evaluation at the all-one root assignment, restricted to the
actual homogeneous polynomial component. -/
def cyclicHomogeneousAugmentation (n : ℕ) : CyclicPolynomialPiece p K n →ₗ[K] K :=
  (MvPolynomial.aeval (fun _ : ZMod p => (1 : K))).toLinearMap.comp
    (CyclicPolynomialPiece p K n).subtype

theorem cyclicHomogeneousAugmentation_eq_sum (n : ℕ) :
    cyclicHomogeneousAugmentation p K n =
      (finiteAugmentation (I := CyclicHomogeneousExponent p n) K).comp
        (cyclicPolynomialCoordinates p K n).toLinearMap := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  change MvPolynomial.aeval (fun _ : ZMod p => (1 : K))
      (MvPolynomial.monomial a.val 1) =
    ∑ i, cyclicPolynomialCoordinates p K n (cyclicHomogeneousMonomial p K n a) i
  rw [cyclicPolynomialCoordinates_monomial]
  simp [MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, Finsupp.prod]

def cyclicHomogeneousAugmentationKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      LinearMap.ker (finiteAugmentation (I := CyclicHomogeneousExponent p n) K) where
  toFun f := ⟨cyclicPolynomialCoordinates p K n f.val, by
    change finiteAugmentation K (cyclicPolynomialCoordinates p K n f.val) = 0
    have hh : cyclicHomogeneousAugmentation p K n f.val = 0 := f.property
    simp only [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe] at hh
    exact hh⟩
  invFun f := ⟨(cyclicPolynomialCoordinates p K n).symm f.val, by
    change cyclicHomogeneousAugmentation p K n
      ((cyclicPolynomialCoordinates p K n).symm f.val) = 0
    rw [cyclicHomogeneousAugmentation_eq_sum, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ f.val
  right_inv f := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ f.val
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact map_smul _ _ _

def cyclicHomogeneousPivot (n : ℕ) (hn : p ∣ n) : CyclicHomogeneousExponent p n :=
  ⟨cyclicConstantExponent p (n / p), by
    rw [cyclicConstantExponent_degree, Nat.mul_comm, Nat.div_mul_cancel hn]⟩

def cyclicHomogeneousDifferenceBasis (n : ℕ) (hn : p ∣ n) :
    Module.Basis {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} K
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn)).map
    (cyclicHomogeneousAugmentationKernelEquiv p K n).symm

/-- The actual kernel vectors are differences of the original monomials;
the pivot is the unique invariant exponent vector in degree n. -/
theorem cyclicHomogeneousDifferenceBasis_apply (n : ℕ) (hn : p ∣ n)
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    (cyclicHomogeneousDifferenceBasis p K n hn a).val =
      cyclicHomogeneousMonomial p K n a.val -
        cyclicHomogeneousMonomial p K n (cyclicHomogeneousPivot p n hn) := by
  apply (cyclicPolynomialCoordinates p K n).injective
  have hleft : cyclicPolynomialCoordinates p K n
      (cyclicHomogeneousDifferenceBasis p K n hn a).val =
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val := by
    change cyclicPolynomialCoordinates p K n
      ((cyclicPolynomialCoordinates p K n).symm
        (augmentationKernelBasis K (cyclicHomogeneousPivot p n hn) a).val) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [hleft, map_sub, cyclicPolynomialCoordinates_monomial,
    cyclicPolynomialCoordinates_monomial]
  funext b
  rw [augmentationKernelBasis_apply]
  simp only [Pi.single_apply, Pi.sub_apply, eq_comm]
  split_ifs <;> rfl

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicRetractionKernel.lean -/
section


section

/-! # The actual homogeneous kernel of the prime orbit retraction

In degree `n`, the orbit retraction is zero if `p` does not divide `n`.
Otherwise it is the coefficient sum, followed by the monomial embedding in
degree `n / p`.  This identifies its actual kernel with the free cyclic
permutation modules used by the equivariant lifting argument.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

def cyclicHomogeneousOrbitRetraction (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K] K[X] :=
  (primeOrbitRetraction p).comp (CyclicPolynomialPiece p K n).subtype

@[simp] theorem cyclicHomogeneousAugmentation_monomial (n : ℕ)
    (a : CyclicHomogeneousExponent p n) :
    cyclicHomogeneousAugmentation p K n (cyclicHomogeneousMonomial p K n a) = 1 := by
  change MvPolynomial.eval (fun _ => (1 : K)) (MvPolynomial.monomial a.val (1 : K)) = 1
  simp [MvPolynomial.eval_monomial]

theorem cyclicHomogeneousOrbitRetraction_eq (n : ℕ) :
    cyclicHomogeneousOrbitRetraction p K n =
      if p ∣ n then
        (Polynomial.monomial (n / p)).comp (cyclicHomogeneousAugmentation p K n)
      else 0 := by
  apply (cyclicHomogeneousMonomialBasis p K n).ext
  intro a
  rw [cyclicHomogeneousMonomialBasis_apply]
  have ha : a.val.sum (fun _ i => i) = n := a.property
  have he : cyclicHomogeneousOrbitRetraction p K n
      (cyclicHomogeneousMonomial p K n a) =
      if p ∣ n then Polynomial.monomial (n / p) 1 else 0 := by
    change primeOrbitRetraction p (MvPolynomial.monomial a.val (1 : K)) = _
    rw [primeOrbitRetraction_monomial, ha]
  rw [he]
  by_cases hn : p ∣ n
  · simp only [if_pos hn, LinearMap.comp_apply, cyclicHomogeneousAugmentation_monomial]
  · simp only [if_neg hn, LinearMap.zero_apply]

theorem cyclicHomogeneousOrbitRetraction_apply (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n f =
      if p ∣ n then Polynomial.monomial (n / p)
        (cyclicHomogeneousAugmentation p K n f) else 0 := by
  rw [cyclicHomogeneousOrbitRetraction_eq]
  split_ifs <;> rfl

theorem cyclicHomogeneousOrbitKernel_eq_top (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) = ⊤ := by
  rw [cyclicHomogeneousOrbitRetraction_eq, if_neg hn, LinearMap.ker_zero]

theorem cyclicHomogeneousOrbitKernel_eq_augmentationKernel (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) =
      LinearMap.ker (cyclicHomogeneousAugmentation p K n) := by
  ext f
  change cyclicHomogeneousOrbitRetraction p K n f = 0 ↔
    cyclicHomogeneousAugmentation p K n f = 0
  rw [cyclicHomogeneousOrbitRetraction_apply, if_pos hn]
  exact Polynomial.monomial_eq_zero_iff _ _

def cyclicOrbitKernelCoordinatesOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (CyclicHomogeneousExponent p n → K) :=
  ((LinearEquiv.ofEq _ _ (cyclicHomogeneousOrbitKernel_eq_top p K n hn)).trans
    Submodule.topEquiv).trans (cyclicPolynomialCoordinates p K n)

@[simp] theorem cyclicOrbitKernelCoordinatesOfNotDvd_apply (n : ℕ) (hn : ¬p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : CyclicHomogeneousExponent p n) :
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f a = f.val.val.coeff a.val := by
  change cyclicPolynomialCoordinates p K n f.val a = f.val.val.coeff a.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a

def cyclicOrbitKernelCoordinatesOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      ({a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn} → K) :=
  ((LinearEquiv.ofEq _ _
    (cyclicHomogeneousOrbitKernel_eq_augmentationKernel p K n hn)).trans
      (cyclicHomogeneousAugmentationKernelEquiv p K n)).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicOrbitKernelCoordinatesOfDvd_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (a : {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}) :
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f a = f.val.val.coeff a.val.val := by
  change cyclicPolynomialCoordinates p K n f.val a.val = f.val.val.coeff a.val.val
  exact cyclicPolynomialCoordinates_apply p K n f.val a.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicHomogeneousAction.lean -/
section

section
/-! # Actual cyclic polynomial actions and free kernel coordinates -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem primeTranslation_symm (g : PrimeCycleGroup p) :
    (Equiv.addLeft g.toAdd).symm = Equiv.addLeft (g⁻¹).toAdd := by
  apply Equiv.ext
  intro x
  apply (Equiv.addLeft g.toAdd).injective
  rw [Equiv.apply_symm_apply]
  change x = g.toAdd + (-g.toAdd + x)
  abel

def cyclicPolynomialRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p) (CyclicPolynomialPiece p K n) where
  toFun g := cyclicHomogeneousRename p K n (Equiv.addLeft g.toAdd)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (0 : ZMod p)) f.val = f.val
    have he : (Equiv.addLeft (0 : ZMod p) : ZMod p → ZMod p) = id := by
      funext x
      exact zero_add x
    rw [he, MvPolynomial.rename_id_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change MvPolynomial.rename (Equiv.addLeft (g.toAdd + h.toAdd)) f.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (MvPolynomial.rename (Equiv.addLeft h.toAdd) f.val)
    rw [MvPolynomial.rename_rename]
    have he : (Equiv.addLeft (g.toAdd + h.toAdd) : ZMod p → ZMod p) =
        (Equiv.addLeft g.toAdd) ∘ (Equiv.addLeft h.toAdd) := by
      funext x
      exact add_assoc g.toAdd h.toAdd x
    rw [he]

theorem cyclicPolynomialCoordinates_equivariant (n : ℕ) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicPolynomialRepresentation p K n)
      permutationFunctionRepresentation (cyclicPolynomialCoordinates p K n).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val).coeff a.val =
    f.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val a.val

theorem cyclicHomogeneousAugmentation_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousAugmentation p K n f := by
  letI := cyclicHomogeneousExponentAction p n
  rw [cyclicHomogeneousAugmentation_eq_sum]
  change (∑ a, cyclicPolynomialCoordinates p K n (cyclicPolynomialRepresentation p K n g f) a) =
    ∑ a, cyclicPolynomialCoordinates p K n f a
  calc
    _ = ∑ a, cyclicPolynomialCoordinates p K n f (g⁻¹ • a) :=
      congrArg (fun z : CyclicHomogeneousExponent p n → K => ∑ a, z a)
        (cyclicPolynomialCoordinates_equivariant p K n g f)
    _ = _ := Fintype.sum_equiv (MulAction.toPerm (g⁻¹)) _ _ (fun _ => rfl)

def cyclicAugmentationKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousAugmentation p K n)) (by
      intro g f hf
      change cyclicHomogeneousAugmentation p K n (cyclicPolynomialRepresentation p K n g f) = 0
      rw [cyclicHomogeneousAugmentation_invariant]
      exact hf)

theorem cyclicHomogeneousPivot_fixed (n : ℕ) (hn : p ∣ n) (g : PrimeCycleGroup p) :
    (cyclicHomogeneousExponentAction p n).smul g (cyclicHomogeneousPivot p n hn) =
      cyclicHomogeneousPivot p n hn := by
  apply Subtype.ext
  exact primeShift_constant_exponent_fixed p (n / p) g

abbrev CyclicNonpivotExponent (n : ℕ) (hn : p ∣ n) :=
  {a : CyclicHomogeneousExponent p n // a ≠ cyclicHomogeneousPivot p n hn}

def cyclicNonpivotExponentAction (n : ℕ) (hn : p ∣ n) :
    MulAction (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn) := by
  letI := cyclicHomogeneousExponentAction p n
  exact {
    smul := fun g a => ⟨g • a.val, by
      intro h
      have hh := congrArg (fun b => g⁻¹ • b) h
      have hpivot : g⁻¹ • cyclicHomogeneousPivot p n hn =
          cyclicHomogeneousPivot p n hn := cyclicHomogeneousPivot_fixed p n hn g⁻¹
      rw [inv_smul_smul, hpivot] at hh
      exact a.property hh⟩
    one_smul := fun a => Subtype.ext (one_smul (PrimeCycleGroup p) a.val)
    mul_smul := fun g h a => Subtype.ext (mul_smul g h a.val) }

/-- Excluding the unique invariant exponent vector leaves a free action. -/
theorem cyclicNonpivotExponent_no_fixed (n : ℕ) (hn : p ∣ n)
    (g : PrimeCycleGroup p) (a : CyclicNonpivotExponent p n hn)
    (hfix : (cyclicNonpivotExponentAction p n hn).smul g a = a) : g = 1 := by
  by_contra hg
  apply a.property
  apply Subtype.ext
  exact cyclicHomogeneous_nonidentity_fixed_unique p n a.val g hg
    (congrArg Subtype.val hfix)

def cyclicAugmentationComplementCoordinates (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousAugmentation p K n) ≃ₗ[K]
      (CyclicNonpivotExponent p n hn → K) :=
  (cyclicHomogeneousAugmentationKernelEquiv p K n).trans
    (augmentationKernelEquiv K (cyclicHomogeneousPivot p n hn)).symm

@[simp] theorem cyclicAugmentationComplementCoordinates_apply (n : ℕ) (hn : p ∣ n)
    (f : LinearMap.ker (cyclicHomogeneousAugmentation p K n))
    (a : CyclicNonpivotExponent p n hn) :
    cyclicAugmentationComplementCoordinates p K n hn f a = f.val.val.coeff a.val.val := rfl

/-- In the actual homogeneous kernel, the difference-monomial coordinates
carry the free permutation representation on nonpivot exponents. -/
theorem cyclicAugmentationComplementCoordinates_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicAugmentationKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicAugmentationComplementCoordinates p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicAugmentationComplementCoordinates p K n hn
      (cyclicAugmentationKernelRepresentation p K n g f) a =
    cyclicAugmentationComplementCoordinates p K n hn f (g⁻¹ • a)
  rw [cyclicAugmentationComplementCoordinates_apply,
    cyclicAugmentationComplementCoordinates_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrbitKernelCoinduced.lean -/
section


section

/-! # Coinduced coordinates for the actual orbit-retraction kernel

The representation here is the literal variable-renaming action restricted to
the kernel of the homogeneous orbit retraction.  The coordinate equivalences
are built from actual monomial coefficients.  Their free-orbit decomposition
provides the coinduced target required by the equivariant lifting step.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K]

theorem cyclicHomogeneousOrbitRetraction_invariant (n : ℕ) (g : PrimeCycleGroup p)
    (f : CyclicPolynomialPiece p K n) :
    cyclicHomogeneousOrbitRetraction p K n (cyclicPolynomialRepresentation p K n g f) =
      cyclicHomogeneousOrbitRetraction p K n f := by
  simp only [cyclicHomogeneousOrbitRetraction_apply,
    cyclicHomogeneousAugmentation_invariant]

theorem cyclicOrbitKernel_invariant (n : ℕ) :
    ∀ (g : PrimeCycleGroup p) (f : CyclicPolynomialPiece p K n),
      f ∈ LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) →
        cyclicPolynomialRepresentation p K n g f ∈
          LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) := by
  intro g f hf
  change cyclicHomogeneousOrbitRetraction p K n
    (cyclicPolynomialRepresentation p K n g f) = 0
  rw [cyclicHomogeneousOrbitRetraction_invariant]
  exact hf

def cyclicOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n))
    (cyclicOrbitKernel_invariant p K n)

theorem cyclicOrbitKernelCoordinatesOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    letI := cyclicHomogeneousExponentAction p n
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfNotDvd_apply, cyclicOrbitKernelCoordinatesOfNotDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val =
    f.val.val.coeff (a.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val

theorem cyclicOrbitKernelCoordinatesOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    letI := cyclicNonpivotExponentAction p n hn
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      permutationFunctionRepresentation
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  funext a
  change cyclicOrbitKernelCoordinatesOfDvd p K n hn
      (cyclicOrbitKernelRepresentation p K n g f) a =
    cyclicOrbitKernelCoordinatesOfDvd p K n hn f (g⁻¹ • a)
  rw [cyclicOrbitKernelCoordinatesOfDvd_apply, cyclicOrbitKernelCoordinatesOfDvd_apply]
  change (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val.val).coeff a.val.val =
    f.val.val.coeff (a.val.val.mapDomain (Equiv.addLeft (g⁻¹).toAdd))
  simpa only [primeTranslation_symm] using
    rename_equiv_coefficient p K (Equiv.addLeft g.toAdd) f.val.val a.val.val

abbrev CyclicOrbitIndexOfNotDvd (n : ℕ) : Type :=
  letI := cyclicHomogeneousExponentAction p n
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicHomogeneousExponent p n)

abbrev CyclicOrbitIndexOfDvd (n : ℕ) (hn : p ∣ n) : Type :=
  letI := cyclicNonpivotExponentAction p n hn
  MulAction.orbitRel.Quotient (PrimeCycleGroup p) (CyclicNonpivotExponent p n hn)

theorem cyclicHomogeneous_no_fixed_of_not_dvd (n : ℕ) (hn : ¬p ∣ n) :
    ∀ (g : PrimeCycleGroup p) (a : CyclicHomogeneousExponent p n),
      (cyclicHomogeneousExponentAction p n).smul g a = a → g = 1 := by
  letI := cyclicHomogeneousExponentAction p n
  intro g a hfix
  apply cyclicHomogeneous_action_free_of_not_dvd p n hn a
  exact hfix.trans (one_smul (PrimeCycleGroup p) a).symm

def cyclicOrbitKernelCoinducedOfNotDvd (n : ℕ) (hn : ¬p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfNotDvd p n → K) := by
  letI := cyclicHomogeneousExponentAction p n
  exact (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))

theorem cyclicOrbitKernelCoinducedOfNotDvd_equivariant (n : ℕ) (hn : ¬p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfNotDvd p K n hn).toLinearMap := by
  letI := cyclicHomogeneousExponentAction p n
  intro g f
  change freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfNotDvd p n → K) g
      (freePermutationCoinducedEquiv
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn)
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicHomogeneous_no_fixed_of_not_dvd p n hn))
    (cyclicOrbitKernelCoordinatesOfNotDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicHomogeneous_no_fixed_of_not_dvd p n hn) g
      (cyclicOrbitKernelCoordinatesOfNotDvd p K n hn f))

def cyclicOrbitKernelCoinducedOfDvd (n : ℕ) (hn : p ∣ n) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → CyclicOrbitIndexOfDvd p n hn → K) := by
  letI := cyclicNonpivotExponentAction p n hn
  exact (cyclicOrbitKernelCoordinatesOfDvd p K n hn).trans
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))

theorem cyclicOrbitKernelCoinducedOfDvd_equivariant (n : ℕ) (hn : p ∣ n) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
      coinducedRepresentation (cyclicOrbitKernelCoinducedOfDvd p K n hn).toLinearMap := by
  letI := cyclicNonpivotExponentAction p n hn
  intro g f
  change freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn
        (cyclicOrbitKernelRepresentation p K n g f)) =
    coinducedRepresentation (K := K) (C := CyclicOrbitIndexOfDvd p n hn → K) g
      (freePermutationCoinducedEquiv
      (cyclicNonpivotExponent_no_fixed p n hn)
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))
  exact (congrArg
    (freePermutationCoinducedEquiv (cyclicNonpivotExponent_no_fixed p n hn))
    (cyclicOrbitKernelCoordinatesOfDvd_equivariant p K n hn g f)).trans
    (freePermutationCoinducedEquiv_equivariant
      (cyclicNonpivotExponent_no_fixed p n hn) g
      (cyclicOrbitKernelCoordinatesOfDvd p K n hn f))

/-- Every degree of the actual orbit-retraction kernel is coinduced, with
no hypothesis on the characteristic or invertibility of the group order. -/
theorem cyclicOrbitKernel_isCoinduced (n : ℕ) :
    ∃ (J : Type) (e : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K)),
      RepresentationIntertwines (cyclicOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  by_cases hn : p ∣ n
  · exact ⟨CyclicOrbitIndexOfDvd p n hn, cyclicOrbitKernelCoinducedOfDvd p K n hn,
      cyclicOrbitKernelCoinducedOfDvd_equivariant p K n hn⟩
  · exact ⟨CyclicOrbitIndexOfNotDvd p n, cyclicOrbitKernelCoinducedOfNotDvd p K n hn,
      cyclicOrbitKernelCoinducedOfNotDvd_equivariant p K n hn⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryKernel.lean -/
section


section

/-! # The combined boundary and orbit kernel

The quotient map records the genuine top-face boundary and the orbit
retraction simultaneously.  Its homogeneous kernel is top multiplication
times the corresponding orbit kernel one rank lower in degree.  Degrees
below the top rank are handled explicitly; both kernels are then zero.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

local instance : LinearOrder (ZMod p) := LinearOrder.lift' ZMod.val (ZMod.val_injective p)

def cyclicPolynomialTop : MvPolynomial (ZMod p) K :=
  ∏ v : ZMod p, MvPolynomial.X v

omit [CharP K p] in
theorem cyclicPolynomialTop_eq_esymm :
    cyclicPolynomialTop p K = MvPolynomial.esymm (ZMod p) K p := by
  unfold cyclicPolynomialTop MvPolynomial.esymm
  have hc : (Finset.univ : Finset (ZMod p)).card = p := by simp
  have he : (Finset.univ : Finset (ZMod p)).powersetCard p = {Finset.univ} :=
    (congrArg (fun n => (Finset.univ : Finset (ZMod p)).powersetCard n) hc.symm).trans
      (Finset.powersetCard_self _)
  rw [he]
  simp

omit [CharP K p] in
theorem cyclicPolynomialTop_degree :
    cyclicPolynomialTop p K ∈ CyclicPolynomialPiece p K p := by
  have hd : vertexDegree (fun v : ZMod p => fullExponent (ZMod p) v) = p := by
    simp [vertexDegree, ZMod.card]
  have hh := monomial_mem_polynomialDegreePiece (fullExponent (ZMod p)) (1 : K)
  rw [hd, full_monomial_eq_prod] at hh
  exact hh

omit [CharP K p] in
theorem cyclicPolynomialTop_mul_injective :
    Function.Injective (fun f : MvPolynomial (ZMod p) K => cyclicPolynomialTop p K * f) :=
  (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset (ZMod p))).left

theorem cyclicPolynomialTop_orbitRetraction (f : MvPolynomial (ZMod p) K) :
    primeOrbitRetraction p (cyclicPolynomialTop p K * f) =
      Polynomial.X * primeOrbitRetraction p f := by
  rw [cyclicPolynomialTop_eq_esymm]
  exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f

def cyclicBoundaryOrbitMap :
    MvPolynomial (ZMod p) K →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  polynomialBooleanBoundaryMap.toLinearMap.prod (primeOrbitRetraction p)

def cyclicBoundaryOrbitDegreeMap (n : ℕ) :
    CyclicPolynomialPiece p K n →ₗ[K]
      PolynomialBoundaryRing (ZMod p) K × K[X] :=
  (cyclicBoundaryOrbitMap p K).comp (CyclicPolynomialPiece p K n).subtype

theorem cyclicBoundaryOrbitDegree_mem_kernel (n : ℕ) (f : CyclicPolynomialPiece p K n) :
    f ∈ LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ↔
      polynomialBooleanBoundaryMap f.val = 0 ∧ primeOrbitRetraction p f.val = 0 := by
  change (polynomialBooleanBoundaryMap f.val, primeOrbitRetraction p f.val) = (0, 0) ↔ _
  exact Prod.mk_inj

omit [CharP K p] in
theorem cyclicPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial (ZMod p) K)
    (hf : cyclicPolynomialTop p K * f ∈ CyclicPolynomialPiece p K (m + p)) :
    f ∈ CyclicPolynomialPiece p K m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) =
      p + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hn : vertexDegree (fun v => (fullExponent (ZMod p) + a) v) ≠ m + p := by
    rw [hdeg]
    omega
  have hh := hf (fullExponent (ZMod p) + a) hn
  rw [cyclicPolynomialTop, ← full_monomial_eq_prod,
    MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem cyclicBoundaryOrbitKernel_zero_below (n : ℕ) (hn : n < p)
    (f : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) : f = 0 := by
  obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
  obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
  have hg0 : g = 0 := by
    ext a
    have hdeg : p ≤ vertexDegree (fun v => (fullExponent (ZMod p) + a) v) := by
      change p ≤ vertexDegree ((fun v => fullExponent (ZMod p) v) + (fun v => a v))
      rw [vertexDegree_add]
      simp [vertexDegree]
    have hh := f.val.property (fullExponent (ZMod p) + a) (by omega)
    rw [← hg, ← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
    exact hh
  apply Subtype.ext
  apply Subtype.ext
  change f.val.val = 0
  rw [← hg, hg0, mul_zero]

theorem cyclicOrbitKernel_zero_degree
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K 0)) : f = 0 := by
  have hcoeff : ∀ a : ZMod p →₀ ℕ, f.val.val.coeff a = 0 := by
    intro a
    by_cases ha : a = 0
    · subst a
      have hE := f.property
      change cyclicHomogeneousOrbitRetraction p K 0 f.val = 0 at hE
      rw [cyclicHomogeneousOrbitRetraction_apply, if_pos (dvd_zero p)] at hE
      have haug : cyclicHomogeneousAugmentation p K 0 f.val = 0 :=
        (Polynomial.monomial_eq_zero_iff _ _).mp hE
      rw [cyclicHomogeneousAugmentation_eq_sum] at haug
      change (∑ a : CyclicHomogeneousExponent p 0,
        cyclicPolynomialCoordinates p K 0 f.val a) = 0 at haug
      have hzero : ∀ a : CyclicHomogeneousExponent p 0, a.val = 0 := by
        intro a
        exact (Finsupp.degree_eq_zero_iff a.val).mp a.property
      letI : Unique (CyclicHomogeneousExponent p 0) := {
        default := ⟨0, by simp⟩
        uniq := fun a => Subtype.ext (hzero a) }
      rw [Finset.univ_unique, Finset.sum_singleton, cyclicPolynomialCoordinates_apply] at haug
      simpa only [hzero default] using haug
    · apply f.val.property
      change vertexDegree (fun v => a v) ≠ 0
      rw [vertexDegree, ← Finsupp.degree_eq_sum]
      exact fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
  apply Subtype.ext
  apply Subtype.ext
  exact MvPolynomial.ext _ _ hcoeff

def cyclicBoundaryOrbitTopMap (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) →ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) := by
  by_cases hn : p ≤ n
  · refine {
      toFun := fun f => ⟨⟨cyclicPolynomialTop p K * f.val.val, ?_⟩, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
    · have hh := polynomialDegreePiece_mul p (n - p) (cyclicPolynomialTop p K) f.val.val
        (cyclicPolynomialTop_degree p K) f.val.property
      simpa only [Nat.add_sub_of_le hn] using hh
    · apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        exact ⟨f.val.val, rfl⟩
      · rw [cyclicPolynomialTop_orbitRetraction]
        change Polynomial.X * cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0
        rw [show cyclicHomogeneousOrbitRetraction p K (n - p) f.val = 0 from f.property,
          mul_zero]
    · intro f g
      apply Subtype.ext
      apply Subtype.ext
      exact mul_add _ _ _
    · intro c f
      apply Subtype.ext
      apply Subtype.ext
      exact mul_smul_comm _ _ _
  · exact 0

theorem cyclicBoundaryOrbitTopMap_apply (n : ℕ) (hn : p ≤ n)
    (f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p))) :
    (cyclicBoundaryOrbitTopMap p K n f).val.val = cyclicPolynomialTop p K * f.val.val := by
  simp only [cyclicBoundaryOrbitTopMap, dif_pos hn]
  rfl

theorem cyclicBoundaryOrbitTopMap_bijective (n : ℕ) :
    Function.Bijective (cyclicBoundaryOrbitTopMap p K n) := by
  by_cases hn : p ≤ n
  · constructor
    · intro f g hfg
      apply Subtype.ext
      apply Subtype.ext
      apply cyclicPolynomialTop_mul_injective p K
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn f).symm.trans
        ((congrArg (fun x => x.val.val) hfg).trans
          (cyclicBoundaryOrbitTopMap_apply p K n hn g))
    · intro f
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f.val).mp f.property
      obtain ⟨g, hg⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val.val).mp hb
      have hgdeg : g ∈ CyclicPolynomialPiece p K (n - p) := by
        apply cyclicPolynomialTop_predecessor_degree p K (n - p) g
        rw [Nat.sub_add_cancel hn]
        simpa only [cyclicPolynomialTop, hg] using f.val.property
      have hgE : primeOrbitRetraction p g = 0 := by
        apply (Polynomial.isRegular_X (R := K)).left
        change Polynomial.X * primeOrbitRetraction p g = Polynomial.X * (0 : K[X])
        rw [mul_zero, ← cyclicPolynomialTop_orbitRetraction,
          show cyclicPolynomialTop p K * g = f.val.val from hg]
        exact hE
      let g' : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) :=
        ⟨⟨g, hgdeg⟩, hgE⟩
      refine ⟨g', ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (cyclicBoundaryOrbitTopMap_apply p K n hn g').trans hg
  · have hlt : n < p := Nat.lt_of_not_ge hn
    have hz : n - p = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
    have hsource : ∀ f : LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)), f = 0 := by
      rw [hz]
      exact cyclicOrbitKernel_zero_degree p K
    constructor
    · intro f g _
      exact (hsource f).trans (hsource g).symm
    · intro f
      exact ⟨0, (map_zero _).trans (cyclicBoundaryOrbitKernel_zero_below p K n hlt f).symm⟩

def cyclicBoundaryOrbitKernelEquiv (n : ℕ) :
    LinearMap.ker (cyclicHomogeneousOrbitRetraction p K (n - p)) ≃ₗ[K]
      LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) :=
  LinearEquiv.ofBijective (cyclicBoundaryOrbitTopMap p K n)
    (cyclicBoundaryOrbitTopMap_bijective p K n)

omit [CharP K p] in
theorem cyclicPolynomialTop_rename (e : Equiv.Perm (ZMod p)) :
    MvPolynomial.rename e (cyclicPolynomialTop p K) = cyclicPolynomialTop p K := by
  simp only [cyclicPolynomialTop, map_prod, MvPolynomial.rename_X]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

def cyclicBoundaryOrbitKernelRepresentation (n : ℕ) :
    CyclicRepresentation K (PrimeCycleGroup p)
      (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) :=
  invariantSubmoduleRepresentation (cyclicPolynomialRepresentation p K n)
    (LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n)) (by
      intro g f hf
      obtain ⟨hb, hE⟩ := (cyclicBoundaryOrbitDegree_mem_kernel p K n f).mp hf
      apply (cyclicBoundaryOrbitDegree_mem_kernel p K n _).mpr
      constructor
      · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f.val).mp hb
        change cyclicPolynomialTop p K * x = f.val at hx
        apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
        refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
        change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
          MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val
        rw [← hx, map_mul, cyclicPolynomialTop_rename]
      · change primeOrbitRetraction p
          (MvPolynomial.rename (Equiv.addLeft g.toAdd) f.val) = 0
        rw [primeOrbitRetraction_rename]
        exact hE)

theorem cyclicBoundaryOrbitKernelEquiv_equivariant (n : ℕ) :
    RepresentationIntertwines (cyclicOrbitKernelRepresentation p K (n - p))
      (cyclicBoundaryOrbitKernelRepresentation p K n)
      (cyclicBoundaryOrbitKernelEquiv p K n).toLinearMap := by
  intro g f
  apply Subtype.ext
  apply Subtype.ext
  by_cases hn : p ≤ n
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    rw [cyclicBoundaryOrbitTopMap_apply p K n hn,
      cyclicBoundaryOrbitTopMap_apply p K n hn, map_mul, cyclicPolynomialTop_rename]
    rfl
  · change (cyclicBoundaryOrbitTopMap p K n
        (cyclicOrbitKernelRepresentation p K (n - p) g f)).val.val =
      MvPolynomial.rename (Equiv.addLeft g.toAdd)
        (cyclicBoundaryOrbitTopMap p K n f).val.val
    simp [cyclicBoundaryOrbitTopMap, hn]

/-- Every actual homogeneous combined kernel has regular-orbit coordinates.
This supplies the kernel hypothesis in the graded equivariant lifting theorem. -/
theorem cyclicBoundaryOrbitKernel_isCoinduced (n : ℕ) :
    ∃ J : Type, ∃ e : LinearMap.ker (cyclicBoundaryOrbitDegreeMap p K n) ≃ₗ[K]
      (PrimeCycleGroup p → J → K),
      RepresentationIntertwines (cyclicBoundaryOrbitKernelRepresentation p K n)
        coinducedRepresentation e.toLinearMap := by
  obtain ⟨J, e, he⟩ := cyclicOrbitKernel_isCoinduced p K (n - p)
  let t := cyclicBoundaryOrbitKernelEquiv p K n
  refine ⟨J, t.symm.trans e, ?_⟩
  intro g x
  have ht : t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x) =
      cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x) := by
    apply t.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := cyclicBoundaryOrbitKernelEquiv_equivariant p K n g (t.symm x)
    change t (cyclicOrbitKernelRepresentation p K (n - p) g (t.symm x)) =
      cyclicBoundaryOrbitKernelRepresentation p K n g (t (t.symm x)) at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  change e (t.symm (cyclicBoundaryOrbitKernelRepresentation p K n g x)) = _
  rw [ht]
  exact he g (t.symm x)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicTopCoordinate.lean -/
section


section

/-! # The genuine fixed top-face quotient and its polynomial section

On the barycentric ring the quotient kills every proper face variable and
retains the top face.  On the polynomial side the section substitutes the
product of all vertex variables.  The orbit retraction is a left inverse of
this section, and its parameter action matches the source quotient exactly.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped Polynomial

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

def booleanTopPolynomialEvaluation : MvPolynomial (BooleanFace V) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun F => if F = booleanTopFace then Polynomial.X else 0)

theorem booleanTopPolynomialEvaluation_forbidden
    (a : BooleanFace V →₀ ℕ) (ha : ¬IsChainExponent a) :
    booleanTopPolynomialEvaluation (K := K) (MvPolynomial.monomial a 1) = 0 := by
  have hx : ∃ F ∈ a.support, F ≠ booleanTopFace := by
    by_contra hn
    apply ha
    intro F hF G hG
    have hFt : F = booleanTopFace := by
      by_contra h
      exact hn ⟨F, hF, h⟩
    have hGt : G = booleanTopFace := by
      by_contra h
      exact hn ⟨G, hG, h⟩
    exact Or.inl (by rw [hFt, hGt])
  obtain ⟨F, hF, hFt⟩ := hx
  rw [booleanTopPolynomialEvaluation, MvPolynomial.aeval_monomial, map_one, one_mul]
  apply Finset.prod_eq_zero hF
  change (if F = booleanTopFace then Polynomial.X else (0 : K[X])) ^ a F = 0
  rw [if_neg hFt, zero_pow (Finsupp.mem_support_iff.mp hF)]

def booleanTopEvaluation : BooleanBarycentricRing V K →ₐ[K] K[X] :=
  Ideal.Quotient.liftₐ (forbiddenIdeal IsChainExponent) booleanTopPolynomialEvaluation (by
    have hi : forbiddenIdeal (K := K) (IsChainExponent (V := V)) ≤
        RingHom.ker booleanTopPolynomialEvaluation.toRingHom := by
      rw [forbiddenIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact booleanTopPolynomialEvaluation_forbidden a ha
    exact fun f hf => hi hf)

@[simp] theorem booleanTopEvaluation_face (F : BooleanFace V) :
    booleanTopEvaluation (K := K) (faceVariable F) =
      if F = booleanTopFace then Polynomial.X else 0 := by
  change booleanTopPolynomialEvaluation (MvPolynomial.X F) = _
  exact MvPolynomial.aeval_X _ _

@[simp] theorem booleanTopEvaluation_top :
    booleanTopEvaluation (V := V) (K := K) booleanTop = Polynomial.X := by
  simp [booleanTop]

theorem booleanTopEvaluation_rankParameter (r : ℕ) :
    booleanTopEvaluation (V := V) (K := K) (booleanRankParameter r) =
      if r = Fintype.card V then Polynomial.X else 0 := by
  rw [booleanRankParameter, map_sum]
  rw [Finset.sum_eq_single (booleanTopFace (V := V))]
  · by_cases h : r = Fintype.card V <;> simp [h, eq_comm]
  · intro F hF hFt
    by_cases hcard : F.val.card = r <;> simp [hcard, hFt]
  · intro h
    exact (h (Finset.mem_univ _)).elim

def topParameterMap : MvPolynomial (Fin (Fintype.card V)) K →ₐ[K] K[X] :=
  MvPolynomial.aeval (fun c => if c.val + 1 = Fintype.card V then Polynomial.X else 0)

theorem booleanTopEvaluation_colorMap :
    (booleanTopEvaluation (V := V) (K := K)).comp booleanColorMap = topParameterMap := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [AlgHom.comp_apply, booleanColorMap, topParameterMap, MvPolynomial.aeval_X]
  rw [← booleanRankParameter_color, booleanTopEvaluation_rankParameter]

theorem booleanTopEvaluation_parameter_mul
    (a : MvPolynomial (Fin (Fintype.card V)) K) (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanColorMap a * x) =
      topParameterMap a * booleanTopEvaluation x := by
  rw [map_mul]
  exact congrArg (fun y : K[X] => y * booleanTopEvaluation x)
    (DFunLike.congr_fun booleanTopEvaluation_colorMap a)

theorem orderingDescentFace_ne_top
    (σ : VertexOrdering (Fintype.card V) V) (c : Fin (Fintype.card V))
    (hc : c ∈ orderingDescents σ) : orderingFace σ c ≠ booleanTopFace := by
  intro he
  have hh := congrArg (fun F : BooleanFace V => F.val.card) he
  change (orderingPrefix σ c).card = (Finset.univ : Finset V).card at hh
  rw [card_orderingPrefix, Finset.card_univ] at hh
  obtain ⟨hlt, _⟩ := (mem_orderingDescents σ c).mp hc
  omega

theorem booleanTopEvaluation_descentVector
    (σ : VertexOrdering (Fintype.card V) V) :
    booleanTopEvaluation (K := K) (descentVector σ) =
      if orderingDescents σ = ∅ then 1 else 0 := by
  by_cases hσ : orderingDescents σ = ∅
  · simp [descentVector, hσ]
  · rw [if_neg hσ, descentVector, map_prod]
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hσ
    apply Finset.prod_eq_zero hc
    rw [booleanTopEvaluation_face, if_neg (orderingDescentFace_ne_top σ c hc)]

end Boolean

section Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]

def cyclicTopEmbedding : K[X] →ₐ[K] MvPolynomial (ZMod p) K :=
  Polynomial.aeval (cyclicPolynomialTop p K)

theorem primeOrbitRetraction_top_pow (n : ℕ) :
    primeOrbitRetraction p (cyclicPolynomialTop p K ^ n) = (Polynomial.X : K[X]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', cyclicPolynomialTop_orbitRetraction, ih, pow_succ']

theorem primeOrbitRetraction_topEmbedding (f : K[X]) :
    primeOrbitRetraction p (cyclicTopEmbedding p K f) = f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n c =>
      rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def, map_smul,
        primeOrbitRetraction_top_pow, Algebra.smul_def]
      exact Polynomial.C_mul_X_pow_eq_monomial

theorem cyclicTopEmbedding_boundary (f : K[X]) :
    polynomialBooleanBoundaryMap (cyclicTopEmbedding p K f) =
      algebraMap K (PolynomialBoundaryRing (ZMod p) K) (f.coeff 0) := by
  have ht : polynomialBooleanBoundaryMap (cyclicPolynomialTop p K) = 0 := by
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    exact ⟨1, mul_one _⟩
  have he : (polynomialBooleanBoundaryMap (V := ZMod p) (K := K)).comp
      (cyclicTopEmbedding p K) = Polynomial.aeval 0 := by
    apply Polynomial.algHom_ext
    simpa [cyclicTopEmbedding] using ht
  have hh := DFunLike.congr_fun he f
  exact hh.trans (Polynomial.coeff_zero_eq_aeval_zero' f).symm

theorem primeOrbitRetraction_parameterLinear :
    IsParameterLinear (polynomialColorMap (V := ZMod p) (K := K))
      (topParameterMap (V := ZMod p) (K := K)) (primeOrbitRetraction p) := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro c f
  simp only [polynomialColorMap, topParameterMap, MvPolynomial.aeval_X, ZMod.card]
  by_cases hc : c.val + 1 = p
  · rw [if_pos hc, hc]
    exact primeOrbitRetraction_top_parameter p (Fact.out : p.Prime).pos (ZMod.card p) f
  · rw [if_neg hc, zero_mul]
    apply primeOrbitRetraction_lower_parameter p (Fact.out : p.Prime) (ZMod.card p)
    · omega
    · have hb : c.val < p := c.isLt.trans_eq (ZMod.card p)
      omega

end Polynomial
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBooleanAction.lean -/
section


section

/-! # Actual Boolean vertex-permutation actions

The action is the existing restriction functor along the inverse vertex
permutation.  The generator formula identifies it with literal relabeling of
faces.  Parameter linearity, ordinary grading, and the fixed top quotient are
proved for this action.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

def booleanPermutationAlgEquiv (e : Equiv.Perm V) :
    BooleanBarycentricRing V K ≃ₐ[K] BooleanBarycentricRing V K :=
  { booleanRestriction (K := K) e.symm.toEmbedding with
    invFun := booleanRestriction e.toEmbedding
    left_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.toEmbedding e.symm.toEmbedding) x
      have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.symm_apply_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh
    right_inv := by
      intro x
      have hh := DFunLike.congr_fun
        (booleanRestriction_comp (K := K) e.symm.toEmbedding e.toEmbedding) x
      have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl V := by
        ext v
        exact e.apply_symm_apply v
      rw [he, booleanRestriction_refl] at hh
      exact hh }

@[simp] theorem booleanPermutationAlgEquiv_face (e : Equiv.Perm V) (F : BooleanFace V) :
    booleanPermutationAlgEquiv (K := K) e (faceVariable F) =
      faceVariable (booleanFaceEmbedding e.toEmbedding F) := by
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl V := by
    ext v
    exact e.symm_apply_apply v
  have hh := booleanRestriction_face_included (K := K) e.symm.toEmbedding
    (booleanFaceEmbedding e.toEmbedding F)
  rw [booleanFaceEmbedding_trans, he, booleanFaceEmbedding_refl] at hh
  exact hh

@[simp] theorem booleanPermutationAlgEquiv_one (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (1 : Equiv.Perm V) x = x := by
  change booleanRestriction (Function.Embedding.refl V) x = x
  rw [booleanRestriction_refl]
  rfl

theorem booleanPermutationAlgEquiv_mul (e f : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanPermutationAlgEquiv (e * f) x =
      booleanPermutationAlgEquiv e (booleanPermutationAlgEquiv f x) := by
  have he : (e * f).symm.toEmbedding = e.symm.toEmbedding.trans f.symm.toEmbedding := by
    ext v
    rfl
  change booleanRestriction (e * f).symm.toEmbedding x =
    booleanRestriction e.symm.toEmbedding (booleanRestriction f.symm.toEmbedding x)
  rw [he]
  exact (DFunLike.congr_fun (booleanRestriction_comp (K := K)
    e.symm.toEmbedding f.symm.toEmbedding) x).symm

theorem booleanPermutationAlgEquiv_parameter (e : Equiv.Perm V) (r : ℕ) :
    booleanPermutationAlgEquiv (K := K) e (booleanRankParameter r) = booleanRankParameter r :=
  booleanRestriction_rankParameter e.symm.toEmbedding r

theorem booleanPermutationAlgEquiv_colorMap (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    booleanPermutationAlgEquiv e (booleanColorMap a) = booleanColorMap a := by
  have he : (booleanPermutationAlgEquiv (K := K) e).toAlgHom.comp booleanColorMap =
      booleanColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, booleanColorMap, MvPolynomial.aeval_X]
    rw [← booleanRankParameter_color]
    exact booleanPermutationAlgEquiv_parameter e (c.val + 1)
  exact DFunLike.congr_fun he a

/-- The genuine permutation action is linear over the prescribed rank-sum
parameter algebra, not merely over the coefficient field. -/
def booleanParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (BooleanBarycentricRing V K) where
  toFun e := {
    toFun := booleanPermutationAlgEquiv e
    map_add' := (booleanPermutationAlgEquiv e).map_add
    map_smul' := by
      intro a x
      change booleanPermutationAlgEquiv e (booleanColorMap a * x) =
        booleanColorMap a * booleanPermutationAlgEquiv e x
      rw [map_mul, booleanPermutationAlgEquiv_colorMap] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_one x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    exact booleanPermutationAlgEquiv_mul e f x

theorem chainOrdinaryDegree_map_faceEmbedding (e : V ↪ V)
    (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a.mapDomain (booleanFaceEmbedding e)) = chainOrdinaryDegree a := by
  unfold chainOrdinaryDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ i j => by simp only [add_mul])]
  simp only [booleanFaceEmbedding_card]

theorem booleanPermutationAlgEquiv_degree (e : Equiv.Perm V) (n : ℕ)
    (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) :
    booleanPermutationAlgEquiv e x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by
  intro a ha
  change booleanChainBasis.repr (booleanRestriction e.symm.toEmbedding x) a = 0
  rw [booleanRestriction_coefficient]
  apply hx
  change chainOrdinaryDegree (a.val.mapDomain (booleanFaceEmbedding e.symm.toEmbedding)) ≠ n
  rw [chainOrdinaryDegree_map_faceEmbedding]
  exact ha

theorem booleanAlgHom_ext {S : Type*} [CommRing S] [Algebra K S]
    (f g : BooleanBarycentricRing V K →ₐ[K] S)
    (h : ∀ F, f (faceVariable F) = g (faceVariable F)) : f = g := by
  have he : f.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) =
      g.comp (Ideal.Quotient.mkₐ K (forbiddenIdeal IsChainExponent)) := by
    apply MvPolynomial.algHom_ext
    exact h
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he a

variable [Nonempty V]

theorem booleanFaceEmbedding_equiv_top (e : Equiv.Perm V) :
    booleanFaceEmbedding e.toEmbedding (booleanTopFace (V := V)) = booleanTopFace := by
  apply Subtype.ext
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  exact Finset.mem_map.mpr ⟨e.symm v, Finset.mem_univ _, e.apply_symm_apply v⟩

theorem booleanTopEvaluation_permutation (e : Equiv.Perm V)
    (x : BooleanBarycentricRing V K) :
    booleanTopEvaluation (booleanPermutationAlgEquiv e x) = booleanTopEvaluation x := by
  have he : (booleanTopEvaluation (V := V) (K := K)).comp
      (booleanPermutationAlgEquiv e).toAlgHom = booleanTopEvaluation := by
    apply booleanAlgHom_ext
    intro F
    change booleanTopEvaluation (booleanPermutationAlgEquiv e (faceVariable F)) =
      booleanTopEvaluation (faceVariable F)
    rw [booleanPermutationAlgEquiv_face, booleanTopEvaluation_face, booleanTopEvaluation_face]
    have ht : booleanFaceEmbedding e.toEmbedding F = booleanTopFace ↔ F = booleanTopFace := by
      constructor
      · intro h
        exact (booleanFaceEmbedding e.toEmbedding).injective
          (h.trans (booleanFaceEmbedding_equiv_top e).symm)
      · rintro rfl
        exact booleanFaceEmbedding_equiv_top e
    simp only [ht]
  exact DFunLike.congr_fun he x

end General

section Graded

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem booleanParameterPermutationRepresentation_graded (e : Equiv.Perm V)
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n) :
    booleanParameterPermutationRepresentation e x ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n := by
  rw [booleanScalarGradedBasis_piece_eq] at hx ⊢
  exact booleanPermutationAlgEquiv_degree e n x hx

end Graded
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicOrdinaryLift.lean -/
section


section

/-! # A normalized ordinary lift to both prescribed quotients

Starting with any graded, normalized parameter-linear boundary lift, correct
the images of the actual descent basis by the top-coordinate section.  The
correction has zero boundary and gives exact compatibility with the fixed
top-face quotient.  No equivariance is assumed at this stage.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial
open scoped Polynomial

section DegreeFacts

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem descentOrdinaryDegree_eq_zero_iff
    (σ : VertexOrdering (Fintype.card V) V) :
    colorOrdinaryDegree (descentColorExponent σ) = 0 ↔ orderingDescents σ = ∅ := by
  rw [colorOrdinaryDegree_eq_zero_iff]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hh := congrArg (fun a : ColorExponent V => a c) h
    simp only [descentColorExponent_apply, if_pos hc, Finsupp.zero_apply] at hh
    exact Nat.one_ne_zero hh
  · intro h
    simp [descentColorExponent, h]

theorem weightOrdering_zero_no_descents :
    orderingDescents (weightOrdering (fun _ : V => 0)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨_, hh⟩ := weightOrdering_descent_lt (fun _ : V => 0)
    ((mem_orderingDescents _ _).mp hc)
  exact (Nat.lt_irrefl 0) hh

theorem parameterLinear_ordinary_degree
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hd : ∀ σ : VertexOrdering (Fintype.card V) V,
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : f x ∈ polynomialDegreePiece n := by
  rw [← booleanChainBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_smul]
  apply Submodule.smul_mem
  have hdeg : chainOrdinaryDegree a.val = n := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (hx a hn)
  rw [← hdeg]
  exact parameterLinear_chain_degree f hf hd a

end DegreeFacts

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

theorem cyclicTopEmbedding_monomial_degree (m : ℕ) (c : K) :
    cyclicTopEmbedding p K (Polynomial.monomial m c) ∈
      CyclicPolynomialPiece p K (m * p) := by
  rw [cyclicTopEmbedding, Polynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  exact polynomialDegreePiece_pow p (cyclicPolynomialTop p K)
    (cyclicPolynomialTop_degree p K) m

theorem cyclicTopEmbedding_orbitRetraction_degree (n : ℕ)
    (f : CyclicPolynomialPiece p K n) :
    cyclicTopEmbedding p K (primeOrbitRetraction p f.val) ∈ CyclicPolynomialPiece p K n := by
  change cyclicTopEmbedding p K (cyclicHomogeneousOrbitRetraction p K n f) ∈ _
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hn : p ∣ n
  · rw [if_pos hn]
    have hh := cyclicTopEmbedding_monomial_degree p K (n / p)
      (cyclicHomogeneousAugmentation p K n f)
    simpa only [Nat.div_mul_cancel hn] using hh
  · rw [if_neg hn, map_zero]
    exact Submodule.zero_mem _

theorem cyclicHomogeneousOrbitRetraction_constant_zero (n : ℕ) (hn : 0 < n)
    (f : CyclicPolynomialPiece p K n) :
    (primeOrbitRetraction p f.val).coeff 0 = 0 := by
  change (cyclicHomogeneousOrbitRetraction p K n f).coeff 0 = 0
  rw [cyclicHomogeneousOrbitRetraction_apply]
  by_cases hd : p ∣ n
  · rw [if_pos hd, Polynomial.coeff_monomial]
    have hq : n / p ≠ 0 := by
      intro hzero
      have hh := Nat.div_mul_cancel hd
      rw [hzero, zero_mul] at hh
      omega
    rw [if_neg hq]
  · rw [if_neg hd]
    rfl

def cyclicOrdinaryCorrectedLift
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  exact ((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).restrictScalars K

@[simp] theorem cyclicOrdinaryCorrectedLift_descent
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) =
      f (descentVector σ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  simpa only [cyclicOrdinaryCorrectedLift, LinearMap.restrictScalars_apply,
    booleanColorBasis_apply] using
    (booleanColorBasis (V := ZMod p) (K := K)).constr_basis
      (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (fun τ => f (descentVector τ) + cyclicTopEmbedding p K
        (booleanTopEvaluation (descentVector τ) - primeOrbitRetraction p (f (descentVector τ)))) σ

theorem cyclicOrdinaryCorrectedLift_parameterLinear
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K) :
    IsParameterLinear booleanColorMap polynomialColorMap (cyclicOrdinaryCorrectedLift p K f) := by
  letI := (polynomialColorMap (V := ZMod p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (MvPolynomial (ZMod p) K) := IsScalarTower.of_algHom polynomialColorMap
  intro a x
  exact (((booleanColorBasis (V := ZMod p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
    (fun σ => f (descentVector σ) + cyclicTopEmbedding p K
      (booleanTopEvaluation (descentVector σ) - primeOrbitRetraction p (f (descentVector σ))))).map_smul a x)

theorem cyclicOrdinaryCorrectedLift_orbitRetraction
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (x : BooleanBarycentricRing (ZMod p) K) :
    primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f x) = booleanTopEvaluation x := by
  have he : (primeOrbitRetraction p).comp (cyclicOrdinaryCorrectedLift p K f) =
      (booleanTopEvaluation (V := ZMod p) (K := K)).toLinearMap := by
    apply parameterLinear_ext_descent (topParameterMap (V := ZMod p) (K := K))
    · intro a y
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear,
        primeOrbitRetraction_parameterLinear]
      rfl
    · exact booleanTopEvaluation_parameter_mul
    · intro σ
      change primeOrbitRetraction p (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, primeOrbitRetraction_topEmbedding]
      rw [← add_sub_assoc,
        add_comm (primeOrbitRetraction p (f (descentVector σ)))
          (booleanTopEvaluation (descentVector σ)), add_sub_cancel_right]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_one
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (h1 : f 1 = 1) : cyclicOrdinaryCorrectedLift p K f 1 = 1 := by
  let σ := weightOrdering (fun _ : ZMod p => 0)
  have hd : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  rw [← hd, cyclicOrdinaryCorrectedLift_descent, hd, h1,
    map_one, primeOrbitRetraction_one, sub_self, map_zero, add_zero]

theorem cyclicOrdinaryCorrectedLift_boundary
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (h1 : f 1 = 1)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (x : BooleanBarycentricRing (ZMod p) K) :
    polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f x) =
      polynomialBooleanBoundaryMap (f x) := by
  have he : polynomialBooleanBoundaryMap.toLinearMap.comp (cyclicOrdinaryCorrectedLift p K f) =
      polynomialBooleanBoundaryMap.toLinearMap.comp f := by
    apply parameterLinear_ext_descent (polynomialBoundaryColorMap (V := ZMod p) (K := K))
    · intro a y
      change polynomialBooleanBoundaryMap
        (cyclicOrdinaryCorrectedLift p K f (booleanColorMap a * y)) = _
      rw [cyclicOrdinaryCorrectedLift_parameterLinear, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro a y
      change polynomialBooleanBoundaryMap (f (booleanColorMap a * y)) = _
      rw [hf, polynomialBooleanBoundaryMap_parameter_mul]
      rfl
    · intro σ
      change polynomialBooleanBoundaryMap (cyclicOrdinaryCorrectedLift p K f (descentVector σ)) = _
      rw [cyclicOrdinaryCorrectedLift_descent, map_add, cyclicTopEmbedding_boundary]
      have hc : (booleanTopEvaluation (descentVector σ) -
          primeOrbitRetraction p (f (descentVector σ))).coeff 0 = 0 := by
        by_cases hσ : orderingDescents σ = ∅
        · have hh : descentVector (K := K) σ = 1 := by simp [descentVector, hσ]
          rw [hh, h1, map_one, primeOrbitRetraction_one, sub_self]
          rfl
        · rw [Polynomial.coeff_sub, booleanTopEvaluation_descentVector, if_neg hσ]
          have hn : 0 < colorOrdinaryDegree (descentColorExponent σ) :=
            Nat.pos_of_ne_zero (fun h => hσ ((descentOrdinaryDegree_eq_zero_iff σ).mp h))
          rw [cyclicHomogeneousOrbitRetraction_constant_zero p K _ hn
            ⟨f (descentVector σ), hd σ⟩]
          simp
      rw [hc, map_zero, add_zero]
      rfl
  exact DFunLike.congr_fun he x

theorem cyclicOrdinaryCorrectedLift_descent_degree
    (f : BooleanBarycentricRing (ZMod p) K →ₗ[K] MvPolynomial (ZMod p) K)
    (hd : ∀ σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p),
      f (descentVector σ) ∈ polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)))
    (σ : VertexOrdering (Fintype.card (ZMod p)) (ZMod p)) :
    cyclicOrdinaryCorrectedLift p K f (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  rw [cyclicOrdinaryCorrectedLift_descent, map_sub]
  apply Submodule.add_mem _ (hd σ)
  apply Submodule.sub_mem
  · rw [booleanTopEvaluation_descentVector]
    by_cases hσ : orderingDescents σ = ∅
    · rw [if_pos hσ, map_one, (descentOrdinaryDegree_eq_zero_iff σ).mpr hσ]
      exact polynomialDegreePiece_one
    · rw [if_neg hσ, map_zero]
      exact Submodule.zero_mem _
  · exact cyclicTopEmbedding_orbitRetraction_degree p K _ ⟨f (descentVector σ), hd σ⟩

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicParameterModules.lean -/
section


section

/-! # Parameter modules and the actual controlled quotient

The scoped polynomial module structure is evaluation at elementary symmetric
polynomials.  The controlled submodule is the intersection of the genuine
boundary kernel and the orbit-retraction kernel.  The quotient and all group
actions are induced from these actual maps.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal

-- The chain predicate does not depend on the equality decision procedure.

open Classical Finset MvPolynomial

namespace CyclicParameterAction

scoped instance (priority := 2000) polynomialAlgebra {V K : Type*} [Fintype V] [CommRing K] :
    Algebra (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  (polynomialColorMap (V := V) (K := K)).toRingHom.toAlgebra

scoped instance (priority := 2000) polynomialSMul {V K : Type*} [Fintype V] [CommRing K] :
    SMul (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toSMul _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance (priority := 2000) polynomialModule {V K : Type*} [Fintype V] [CommRing K] :
    Module (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  @Algebra.toModule _ _ _ _ (polynomialAlgebra (V := V) (K := K))

scoped instance polynomialTower {V K : Type*} [Fintype V] [CommRing K] :
    IsScalarTower K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K) :=
  IsScalarTower.of_algHom (polynomialColorMap (V := V) (K := K))

end CyclicParameterAction

open scoped CyclicParameterAction

section General

variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

theorem polynomialColorMap_rename (e : Equiv.Perm V)
    (a : MvPolynomial (Fin (Fintype.card V)) K) :
    MvPolynomial.rename e (polynomialColorMap a) = polynomialColorMap a := by
  have he : (MvPolynomial.rename e).comp (polynomialColorMap (V := V) (K := K)) =
      polynomialColorMap := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, polynomialColorMap, MvPolynomial.aeval_X,
      MvPolynomial.rename_esymm]
  exact DFunLike.congr_fun he a

def polynomialParameterPermutationRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card V)) K)
      (Equiv.Perm V) (MvPolynomial V K) where
  toFun e := {
    toFun := MvPolynomial.rename e
    map_add' := (MvPolynomial.rename e).map_add
    map_smul' := by
      intro a x
      change MvPolynomial.rename e (polynomialColorMap a * x) =
        polynomialColorMap a * MvPolynomial.rename e x
      rw [map_mul, polynomialColorMap_rename] }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact MvPolynomial.rename_id_apply x
  map_mul' e f := by
    apply LinearMap.ext
    intro x
    change MvPolynomial.rename (e * f) x = MvPolynomial.rename e (MvPolynomial.rename f x)
    rw [MvPolynomial.rename_rename]
    rfl

def parameterLinearMap
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f) :
    BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K where
  toFun := f
  map_add' := f.map_add
  map_smul' := hf

end General

section QuotientAction

variable {A G N : Type*} [CommRing A] [Group G] [AddCommGroup N] [Module A N]

def invariantQuotientRepresentation (ρ : CyclicRepresentation A G N)
    (H : Submodule A N) (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    CyclicRepresentation A G (N ⧸ H) where
  toFun g := H.mapQ H (ρ g) (fun x hx => hH g x hx)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ 1 y) = H.mkQ y
    rw [ρ.map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := H.mkQ_surjective x
    change H.mkQ (ρ (g * h) y) = H.mkQ (ρ g (ρ h y))
    rw [ρ.map_mul]
    rfl

@[simp] theorem invariantQuotientRepresentation_mk
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) (g : G) (x : N) :
    invariantQuotientRepresentation ρ H hH g (H.mkQ x) = H.mkQ (ρ g x) := rfl

theorem invariantQuotientRepresentation_mk_intertwines
    (ρ : CyclicRepresentation A G N) (H : Submodule A N)
    (hH : ∀ g x, x ∈ H → ρ g x ∈ H) :
    RepresentationIntertwines ρ (invariantQuotientRepresentation ρ H hH) H.mkQ := by
  intro g x
  rfl

end QuotientAction

section Cyclic

variable (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
variable [LinearOrder (ZMod p)]

-- Use the same equality decision as the descent-basis linear order.
local instance (priority := 3000) : DecidableEq (ZMod p) :=
  fun a b => LinearOrder.toDecidableEq a b

def cyclicVertexPermutation : PrimeCycleGroup p →* Equiv.Perm (ZMod p) where
  toFun g := Equiv.addLeft g.toAdd
  map_one' := by ext v; exact zero_add v
  map_mul' g h := by ext v; exact add_assoc g.toAdd h.toAdd v

def cyclicPolynomialParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (MvPolynomial (ZMod p) K) :=
  polynomialParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

def cyclicBooleanParameterRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (BooleanBarycentricRing (ZMod p) K) :=
  booleanParameterPermutationRepresentation.comp (cyclicVertexPermutation p)

@[simp] theorem cyclicPolynomialParameterRepresentation_apply
    (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K) :
    cyclicPolynomialParameterRepresentation p K g f =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f := rfl

@[simp] theorem cyclicBooleanParameterRepresentation_apply
    (g : PrimeCycleGroup p) (x : BooleanBarycentricRing (ZMod p) K) :
    cyclicBooleanParameterRepresentation p K g x =
      booleanPermutationAlgEquiv (Equiv.addLeft g.toAdd) x := rfl

def cyclicControlledKernel :
    Submodule (MvPolynomial (Fin (Fintype.card (ZMod p))) K) (MvPolynomial (ZMod p) K) where
  carrier := {f | polynomialBooleanBoundaryMap f = 0 ∧ primeOrbitRetraction p f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · rw [map_add, hf.1, hg.1, add_zero]
    · rw [map_add, hf.2, hg.2, add_zero]
  smul_mem' := by
    intro a f hf
    change polynomialBooleanBoundaryMap (polynomialColorMap a * f) = 0 ∧
      primeOrbitRetraction p (polynomialColorMap a * f) = 0
    constructor
    · rw [polynomialBooleanBoundaryMap_parameter_mul, hf.1, mul_zero]
    · rw [primeOrbitRetraction_parameterLinear, hf.2, mul_zero]

theorem cyclicControlledKernel_invariant :
    ∀ (g : PrimeCycleGroup p) (f : MvPolynomial (ZMod p) K),
      f ∈ cyclicControlledKernel p K →
        cyclicPolynomialParameterRepresentation p K g f ∈ cyclicControlledKernel p K := by
  intro g f hf
  constructor
  · obtain ⟨x, hx⟩ := (polynomialBooleanBoundaryMap_eq_zero_iff f).mp hf.1
    change cyclicPolynomialTop p K * x = f at hx
    apply (polynomialBooleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨MvPolynomial.rename (Equiv.addLeft g.toAdd) x, ?_⟩
    change cyclicPolynomialTop p K * MvPolynomial.rename (Equiv.addLeft g.toAdd) x =
      MvPolynomial.rename (Equiv.addLeft g.toAdd) f
    rw [← hx, map_mul, cyclicPolynomialTop_rename]
  · rw [cyclicPolynomialParameterRepresentation_apply, primeOrbitRetraction_rename]
    exact hf.2

abbrev CyclicControlledQuotient :=
  MvPolynomial (ZMod p) K ⧸ cyclicControlledKernel p K

def cyclicControlledQuotientRepresentation :
    CyclicRepresentation (MvPolynomial (Fin (Fintype.card (ZMod p))) K)
      (PrimeCycleGroup p) (CyclicControlledQuotient p K) :=
  invariantQuotientRepresentation (cyclicPolynomialParameterRepresentation p K)
    (cyclicControlledKernel p K) (cyclicControlledKernel_invariant p K)

end Cyclic
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerParameterQuotient.lean -/
section


section

/-! # The parameter-linear simultaneous quotient

The quotient is by the intersection of the actual proper-boundary and
fixed-face kernels. Its parameter-module structure is the prescribed rank
parameter action, and its group action is induced by literal vertex
permutations. Its homogeneous kernel is identified with the corresponding
actual coefficient submodule, with no projectivity hypothesis.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Nonempty W] [Group G]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) primePowerVertexOrder : LinearOrder (ZMod p × W) :=
  linearOrderWithDecidableEq
    (LinearOrder.lift' (Fintype.equivFin (ZMod p × W)) (Fintype.equivFin (ZMod p × W)).injective)
    (Classical.decEq _)

abbrev PrimePowerParameterRing := MvPolynomial (Fin (Fintype.card (ZMod p × W))) K
abbrev PrimeBooleanDegreePiece (n : ℕ) :=
  basisOrdinaryDegreePiece (booleanChainBasis (V := ZMod p × W) (K := K))
    (fun a => booleanOrdinaryDegree a.val) n

/-- Closure is proved directly from the two actual algebra maps. -/
def primeControlledParameterKernel :
    Submodule (PrimePowerParameterRing (W := W) p K) (BooleanBarycentricRing (ZMod p × W) K) where
  carrier := {x | booleanBoundaryMap x = 0 ∧ primeFixedFaceQuotient p K x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · rw [map_add, hx.1, hy.1, add_zero]
    · rw [map_add, hx.2, hy.2, add_zero]
  smul_mem' := by
    intro a x hx
    change booleanBoundaryMap (booleanColorMap a * x) = 0 ∧
      primeFixedFaceQuotient p K (booleanColorMap a * x) = 0
    constructor
    · rw [map_mul, hx.1, mul_zero]
    · rw [map_mul, hx.2, mul_zero]

@[simp] theorem primeControlledParameterKernel_restrictScalars :
    (primeControlledParameterKernel (W := W) p K).restrictScalars K = PrimeControlledKernel (W := W) p K := by
  ext x
  rfl

abbrev PrimeControlledParameterQuotient :=
  BooleanBarycentricRing (ZMod p × W) K ⧸ primeControlledParameterKernel (W := W) p K

variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))

def primeBooleanParameterRepresentation :
    CyclicRepresentation (PrimePowerParameterRing (W := W) p K) G
      (BooleanBarycentricRing (ZMod p × W) K) :=
  booleanParameterPermutationRepresentation.comp ρ

@[simp] theorem primeBooleanParameterRepresentation_apply (g : G)
    (x : BooleanBarycentricRing (ZMod p × W) K) :
    primeBooleanParameterRepresentation p K ρ g x = booleanVertexRelabelEquiv (ρ g) x := rfl

/-- The full top variable is fixed by every vertex permutation. -/
theorem booleanVertexRelabel_top (e : Equiv.Perm (ZMod p × W)) :
    booleanVertexRelabelEquiv (K := K) e booleanTop = booleanTop := by
  change booleanPermutationAlgEquiv e (faceVariable booleanTopFace) = faceVariable booleanTopFace
  rw [booleanPermutationAlgEquiv_face, booleanFaceEmbedding_equiv_top]

include hρ in
theorem primeControlledParameterKernel_invariant :
    ∀ (g : G) (x : BooleanBarycentricRing (ZMod p × W) K),
      x ∈ primeControlledParameterKernel (W := W) p K →
        primeBooleanParameterRepresentation p K ρ g x ∈ primeControlledParameterKernel (W := W) p K := by
  intro g x hx
  constructor
  · obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hx.1
    apply (booleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨booleanVertexRelabelEquiv (ρ g) y, ?_⟩
    rw [primeBooleanParameterRepresentation_apply, ← hy, map_mul, booleanVertexRelabel_top]
  · rw [primeBooleanParameterRepresentation_apply, primeOrbitParentAction_normalForm p ρ hρ g,
      primeFixedFaceQuotient_relabel]
    rw [show primeFixedFaceQuotient p K x = 0 from hx.2, map_zero]

def primeControlledParameterRepresentation :
    CyclicRepresentation (PrimePowerParameterRing (W := W) p K) G
      (PrimeControlledParameterQuotient (W := W) p K) :=
  invariantQuotientRepresentation (primeBooleanParameterRepresentation p K ρ)
    (primeControlledParameterKernel (W := W) p K) (primeControlledParameterKernel_invariant p K ρ hρ)

theorem primeControlledParameterQuotient_intertwines :
    RepresentationIntertwines (primeBooleanParameterRepresentation p K ρ)
      (primeControlledParameterRepresentation p K ρ hρ) (primeControlledParameterKernel (W := W) p K).mkQ := by
  intro g x
  rfl

def primeControlledParameterDegreeMap (n : ℕ) :
    PrimeBooleanDegreePiece (W := W) p K n →ₗ[K] PrimeControlledParameterQuotient (W := W) p K :=
  ((primeControlledParameterKernel (W := W) p K).mkQ.restrictScalars K).comp
    (PrimeBooleanDegreePiece (W := W) p K n).subtype

/-- The formal quotient has exactly the simultaneous boundary kernel. -/
theorem primeControlledParameterDegreeKernel_eq (n : ℕ) :
    LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n) =
      (PrimeControlledKernel (W := W) p K).comap (PrimeBooleanDegreePiece (W := W) p K n).subtype := by
  ext x
  change (primeControlledParameterKernel (W := W) p K).mkQ x.val = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem primeBooleanParameterRepresentation_degree :
    ∀ (g : G) (n : ℕ) (x : BooleanBarycentricRing (ZMod p × W) K),
      x ∈ PrimeBooleanDegreePiece (W := W) p K n →
        primeBooleanParameterRepresentation p K ρ g x ∈ PrimeBooleanDegreePiece (W := W) p K n := by
  intro g n x hx
  exact booleanPermutationAlgEquiv_degree (ρ g) n x hx

/-- The quotient map detects the literal two prescribed equations. -/
theorem primeControlledParameterQuotient_eq_iff
    (x y : BooleanBarycentricRing (ZMod p × W) K) :
    (primeControlledParameterKernel (W := W) p K).mkQ x = (primeControlledParameterKernel (W := W) p K).mkQ y ↔
      booleanBoundaryMap x = booleanBoundaryMap y ∧
        primeFixedFaceQuotient p K x = primeFixedFaceQuotient p K y := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (booleanBoundaryMap (x-y) = 0 ∧ primeFixedFaceQuotient p K (x-y) = 0) ↔ _
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_zero]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicFixedFaceBoundary.lean -/
section

section
/-! # The boundary of the actual fixed-face discrepancy

Restrictions to all proper finite subsets detect the genuine top-coordinate
quotient.  Applying the two literal restriction squares therefore puts the
discrepancy between an ordinary boundary lift and the prescribed fixed-face
map in the actual boundary kernel.  Its degree and divisibility properties
follow from the integral moment map and the fixed-face quotient.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section BoundaryDetection
variable {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) (S : Finset W) : DecidableEq S := Classical.decEq _

/-- The inclusion of an actual finite vertex subset, including the empty set. -/
def fixedOrbitSubsetEmbedding (S : Finset W) : S ↪ W :=
  Function.Embedding.subtype (fun w => w ∈ S)

/-- A chain with zero top exponent is contained in a proper vertex subset. -/
theorem booleanBoundaryExponent_supported_proper
    (a : {a : BooleanFace W →₀ ℕ // BooleanBoundaryAllowed a}) :
    ∃ S : Finset W, S ≠ Finset.univ ∧ ∀ F ∈ a.val.support, F.val ⊆ S := by
  rcases Finset.eq_empty_or_nonempty a.val.support with he | hne
  · refine ⟨∅, ?_, ?_⟩
    · intro h
      exact Finset.univ_nonempty.ne_empty h.symm
    · intro F hF
      rw [he] at hF
      exact False.elim (Finset.notMem_empty F hF)
  · obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image a.val.support
      (fun G : BooleanFace W => G.val.card) hne
    refine ⟨F.val, ?_, ?_⟩
    · intro h
      have ht : F = booleanTopFace := Subtype.ext h
      subst F
      exact Finsupp.mem_support_iff.mp hF a.property.2
    · intro G hG
      rcases a.property.1 G hG F hF with hGF | hFG
      · exact hGF
      · have he : F.val = G.val := Finset.eq_of_subset_of_card_le hFG (hmax G hG)
        rw [← he]

/-- Vanishing on every proper vertex subset is vanishing in the actual
quotient by the top face variable, over any coefficient ring. -/
theorem booleanBoundaryMap_eq_zero_of_subsetRestrictions
    (x : BooleanBarycentricRing W K)
    (hx : ∀ (S : Finset W), S ≠ Finset.univ →
      booleanRestriction (fixedOrbitSubsetEmbedding S) x = 0) :
    booleanBoundaryMap x = 0 := by
  apply (standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
    (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
      booleanTopFace)).repr.injective
  ext a
  rw [map_zero, Finsupp.zero_apply]
  change ((standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
    (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
      booleanTopFace)).repr (coordinateBoundaryMap IsChainExponent booleanTopFace x)) a = 0
  rw [coordinateBoundaryMap_coefficient]
  obtain ⟨S, hS, hinside⟩ := booleanBoundaryExponent_supported_proper a
  let i : S ↪ W := fixedOrbitSubsetEmbedding S
  have hrange : ∀ F ∈ a.val.support, F ∈ Set.range (booleanFaceEmbedding i) := by
    intro F hF
    let t : Finset S := F.val.attach.map
      ⟨fun w => ⟨w.val, hinside F hF w.property⟩,
        fun v w h => by
          apply Subtype.ext
          have hh := congrArg (fun z : S => z.val) h
          exact hh⟩
    have ht : t.Nonempty := F.property.attach.map
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, hvw⟩ := Finset.mem_map.mp hw
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
      have he : u.val = w := (congrArg Subtype.val huv).trans hvw
      exact he ▸ u.property
    · intro hw
      refine Finset.mem_map.mpr ⟨⟨w, hinside F hF hw⟩, ?_, rfl⟩
      exact Finset.mem_map.mpr ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩
  let b : BooleanChainExponent S :=
    ⟨a.val.comapDomain (booleanFaceEmbedding i) (booleanFaceEmbedding i).injective.injOn, by
      intro F hF G hG
      have hF' : booleanFaceEmbedding i F ∈ a.val.support := by
        simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hF
      have hG' : booleanFaceEmbedding i G ∈ a.val.support := by
        simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hG
      exact (a.property.1 _ hF' _ hG').imp
        Finset.map_subset_map.mp Finset.map_subset_map.mp⟩
  have hc := congrArg (fun z : BooleanBarycentricRing S K =>
    (booleanChainBasis (K := K)).repr z b) (hx S hS)
  rw [booleanRestriction_coefficient, map_zero, Finsupp.zero_apply] at hc
  have he : (⟨b.val.mapDomain (booleanFaceEmbedding i),
      isChainExponent_map_booleanFaceEmbedding i b.property⟩ : BooleanChainExponent W) =
      ⟨a.val, a.property.1⟩ := by
    apply Subtype.ext
    exact Finsupp.mapDomain_comapDomain _ (booleanFaceEmbedding i).injective a.val hrange
  rw [he] at hc
  exact hc

end BoundaryDetection

section MomentDegree
variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]

/-- The already verified support-degree formula in the actual homogeneous
polynomial submodule used by the ordinary parameter-basis construction. -/
theorem primeOrbitMomentRetraction_mem_polynomialDegreePiece (n : ℕ)
    (f : MvPolynomial (ZMod p × W) K) (hf : f ∈ polynomialDegreePiece n) :
    primeOrbitMomentRetraction p K f ∈ polynomialDegreePiece (n / p) := by
  have hdeg : ∀ a ∈ f.support, a.degree = n := by
    intro a ha
    by_contra hn
    have hd : vertexDegree (fun v => a v) ≠ n := by
      simpa only [vertexDegree, ← Finsupp.degree_eq_sum] using hn
    exact MvPolynomial.mem_support_iff.mp ha (hf a hd)
  intro a ha
  by_contra hc
  have he := primeOrbitMomentRetraction_degree p K f n hdeg a
    (MvPolynomial.mem_support_iff.mpr hc)
  exact ha (by simpa only [vertexDegree, ← Finsupp.degree_eq_sum] using he)

theorem primeOrbitMomentRetraction_zero_of_polynomialDegree_not_dvd (n : ℕ)
    (f : MvPolynomial (ZMod p × W) K) (hf : f ∈ polynomialDegreePiece n)
    (hn : ¬ p ∣ n) : primeOrbitMomentRetraction p K f = 0 := by
  apply primeOrbitMomentRetraction_zero_of_degree_not_dvd p K f n _ hn
  intro a ha
  by_contra hn'
  have hd : vertexDegree (fun v => a v) ≠ n := by
    simpa only [vertexDegree, ← Finsupp.degree_eq_sum] using hn'
  exact MvPolynomial.mem_support_iff.mp ha (hf a hd)

end MomentDegree

section Discrepancy
variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) (S : Finset W) : DecidableEq S := Classical.decEq _
local instance (priority := 2000) (S : Finset W) : DecidableEq (ZMod p × S) := Classical.decEq _

/-- A prescribed quotient family and a coherent ordinary boundary lift have
an actual discrepancy with zero quotient boundary.  The hypotheses are the
three literal restriction squares on each proper union of prime orbits. -/
theorem primeFixedFace_discrepancy_boundary
    (f₀ : MvPolynomial (ZMod p × W) K →ₗ[K] BooleanBarycentricRing (ZMod p × W) K)
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (fS : ∀ S : Finset W, S ≠ Finset.univ →
      MvPolynomial (ZMod p × S) K →ₗ[K] BooleanBarycentricRing (ZMod p × S) K)
    (ψS : ∀ S : Finset W, S ≠ Finset.univ →
      MvPolynomial S K →ₗ[K] BooleanBarycentricRing S K)
    (hf₀ : ∀ S hS x,
      booleanRestriction (primeOrbitEmbedding p (fixedOrbitSubsetEmbedding S)) (f₀ x) =
        fS S hS (MvPolynomial.killCompl
          (primeOrbitEmbedding p (fixedOrbitSubsetEmbedding S)).injective x))
    (hψ : ∀ S hS x, booleanRestriction (fixedOrbitSubsetEmbedding S) (ψ x) =
      ψS S hS (MvPolynomial.killCompl (fixedOrbitSubsetEmbedding S).injective x))
    (hcontrol : ∀ S hS x,
      primeFixedFaceQuotient p K (fS S hS x) =
        ψS S hS (primeOrbitMomentRetraction p K x))
    (x : MvPolynomial (ZMod p × W) K) :
    booleanBoundaryMap
      (ψ (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (f₀ x)) = 0 := by
  apply booleanBoundaryMap_eq_zero_of_subsetRestrictions K
  intro S hS
  rw [map_sub, hψ S hS, ← primeFixedFaceQuotient_restriction,
    hf₀ S hS, hcontrol S hS, primeOrbitMomentRetraction_restriction, sub_self]

theorem primeFixedFace_discrepancy_degree
    (f₀ : MvPolynomial (ZMod p × W) K →ₗ[K] BooleanBarycentricRing (ZMod p × W) K)
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (hf₀ : ∀ n x, x ∈ polynomialDegreePiece n →
      f₀ x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n)
    (hψ : ∀ n x, x ∈ polynomialDegreePiece n →
      ψ x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (x : MvPolynomial (ZMod p × W) K) (hx : x ∈ polynomialDegreePiece n) :
    ψ (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (f₀ x) ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) (n / p) := by
  exact Submodule.sub_mem _
    (hψ _ _ (primeOrbitMomentRetraction_mem_polynomialDegreePiece p K n x hx))
    (primeFixedFaceQuotient_degree p K n (f₀ x) (hf₀ n x hx))

theorem primeFixedFace_discrepancy_zero_of_degree_not_dvd
    (f₀ : MvPolynomial (ZMod p × W) K →ₗ[K] BooleanBarycentricRing (ZMod p × W) K)
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (hf₀ : ∀ n x, x ∈ polynomialDegreePiece n →
      f₀ x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (x : MvPolynomial (ZMod p × W) K)
    (hx : x ∈ polynomialDegreePiece n) (hn : ¬ p ∣ n) :
    ψ (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (f₀ x) = 0 := by
  rw [primeOrbitMomentRetraction_zero_of_polynomialDegree_not_dvd p K n x hx hn,
    map_zero, primeFixedFaceQuotient_zero_of_degree_not_dvd p K n hn (f₀ x) (hf₀ n x hx),
    sub_self]

end Discrepancy
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStableFaceGeometry.lean -/
section

section
/-! # Stable finite simplex faces in prime-orbit coordinates

The empty face is included.  A translation-stable finite subset is the
union of its full prime orbits, and its actual simplex atoms identify with
a prime coordinate times the actual atoms of its orbit-label face.  These
identifications commute with inclusions and with centralizing relabelings.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset

variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- A union of full prime orbits, as an actual face of the finite simplex. -/
def primeOrbitFace (S : Finset W) : Finset (ZMod p × W) := Finset.univ ×ˢ S

@[simp] theorem mem_primeOrbitFace (S : Finset W) (x : ZMod p) (w : W) :
    (x, w) ∈ primeOrbitFace p S ↔ w ∈ S := by
  simp only [primeOrbitFace, Finset.mem_product, Finset.mem_univ, true_and]

@[simp] theorem primeOrbitFace_empty : primeOrbitFace (W := W) p ∅ = ∅ := by
  ext v
  rcases v with ⟨x, w⟩
  simp only [mem_primeOrbitFace, Finset.notMem_empty]

@[simp] theorem primeOrbitFace_univ : primeOrbitFace (W := W) p Finset.univ = Finset.univ := by
  ext v
  rcases v with ⟨x, w⟩
  simp only [mem_primeOrbitFace, Finset.mem_univ]

@[simp] theorem primeOrbitFace_card (S : Finset W) : (primeOrbitFace p S).card = p * S.card := by
  simp only [primeOrbitFace, Finset.card_product, Finset.card_univ, ZMod.card]

@[simp] theorem primeOrbitFace_subset_iff (S T : Finset W) :
    primeOrbitFace p S ⊆ primeOrbitFace p T ↔ S ⊆ T := by
  constructor
  · intro h w hw
    exact (mem_primeOrbitFace p T 0 w).mp (h ((mem_primeOrbitFace p S 0 w).mpr hw))
  · intro h v hv
    exact (mem_primeOrbitFace p T v.1 v.2).mpr (h ((mem_primeOrbitFace p S v.1 v.2).mp hv))

/-- Literal invariance under the prime translations. -/
def PrimeTranslationStable (F : Finset (ZMod p × W)) : Prop :=
  ∀ t : ZMod p, F.image (primeOrbitRelabel p (Equiv.refl W) (fun _ => t)) = F

def primeStableFaceLabels (F : Finset (ZMod p × W)) : Finset W := F.image Prod.snd

theorem primeTranslationStable_mem_iff (F : Finset (ZMod p × W))
    (hF : PrimeTranslationStable p F) (x y : ZMod p) (w : W) :
    (x, w) ∈ F ↔ (y, w) ∈ F := by
  have hxy : ∀ x y : ZMod p, (x, w) ∈ F → (y, w) ∈ F := by
    intro x y hx
    rw [← hF (y - x)]
    refine Finset.mem_image.mpr ⟨(x, w), hx, ?_⟩
    apply Prod.ext
    · exact sub_add_cancel y x
    · rfl
  exact ⟨hxy x y, hxy y x⟩

theorem primeOrbitFace_stable (S : Finset W) : PrimeTranslationStable p (primeOrbitFace p S) := by
  intro t
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_primeOrbitFace p S (t + u.1) u.2).mpr
      ((mem_primeOrbitFace p S u.1 u.2).mp hu)
  · intro hv
    refine Finset.mem_image.mpr ⟨(v.1 - t, v.2), ?_, ?_⟩
    · exact (mem_primeOrbitFace p S (v.1 - t) v.2).mpr
        ((mem_primeOrbitFace p S v.1 v.2).mp hv)
    · apply Prod.ext
      · exact add_sub_cancel _ _
      · rfl

@[simp] theorem primeStableFaceLabels_orbitFace (S : Finset W) :
    primeStableFaceLabels p (primeOrbitFace p S) = S := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hw
    exact he ▸ (mem_primeOrbitFace p S v.1 v.2).mp hv
  · intro hw
    exact Finset.mem_image.mpr ⟨(0, w), (mem_primeOrbitFace p S 0 w).mpr hw, rfl⟩

/-- No nonempty-face assumption: this also classifies the empty stable face. -/
theorem primeStableFace_eq_orbitFace (F : Finset (ZMod p × W))
    (hF : PrimeTranslationStable p F) : F = primeOrbitFace p (primeStableFaceLabels p F) := by
  ext v
  rw [mem_primeOrbitFace]
  constructor
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  · intro hv
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
    apply (primeTranslationStable_mem_iff p F hF u.1 v.1 v.2).mp
    simpa only [← he] using hu

theorem primeTranslationStable_iff (F : Finset (ZMod p × W)) :
    PrimeTranslationStable p F ↔ F = primeOrbitFace p (primeStableFaceLabels p F) := by
  constructor
  · exact primeStableFace_eq_orbitFace p F
  · intro h
    rw [h]
    exact primeOrbitFace_stable p _

theorem primeStableFaceLabels_mono {F G : Finset (ZMod p × W)} (h : F ⊆ G) :
    primeStableFaceLabels p F ⊆ primeStableFaceLabels p G := Finset.image_subset_image h

/-- The actual vertices of a full-orbit face, before identifying atoms. -/
def primeOrbitFaceElements (S : Finset W) : (primeOrbitFace p S) ≃ (ZMod p × S) where
  toFun v := (v.val.1, ⟨v.val.2, (mem_primeOrbitFace p S v.val.1 v.val.2).mp v.property⟩)
  invFun v := ⟨(v.1, v.2.val), (mem_primeOrbitFace p S v.1 v.2.val).mpr v.2.property⟩
  left_inv v := Subtype.ext (Prod.eta v.val)
  right_inv v := Prod.ext rfl (Subtype.ext rfl)

/-- The exact atoms used in the original stalk definitions. -/
def primeOrbitFaceVertexEquiv (S : Finset W) :
    FaceVertex (primeOrbitFace p S) ≃ (ZMod p × FaceVertex S) :=
  (simplexVertexEquiv (primeOrbitFace p S)).trans
    ((primeOrbitFaceElements p S).trans
      (Equiv.prodCongr (Equiv.refl _) (simplexVertexEquiv S).symm))

@[simp] theorem primeOrbitFaceVertexEquiv_symm_val (S : Finset W)
    (v : ZMod p × FaceVertex S) :
    ((primeOrbitFaceVertexEquiv p S).symm v).val =
      {(v.1, (simplexVertexEquiv S v.2).val)} := rfl

theorem simplexVertexEquiv_inclusion_val {S T : Finset W} (h : S ⊆ T) (v : FaceVertex S) :
    (simplexVertexEquiv T (faceVertexInclusion h v)).val = (simplexVertexEquiv S v).val := by
  obtain ⟨u, rfl⟩ := (simplexVertexEquiv S).symm.surjective v
  have he : faceVertexInclusion h ((simplexVertexEquiv S).symm u) =
      (simplexVertexEquiv T).symm ⟨u.val, h u.property⟩ := rfl
  rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The coordinate square for every inclusion of stable faces. -/
theorem primeOrbitFaceVertexEquiv_inclusion {S T : Finset W} (h : S ⊆ T)
    (v : FaceVertex (primeOrbitFace p S)) :
    primeOrbitFaceVertexEquiv p T
        (faceVertexInclusion ((primeOrbitFace_subset_iff p S T).mpr h) v) =
      primeOrbitEmbedding p (faceVertexInclusion h) (primeOrbitFaceVertexEquiv p S v) := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (primeOrbitFaceVertexEquiv p S).symm.surjective v
  rw [Equiv.apply_symm_apply]
  apply (primeOrbitFaceVertexEquiv p T).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  change {(x, (simplexVertexEquiv S a).val)} =
    {(x, (simplexVertexEquiv T (faceVertexInclusion h a)).val)}
  rw [simplexVertexEquiv_inclusion_val]

theorem primeOrbitFaceVertexEquiv_inclusion_square {S T : Finset W} (h : S ⊆ T) :
    (faceVertexInclusion ((primeOrbitFace_subset_iff p S T).mpr h)).trans
        (primeOrbitFaceVertexEquiv p T).toEmbedding =
      (primeOrbitFaceVertexEquiv p S).toEmbedding.trans
        (primeOrbitEmbedding p (faceVertexInclusion h)) := by
  apply Function.Embedding.ext
  intro v
  exact primeOrbitFaceVertexEquiv_inclusion p h v

/-- The same coordinates for an arbitrary stable face, using its literal
image under the orbit-label projection. -/
def primeStableFaceVertexEquiv (F : Finset (ZMod p × W)) (hF : PrimeTranslationStable p F) :
    FaceVertex F ≃ (ZMod p × FaceVertex (primeStableFaceLabels p F)) :=
  (Equiv.cast (congrArg (fun T : Finset (ZMod p × W) => FaceVertex T)
    (primeStableFace_eq_orbitFace p F hF))).trans
      (primeOrbitFaceVertexEquiv p (primeStableFaceLabels p F))

section Relabeling
variable (σ : Equiv.Perm W) (g : W → ZMod p)

theorem primeOrbitFace_relabel (S : Finset W) :
    finsetOrderCongr (primeOrbitRelabel p σ g) (primeOrbitFace p S) =
      primeOrbitFace p (finsetOrderCongr σ S) := by
  ext v
  change v ∈ (primeOrbitFace p S).map (primeOrbitRelabel p σ g).toEmbedding ↔ _
  rw [Finset.mem_map, mem_primeOrbitFace]
  change (∃ u ∈ primeOrbitFace p S, primeOrbitRelabel p σ g u = v) ↔
    v.2 ∈ S.map σ.toEmbedding
  rw [Finset.mem_map]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u.2, (mem_primeOrbitFace p S u.1 u.2).mp hu, ?_⟩
    exact congrArg (fun z : ZMod p × W => z.2) he
  · rintro ⟨w, hw, he⟩
    refine ⟨(v.1 - g w, w), (mem_primeOrbitFace p S _ w).mpr hw, ?_⟩
    apply Prod.ext
    · exact add_sub_cancel _ _
    · exact he

theorem simplexVertexEquiv_order_val (S : Finset W) (v : FaceVertex S) :
    (simplexVertexEquiv (finsetOrderCongr σ S)
      (faceVertexOrderEquiv (finsetOrderCongr σ) S v)).val =
      σ (simplexVertexEquiv S v).val := by
  obtain ⟨u, rfl⟩ := (simplexVertexEquiv S).symm.surjective v
  have he : faceVertexOrderEquiv (finsetOrderCongr σ) S ((simplexVertexEquiv S).symm u) =
      (simplexVertexEquiv (finsetOrderCongr σ S)).symm
        ⟨σ u.val, Finset.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩ := by
    apply Subtype.ext
    exact Finset.map_singleton σ.toEmbedding u.val
  rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The relabeling of actual stalk atoms, with the target face identified by
the proved full-orbit face equality. -/
def primeOrbitFaceStalkRelabel (S : Finset W) :
    FaceVertex (primeOrbitFace p S) ≃ FaceVertex (primeOrbitFace p (finsetOrderCongr σ S)) :=
  (faceVertexOrderEquiv (finsetOrderCongr (primeOrbitRelabel p σ g)) (primeOrbitFace p S)).trans
    (Equiv.cast (congrArg (fun T : Finset (ZMod p × W) => FaceVertex T)
      (primeOrbitFace_relabel p σ g S)))

theorem primeOrbitFaceStalkRelabel_val (S : Finset W) (v : FaceVertex (primeOrbitFace p S)) :
    (primeOrbitFaceStalkRelabel p σ g S v).val =
      finsetOrderCongr (primeOrbitRelabel p σ g) v.val := by
  have hcast {F H : Finset (ZMod p × W)} (h : F = H) (a : FaceVertex F) :
      ((Equiv.cast (congrArg (fun T : Finset (ZMod p × W) => FaceVertex T) h)) a).val = a.val := by
    subst H
    rfl
  exact hcast (primeOrbitFace_relabel p σ g S) _

/-- The centralizing vertex permutation induces exactly the parent action
on the actual atoms of the orbit-label face, with the extracted shifts. -/
theorem primeOrbitFaceVertexEquiv_relabel (S : Finset W)
    (v : FaceVertex (primeOrbitFace p S)) :
    primeOrbitFaceVertexEquiv p (finsetOrderCongr σ S)
        (primeOrbitFaceStalkRelabel p σ g S v) =
      primeOrbitRelabel p (faceVertexOrderEquiv (finsetOrderCongr σ) S)
        (fun a => g (simplexVertexEquiv S a).val) (primeOrbitFaceVertexEquiv p S v) := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (primeOrbitFaceVertexEquiv p S).symm.surjective v
  rw [Equiv.apply_symm_apply]
  apply (primeOrbitFaceVertexEquiv p (finsetOrderCongr σ S)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rw [primeOrbitFaceStalkRelabel_val, primeOrbitFaceVertexEquiv_symm_val,
    finsetOrderCongr_apply, Finset.map_singleton, primeOrbitFaceVertexEquiv_symm_val]
  change {(g (simplexVertexEquiv S a).val + x, σ (simplexVertexEquiv S a).val)} =
    {(g (simplexVertexEquiv S a).val + x,
      (simplexVertexEquiv (finsetOrderCongr σ S)
        (faceVertexOrderEquiv (finsetOrderCongr σ) S a)).val)}
  rw [simplexVertexEquiv_order_val]

end Relabeling
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralGradedLift.lean -/
section


section

/-! # Integral equivariant lifting with explicit coefficient splittings

The extension-of-scalars argument does not require a field. An ordinary
retraction of the actual target kernel suffices, and the lower-generator
intersection has an explicit retraction obtained from the parameter basis.
These maps are used in the integral prime-power construction for the scalar
image assertion of Section 9.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical

section SplitKernel
variable {K G M N Q C : Type*} [CommRing K] [Group G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup Q] [Module K Q] [AddCommGroup C] [Module K C]

theorem exists_equivariantLift_of_coinduced_split_kernel
    (ρ : CyclicRepresentation K G M) (τ : CyclicRepresentation K G N)
    (υ : CyclicRepresentation K G Q)
    (q : N →ₗ[K] Q) (hq : RepresentationIntertwines τ υ q)
    (a : M →ₗ[K] Q) (ha : RepresentationIntertwines ρ υ a)
    (β : M →ₗ[K] N) (hqβ : q.comp β = a)
    (s : N →ₗ[K] LinearMap.ker q)
    (hs : s.comp (LinearMap.ker q).subtype = LinearMap.id)
    (e : LinearMap.ker q ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines
      (invariantSubmoduleRepresentation τ (LinearMap.ker q)
        (kernel_invariant_of_intertwines τ υ q hq)) coinducedRepresentation e.toLinearMap) :
    ∃ F : M →ₗ[K] N, RepresentationIntertwines ρ τ F ∧ q.comp F = a := by
  let H := LinearMap.ker q
  let ρH := invariantSubmoduleRepresentation τ H
    (kernel_invariant_of_intertwines τ υ q hq)
  have hi : RepresentationIntertwines ρH τ H.subtype := by
    intro g x
    rfl
  have hid : RepresentationIntertwines ρH ρH (LinearMap.id : H →ₗ[K] H) := by
    intro g x
    rfl
  obtain ⟨r, hre, hri⟩ := exists_equivariantExtension_of_coinduced
    ρH τ ρH e he H.subtype s hi hs LinearMap.id hid
  let P : N →ₗ[K] N := LinearMap.id - H.subtype.comp r
  have hP : RepresentationIntertwines τ τ P := by
    intro g x
    change τ g x - (r (τ g x)).val = τ g (x - (r x).val)
    rw [hre, map_sub]
    rfl
  have hPH (x : H) : P x.val = 0 := by
    have hrx := congrArg (fun F : H →ₗ[K] H => (F x).val) hri
    change x.val - (r x.val).val = 0
    change (r x.val).val = x.val at hrx
    rw [hrx, sub_self]
  have hqP (x : N) : q (P x) = q x := by
    change q (x - (r x).val) = q x
    rw [map_sub, show q (r x).val = 0 from (r x).property, sub_zero]
  refine ⟨P.comp β, ?_, ?_⟩
  · intro g x
    have hx : β (ρ g x) - τ g (β x) ∈ H := by
      change q (β (ρ g x) - τ g (β x)) = 0
      rw [map_sub, hq]
      have hb1 := congrArg (fun F : M →ₗ[K] Q => F (ρ g x)) hqβ
      have hb2 := congrArg (fun F : M →ₗ[K] Q => F x) hqβ
      change q (β (ρ g x)) = a (ρ g x) at hb1
      change q (β x) = a x at hb2
      rw [hb1, hb2, ha, sub_self]
    have hz := hPH ⟨β (ρ g x) - τ g (β x), hx⟩
    rw [map_sub] at hz
    change P (β (ρ g x)) = τ g (P (β x))
    exact (sub_eq_zero.mp hz).trans (hP g (β x))
  · apply LinearMap.ext
    intro x
    change q (P (β x)) = a x
    rw [hqP]
    exact congrArg (fun F : M →ₗ[K] Q => F x) hqβ


end SplitKernel

namespace ScalarGradedBasis

variable {K A M I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
variable (s : ScalarGradedBasis K A M I J)

/-- Projection onto the actual span of the lower-degree parameter generators. -/
def cutProjection (n : ℕ) : M →ₗ[A] M :=
  s.parameterBasis.constr A (fun i =>
    if s.generatorDegree i < n then s.parameterBasis i else 0)

@[simp] theorem cutProjection_generator (n : ℕ) (i : I) :
    s.cutProjection n (s.parameterBasis i) =
      if s.generatorDegree i < n then s.parameterBasis i else 0 :=
  s.parameterBasis.constr_basis A _ i

@[simp] theorem cutProjection_coefficient (n : ℕ) (j : J) :
    s.cutProjection n (s.coefficientBasis j) =
      if s.generatorDegree (s.parent j) < n then s.coefficientBasis j else 0 := by
  rw [s.coefficient_eq, map_smul, s.cutProjection_generator]
  split_ifs <;> simp

theorem cutProjection_mem (n : ℕ) (x : M) : s.cutProjection n x ∈ s.cut n := by
  rw [← s.parameterBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply (s.cut n).sum_mem
  intro i hi
  rw [map_smul, s.cutProjection_generator]
  apply (s.cut n).smul_mem
  split_ifs with h
  · exact s.generator_mem_cut i h
  · exact (s.cut n).zero_mem

theorem cutProjection_eq_self (n : ℕ) (x : M) (hx : x ∈ s.cut n) :
    s.cutProjection n x = x := by
  have he := s.maps_eq_on_cut n (s.cutProjection n) LinearMap.id
    (fun i hi => by simp only [s.cutProjection_generator, if_pos hi, LinearMap.id_apply]) x hx
  exact he

theorem cutProjection_preserves_piece (n k : ℕ) (x : M) (hx : x ∈ s.piece k) :
    s.cutProjection n x ∈ s.piece k := by
  let f : M →ₗ[K] M := (s.cutProjection n).restrictScalars K
  change f x ∈ s.piece k
  rw [← s.coefficientBasis.linearCombination_repr x,
    Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply (s.piece k).sum_mem
  intro j hj
  rw [map_smul]
  apply (s.piece k).smul_mem
  change s.cutProjection n (s.coefficientBasis j) ∈ s.piece k
  rw [s.cutProjection_coefficient]
  split_ifs
  · have hd : s.degree j = k := by
      by_contra hne
      exact Finsupp.mem_support_iff.mp hj (hx j hne)
    exact hd ▸ s.coefficient_mem_piece j
  · exact (s.piece k).zero_mem

/-- The actual intersection of the lower-generator span with a homogeneous piece. -/
def cutDegreeIntersection (n k : ℕ) : Submodule K (s.piece k) :=
  ((s.cut n).restrictScalars K).comap (s.piece k).subtype

/-- An integral retraction; no complement or basis over a field is assumed. -/
def cutDegreeRetraction (n k : ℕ) : s.piece k →ₗ[K] s.cutDegreeIntersection n k where
  toFun x := ⟨⟨s.cutProjection n x.val,
    s.cutProjection_preserves_piece n k x.val x.property⟩,
    s.cutProjection_mem n x.val⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((s.cutProjection n).restrictScalars K).map_smul c x.val

theorem cutDegreeRetraction_subtype (n k : ℕ) :
    (s.cutDegreeRetraction n k).comp (s.cutDegreeIntersection n k).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact s.cutProjection_eq_self n x.val.val x.property

end ScalarGradedBasis

namespace ScalarGradedBasis

open Classical

variable {K A M I J N Q G : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
  [Group G]

variable (s : ScalarGradedBasis K A M I J)
variable (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
variable (υ : CyclicRepresentation A G Q)
variable (T : ℕ → Submodule K N) (q : N →ₗ[A] Q) (a : M →ₗ[A] Q)
variable (hρ : ∀ g n x, x ∈ s.piece n → ρ g x ∈ s.piece n)
variable (hτ : ∀ g n x, x ∈ T n → τ g x ∈ T n)
variable (hq : RepresentationIntertwines τ υ q)

def integralSourceDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (s.piece n) :=
  invariantSubmoduleRepresentation (restrictRepresentation ρ) (s.piece n)
    (fun g x hx => hρ g n x hx)

def integralTargetDegreeRepresentation (n : ℕ) : CyclicRepresentation K G (T n) :=
  invariantSubmoduleRepresentation (restrictRepresentation τ) (T n)
    (fun g x hx => hτ g n x hx)

def integralDegreeQuotient (n : ℕ) : T n →ₗ[K] Q :=
  (q.restrictScalars K).comp (T n).subtype

def integralDegreeTarget (n : ℕ) : s.piece n →ₗ[K] Q :=
  (a.restrictScalars K).comp (s.piece n).subtype

include hq in
theorem integralDegreeQuotient_intertwines (n : ℕ) :
    RepresentationIntertwines (integralTargetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (integralDegreeQuotient T q n) := by
  intro g x
  exact hq g x.val

def integralKernelDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (LinearMap.ker (integralDegreeQuotient T q n)) :=
  invariantSubmoduleRepresentation (integralTargetDegreeRepresentation τ T hτ n)
    (LinearMap.ker (integralDegreeQuotient T q n))
    (kernel_invariant_of_intertwines (integralTargetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (integralDegreeQuotient T q n)
      (integralDegreeQuotient_intertwines τ υ T q hτ hq n))

variable
  (hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
    s.multiplier j • y ∈ T (s.degree j))

include hρ hmult

/-- The full one-degree step, including construction of the lower subspace and
its explicit integral linear retraction. The source splitting is constructed
from the actual parameter basis and preserves the chosen homogeneous degree. -/
theorem integralDegreeLift_of_coinduced_kernel
    {n : ℕ} {f : M →ₗ[A] N} (hf : s.LiftStage ρ τ T q a n f)
    (β : s.piece n →ₗ[K] T n)
    (hβ : RepresentationIntertwines (s.integralSourceDegreeRepresentation ρ hρ n)
      (integralTargetDegreeRepresentation τ T hτ n) β)
    (hqβ : (integralDegreeQuotient T q n).comp β = s.integralDegreeTarget a n)
    {C : Type*} [AddCommGroup C] [Module K C]
    (e : LinearMap.ker (integralDegreeQuotient T q n) ≃ₗ[K] (G → C))
    (he : RepresentationIntertwines (integralKernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation e.toLinearMap) :
    ∃ L : s.piece n →ₗ[K] N, s.DegreeLift ρ τ T q a hρ n f L := by
  let ρn := s.integralSourceDegreeRepresentation ρ hρ n
  let τn := integralTargetDegreeRepresentation τ T hτ n
  let υK := restrictRepresentation (K := K) υ
  let qn := integralDegreeQuotient T q n
  let an := s.integralDegreeTarget a n
  let U : Submodule K (s.piece n) :=
    ((s.cut n).restrictScalars K).comap (s.piece n).subtype
  have hU : ∀ g x, x ∈ U → ρn g x ∈ U := by
    intro g x hx
    change ρ g x.val ∈ s.cut n
    exact s.cut_invariant ρ hρ n g x.val hx
  let r : s.piece n →ₗ[K] U := s.cutDegreeRetraction n n
  have hr : r.comp U.subtype = LinearMap.id := s.cutDegreeRetraction_subtype n n
  let fU : U →ₗ[K] T n :=
    LinearMap.codRestrict (T n)
      ((f.restrictScalars K).comp ((s.piece n).subtype.comp U.subtype)) (by
        intro x
        exact s.graded_of_generators T hmult f hf.1 n x.val.val x.val.property)
  have hfU : RepresentationIntertwines
      (invariantSubmoduleRepresentation ρn U hU) τn fU := by
    intro g x
    apply Subtype.ext
    exact LiftStage.equivariant_on_cut s ρ τ T q a hf g x.val.val x.property
  have hqfU : qn.comp fU = an.comp U.subtype := by
    ext x
    exact LiftStage.quotient_on_cut s ρ τ T q a hf x.val.val x.property
  have hqn : RepresentationIntertwines τn υK qn :=
    integralDegreeQuotient_intertwines τ υ T q hτ hq n
  obtain ⟨L, hLeq, hLU, hqL⟩ := equivariant_lift_extend_subspace
    ρn τn υK U hU r hr qn hqn an β hβ hqβ fU hfU hqfU e he
  refine ⟨(T n).subtype.comp L, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (L x).property
  · intro g x
    exact congrArg Subtype.val (hLeq g x)
  · intro x
    exact congrArg (fun F : s.piece n →ₗ[K] Q => F x) hqL
  · intro x hx
    let ux : U := ⟨x, hx⟩
    exact congrArg (fun F : U →ₗ[K] T n => (F ux).val) hLU

/-- Graded parameter-linear equivariant lifting, with every one-degree
extension proved from regular-orbit coordinates for its actual kernel. -/
theorem exists_integralEquivariantGradedLift_of_coinduced_kernels [Fintype I]
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hβ : ∀ n, RepresentationIntertwines (s.integralSourceDegreeRepresentation ρ hρ n)
      (integralTargetDegreeRepresentation τ T hτ n) (β n))
    (hqβ : ∀ n, (integralDegreeQuotient T q n).comp (β n) = s.integralDegreeTarget a n)
    (e : ∀ n, LinearMap.ker (integralDegreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (integralKernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  apply s.exists_equivariantGradedLift_of_degreeExtensions ρ τ T q a hρ hmult
  intro n f hf
  exact s.integralDegreeLift_of_coinduced_kernel ρ τ υ T q a hρ hτ hq hmult hf
    (β n) (hβ n) (hqβ n) (e n) (he n)

/-- The form used for the actual face rings: the preliminary lift is required
only to preserve degree and the prescribed quotient map.  All equivariance is
constructed from the explicit regular-orbit kernels. -/
theorem exists_integralEquivariantGradedLift_of_split_ordinary_lifts [Fintype I]
    (ha : RepresentationIntertwines ρ υ a)
    (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
    (β : ∀ n, s.piece n →ₗ[K] T n)
    (hqβ : ∀ n, (integralDegreeQuotient T q n).comp (β n) = s.integralDegreeTarget a n)
    (r : ∀ n, T n →ₗ[K] LinearMap.ker (integralDegreeQuotient T q n))
    (hr : ∀ n, (r n).comp (LinearMap.ker (integralDegreeQuotient T q n)).subtype = LinearMap.id)
    (e : ∀ n, LinearMap.ker (integralDegreeQuotient T q n) ≃ₗ[K] (G → C n))
    (he : ∀ n, RepresentationIntertwines
      (integralKernelDegreeRepresentation τ υ T q hτ hq n)
      coinducedRepresentation (e n).toLinearMap) :
    ∃ f : M →ₗ[A] N,
      (∀ n x, x ∈ s.piece n → f x ∈ T n) ∧ q.comp f = a ∧
      RepresentationIntertwines ρ τ f := by
  have hβeq : ∀ n, ∃ F : s.piece n →ₗ[K] T n,
      RepresentationIntertwines (s.integralSourceDegreeRepresentation ρ hρ n)
        (integralTargetDegreeRepresentation τ T hτ n) F ∧
      (integralDegreeQuotient T q n).comp F = s.integralDegreeTarget a n := by
    intro n
    apply exists_equivariantLift_of_coinduced_split_kernel
      (s.integralSourceDegreeRepresentation ρ hρ n) (integralTargetDegreeRepresentation τ T hτ n)
      (restrictRepresentation υ) (integralDegreeQuotient T q n)
      (integralDegreeQuotient_intertwines τ υ T q hτ hq n) (s.integralDegreeTarget a n)
      (fun g x => ha g x.val) (β n) (hqβ n) (r n) (hr n) (e n) (he n)
  choose F hF hqF using hβeq
  exact s.exists_integralEquivariantGradedLift_of_coinduced_kernels
    ρ τ υ T q a hρ hτ hq hmult C F hF hqF e he

end ScalarGradedBasis
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerControlledCoinduction.lean -/
section


section

/-! # Coinduction and splitting for every actual controlled degree kernel

The degree-restricted parameter quotient has exactly the simultaneous
boundary/fixed-face kernel. Multiplication by the invariant top variable
identifies its positive degree pieces with the original fixed-face kernel.
The degrees below the top rank vanish. This supplies, over arbitrary K,
both hypotheses of the integral graded lifting theorem.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
universe uW uG uK
open Classical

variable (p : ℕ) [Fact p.Prime]
variable {W : Type uW} {G : Type uG} [Fintype W] [Nonempty W] [Group G]
variable (K : Type uK) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : LinearOrder (ZMod p × W) := primePowerVertexOrder p

def primeControlledParameterHomogeneousEquiv (n : ℕ) :
    LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n) ≃ₗ[K]
      primeControlledHomogeneousKernel (W := W) p K n :=
  LinearEquiv.ofEq _ _ (primeControlledParameterDegreeKernel_eq p K n)

def primeControlledParameterDegreeRetraction (n : ℕ) :
    PrimeBooleanDegreePiece (W := W) p K n →ₗ[K]
      LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n) :=
  (primeControlledParameterHomogeneousEquiv p K n).symm.toLinearMap.comp
    (primeControlledHomogeneousProjection p K n)

theorem primeControlledParameterDegreeRetraction_retract (n : ℕ) :
    (primeControlledParameterDegreeRetraction (W := W) p K n).comp
      (LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n)).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (primeControlledParameterHomogeneousEquiv p K n).injective
  change primeControlledParameterHomogeneousEquiv p K n
      ((primeControlledParameterHomogeneousEquiv p K n).symm
        (primeControlledHomogeneousProjection p K n x.val)) =
      primeControlledParameterHomogeneousEquiv p K n x
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (primeControlledHomogeneousProjection_retract p K n)
    (primeControlledParameterHomogeneousEquiv p K n x)

def primeControlledParameterDegreeRepresentation (n : ℕ) :
    CyclicRepresentation K G (LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n)) :=
  ScalarGradedBasis.integralKernelDegreeRepresentation
    (primeBooleanParameterRepresentation p K ρ) (primeControlledParameterRepresentation p K ρ hρ)
    (PrimeBooleanDegreePiece (W := W) p K) (primeControlledParameterKernel (W := W) p K).mkQ
    (primeBooleanParameterRepresentation_degree p K ρ)
    (primeControlledParameterQuotient_intertwines p K ρ hρ) n

/-- Top multiplication, with the target expressed as the kernel of the
actual degree-restricted parameter quotient map. -/
def primeControlledParameterTopEquiv (n : ℕ) :
    PrimeFixedKernelDegreePiece (W := W) p K n ≃ₗ[K]
      LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K (n + Fintype.card (ZMod p × W))) :=
  (primeControlledHomogeneousTopEquiv p K n).trans
    (primeControlledParameterHomogeneousEquiv p K (n + Fintype.card (ZMod p × W))).symm

@[simp] theorem primeControlledParameterTopEquiv_apply (n : ℕ)
    (x : PrimeFixedKernelDegreePiece (W := W) p K n) :
    (primeControlledParameterTopEquiv p K n x).val.val = booleanTop * x.val.val := rfl

theorem primeControlledParameterTopEquiv_intertwines (n : ℕ) :
    RepresentationIntertwines (primeFixedKernelHomogeneousRepresentation p K ρ hρ n)
      (primeControlledParameterDegreeRepresentation p K ρ hρ (n + Fintype.card (ZMod p × W)))
      (primeControlledParameterTopEquiv p K n).toLinearMap := by
  intro g x
  apply Subtype.ext
  apply Subtype.ext
  change booleanTop * (primeFixedKernelRepresentation p K ρ hρ g x.val).val =
    booleanVertexRelabelEquiv (ρ g) (booleanTop * x.val.val)
  rw [primeFixedKernelRepresentation_val, map_mul, booleanVertexRelabel_top]

theorem primeControlledParameterDegree_zero_below (n : ℕ)
    (hn : n < Fintype.card (ZMod p × W))
    (x : LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n)) : x = 0 := by
  let y := (primeControlledDegreeSwap p K n).symm
    (primeControlledParameterHomogeneousEquiv p K n x)
  have hy := primeControlledDegree_zero_below p K n hn y
  apply (primeControlledParameterHomogeneousEquiv p K n).injective
  apply (primeControlledDegreeSwap p K n).symm.injective
  simpa only [map_zero] using hy

section Coinduced
variable [Finite G] [IsCyclic G]
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))

include hG hZ htranslations

/-- All homogeneous simultaneous kernels are actual regular function modules,
including the zero pieces below the top rank. -/
theorem primeControlledParameterDegree_isCoinduced (n : ℕ) :
    ∃ J : Type uW, ∃ e : LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n) ≃ₗ[K]
      (G → J → K),
      RepresentationIntertwines (primeControlledParameterDegreeRepresentation p K ρ hρ n)
        coinducedRepresentation e.toLinearMap := by
  by_cases hn : Fintype.card (ZMod p × W) ≤ n
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    have hn' : n = m + Fintype.card (ZMod p × W) := hm.trans (Nat.add_comm _ _)
    clear hm
    subst n
    obtain ⟨J, e, he⟩ := primeFixedKernelDegree_isCoinduced p K ρ hρ hG Z hZ htranslations m
    let t := primeControlledParameterTopEquiv (W := W) p K m
    refine ⟨J, t.symm.trans e, ?_⟩
    intro g x
    have ht : t.symm (primeControlledParameterDegreeRepresentation p K ρ hρ
          (m + Fintype.card (ZMod p × W)) g x) =
        primeFixedKernelHomogeneousRepresentation p K ρ hρ m g (t.symm x) := by
      apply t.injective
      rw [LinearEquiv.apply_symm_apply]
      have hh := primeControlledParameterTopEquiv_intertwines p K ρ hρ m g (t.symm x)
      change t (primeFixedKernelHomogeneousRepresentation p K ρ hρ m g (t.symm x)) =
        primeControlledParameterDegreeRepresentation p K ρ hρ
          (m + Fintype.card (ZMod p × W)) g (t (t.symm x)) at hh
      simpa only [LinearEquiv.apply_symm_apply] using hh.symm
    change e (t.symm (primeControlledParameterDegreeRepresentation p K ρ hρ
      (m + Fintype.card (ZMod p × W)) g x)) = _
    exact (congrArg e ht).trans (he g (t.symm x))
  · have hlt : n < Fintype.card (ZMod p × W) := Nat.lt_of_not_ge hn
    letI : Subsingleton (LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n)) :=
      ⟨fun x y => (primeControlledParameterDegree_zero_below p K n hlt x).trans
        (primeControlledParameterDegree_zero_below p K n hlt y).symm⟩
    let e : LinearMap.ker (primeControlledParameterDegreeMap (W := W) p K n) ≃ₗ[K]
        (G → PEmpty.{uW+1} → K) := LinearEquiv.ofSubsingleton _ _
    refine ⟨PEmpty.{uW+1}, e, ?_⟩
    intro g x
    exact Subsingleton.elim _ _

end Coinduced
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedBasisTransport.lean -/
section


section

/-! # Transport of the positive graded parameter basis

Both the parameter basis and the coefficient basis are transported through
an actual parameter-linear equivalence. Thus the polynomial source in the
integral controlled lift has the same positive graded free-module structure
as the previously verified Boolean descent basis. Its homogeneous pieces
are identified with ordinary polynomial degree by an explicit grading law.
-/

noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal
open Classical
open scoped CyclicParameterAction

namespace ScalarGradedBasis
variable {K A M N I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]

/-- Transport both actual free bases through the same linear equivalence. -/
def transport (s : ScalarGradedBasis K A M I J) (e : M ≃ₗ[A] N) :
    ScalarGradedBasis K A N I J where
  parameterBasis := s.parameterBasis.map e
  coefficientBasis := s.coefficientBasis.map (e.restrictScalars K)
  generatorDegree := s.generatorDegree
  degree := s.degree
  parent := s.parent
  multiplier := s.multiplier
  coefficient_eq j := by
    change e (s.coefficientBasis j) = s.multiplier j • e (s.parameterBasis (s.parent j))
    rw [s.coefficient_eq, map_smul]
  parent_degree_le := s.parent_degree_le
  equal_degree_eq j hj := by
    change e (s.coefficientBasis j) = e (s.parameterBasis (s.parent j))
    exact congrArg e (s.equal_degree_eq j hj)
  generator_homogeneous i j hj := by
    change s.coefficientBasis.repr (e.symm (e (s.parameterBasis i))) j = 0
    rw [e.symm_apply_apply]
    exact s.generator_homogeneous i j hj

@[simp] theorem transport_parameterBasis (s : ScalarGradedBasis K A M I J)
    (e : M ≃ₗ[A] N) (i : I) :
    (s.transport e).parameterBasis i = e (s.parameterBasis i) := rfl

@[simp] theorem transport_coefficientBasis (s : ScalarGradedBasis K A M I J)
    (e : M ≃ₗ[A] N) (j : J) :
    (s.transport e).coefficientBasis j = e (s.coefficientBasis j) := rfl

@[simp] theorem mem_transport_piece (s : ScalarGradedBasis K A M I J)
    (e : M ≃ₗ[A] N) (n : ℕ) (y : N) :
    y ∈ (s.transport e).piece n ↔ e.symm y ∈ s.piece n := Iff.rfl

@[simp] theorem transport_mem_piece (s : ScalarGradedBasis K A M I J)
    (e : M ≃ₗ[A] N) (n : ℕ) (x : M) :
    e x ∈ (s.transport e).piece n ↔ x ∈ s.piece n := by
  rw [mem_transport_piece, e.symm_apply_apply]

end ScalarGradedBasis

section Polynomial
variable {V K : Type*} [Fintype V] [LinearOrder V] [CommRing K]

/-- The source basis used in the polynomial-to-Boolean integral lifting step. -/
def polynomialScalarGradedBasis
    (e : BooleanBarycentricRing V K ≃ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K) :
    ScalarGradedBasis K (MvPolynomial (Fin (Fintype.card V)) K) (MvPolynomial V K)
      (VertexOrdering (Fintype.card V) V)
      (VertexOrdering (Fintype.card V) V × ColorExponent V) :=
  booleanScalarGradedBasis.transport e

theorem polynomialScalarGradedBasis_piece_eq
    (e : BooleanBarycentricRing V K ≃ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      MvPolynomial V K)
    (he : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n ↔ e x ∈ polynomialDegreePiece n)
    (n : ℕ) : (polynomialScalarGradedBasis e).piece n = polynomialDegreePiece n := by
  apply Submodule.ext
  intro y
  change y ∈ (booleanScalarGradedBasis.transport e).piece n ↔ _
  rw [ScalarGradedBasis.mem_transport_piece, booleanScalarGradedBasis_piece_eq,
    he, e.apply_symm_apply]

end Polynomial
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicGradedIsomorphism.lean -/
section


section

/-! # A graded boundary lift is an isomorphism

The proof uses a finite triangular argument on the actual parameter basis.
A homogeneous element divisible by the positive-degree top parameter belongs
to the span of strictly lower-degree parameter generators.  Thus two graded
parameter lifts with the same boundary differ by a strictly triangular map
after conjugating by either known lift.  The coefficient ring is arbitrary.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial
open scoped CyclicParameterAction

section Abstract

variable {K A M I J : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem ScalarGradedBasis.bijective_of_lower_cut_errors
    (s : ScalarGradedBasis K A M I J) (f : M →ₗ[A] M)
    (hf : ∀ i, f (s.parameterBasis i) - s.parameterBasis i ∈ s.cut (s.generatorDegree i)) :
    Function.Bijective f := by
  have hcoeff (i j : I) (hij : s.generatorDegree i ≤ s.generatorDegree j) :
      s.parameterBasis.repr (f (s.parameterBasis i) - s.parameterBasis i) j = 0 := by
    by_contra hn
    have hs := (s.parameterBasis.mem_span_image).mp (hf i)
    have hj := hs (Finsupp.mem_support_iff.mpr hn)
    exact (Nat.not_lt_of_ge hij) hj
  apply canonicalLeading_bijective s.parameterBasis s.parameterBasis s.generatorDegree f
  constructor
  · intro i
    have hh := hcoeff i i le_rfl
    simpa only [map_sub, Finsupp.sub_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, sub_eq_zero] using hh
  · intro i j hne hij
    have hh := hcoeff i j hij
    simpa [Finsupp.single_apply, hne, Ne.symm hne] using hh

end Abstract

section Boolean

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

theorem chainOrdinaryDegree_add (a b : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + b) = chainOrdinaryDegree a + chainOrdinaryDegree b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])

theorem chainOrdinaryDegree_add_top (a : BooleanFace V →₀ ℕ) :
    chainOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      chainOrdinaryDegree a + Fintype.card V := by
  rw [chainOrdinaryDegree_add]
  simp [chainOrdinaryDegree, booleanTopFace]

theorem booleanTop_mul_shift_coefficient (x : BooleanBarycentricRing V K)
    (a : BooleanChainExponent V) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem booleanTop_predecessor_degree (m : ℕ) (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) (m + Fintype.card V)) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ m + Fintype.card V := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [booleanTop_mul_shift_coefficient] at hh

theorem booleanTop_homogeneous_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (x : BooleanBarycentricRing V K)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : chainOrdinaryDegree b.val ≠ n := by
    change chainOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [chainOrdinaryDegree_add_top]
    omega
  have hh := hx b hb
  rw [booleanTop_mul_shift_coefficient] at hh
  exact hh

theorem booleanTop_mul_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n) :
    booleanTop * x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  let c : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hc : c.val + 1 = Fintype.card V := by dsimp [c]; omega
  have ht : booleanTop * x = (MvPolynomial.X c : MvPolynomial (Fin (Fintype.card V)) K) • x := by
    change booleanTop * x = booleanColorMap (MvPolynomial.X c) * x
    rw [booleanColorMap, MvPolynomial.aeval_X, ← booleanRankParameter_color, hc,
      booleanRankParameter_top]
  rw [ht]
  exact ((booleanScalarGradedBasis (V := V) (K := K)).cut n).smul_mem _ hx

/-- A genuine top-boundary kernel element of degree `n` uses only parameter
generators of degree strictly below `n`. -/
theorem booleanBoundary_homogeneous_mem_cut (n : ℕ) (x : BooleanBarycentricRing V K)
    (hx : x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : booleanBoundaryMap x = 0) :
    x ∈ (booleanScalarGradedBasis (V := V) (K := K)).cut n := by
  obtain ⟨y, hy⟩ := (booleanBoundaryMap_eq_zero_iff x).mp hb
  rw [booleanScalarGradedBasis_piece_eq] at hx
  have htop : booleanTop * y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n := by simpa only [hy] using hx
  by_cases hn : Fintype.card V ≤ n
  · have hydeg : y ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece
        (n - Fintype.card V) := by
      rw [booleanScalarGradedBasis_piece_eq]
      apply booleanTop_predecessor_degree
      simpa only [Nat.sub_add_cancel hn] using htop
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    have hlt : n - Fintype.card V < n := by omega
    rw [← hy]
    exact booleanTop_mul_mem_cut n y
      ((booleanScalarGradedBasis (V := V) (K := K)).homogeneous_mem_cut hlt y hydeg)
  · have hyzero := booleanTop_homogeneous_zero_below n (Nat.lt_of_not_ge hn) y htop
    rw [← hy, hyzero, mul_zero]
    exact Submodule.zero_mem _

theorem booleanParameterEnd_bijective_of_graded_boundary_identity
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K)
    (hd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hb : ∀ x, booleanBoundaryMap (f x) = booleanBoundaryMap x) :
    Function.Bijective f := by
  let s := booleanScalarGradedBasis (V := V) (K := K)
  apply s.bijective_of_lower_cut_errors f
  intro i
  apply booleanBoundary_homogeneous_mem_cut
  · exact (s.piece (s.generatorDegree i)).sub_mem
      (hd _ _ (s.generator_mem_piece i)) (s.generator_mem_piece i)
  · rw [map_sub, hb, sub_self]

/-- Any graded parameter-linear lift of the same actual boundary is an
isomorphism once one graded parameter comparison is known. -/
theorem parameterLift_bijective_of_same_boundary
    (e : ParameterEquiv (booleanColorMap (V := V) (K := K)) polynomialColorMap)
    (b : LocalBoundaryComparison (V := V) (K := K))
    (he : ∀ x, polynomialBooleanBoundaryMap (e.toLinearEquiv x) =
      b.toLinearEquiv (booleanBoundaryMap x))
    (hed : ∀ n y, y ∈ polynomialDegreePiece n → e.toLinearEquiv.symm y ∈
      (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hfd : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ polynomialDegreePiece n)
    (hfb : ∀ x, polynomialBooleanBoundaryMap (f x) =
      polynomialBooleanBoundaryMap (e.toLinearEquiv x)) : Function.Bijective f := by
  let T : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K :=
    e.overParameters.symm.toLinearMap.comp (parameterLinearMap f hf)
  have hT : Function.Bijective T := by
    apply booleanParameterEnd_bijective_of_graded_boundary_identity T
    · intro n x hx
      exact hed n (f x) (hfd n x hx)
    · intro x
      apply b.toLinearEquiv.injective
      rw [← he, ← he]
      change polynomialBooleanBoundaryMap (e.toLinearEquiv (e.toLinearEquiv.symm (f x))) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hfb x
  have hcomp : (fun x => e.toLinearEquiv (T x)) = f := by
    funext x
    exact e.toLinearEquiv.apply_symm_apply (f x)
  rw [← hcomp]
  exact e.toLinearEquiv.bijective.comp hT

end Boolean
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicReverseBijectivity.lean -/
section


section

/-! # Bijectivity of normalized reverse controlled lifts

A homogeneous parameter-linear Boolean endomorphism with identity boundary
has strictly lower generator-degree error on every descent-basis vector.
The already proved finite triangular inversion theorem makes it bijective.
Composing an actual polynomial-to-Boolean lift with an ordinary inverse
comparison reduces its bijectivity to this criterion, over every coefficient
ring and without any scalar invertibility assumption.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical
open scoped CyclicParameterAction

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

theorem booleanEndomorphism_bijective_of_identity_boundary
    (f : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K)
    (hgrade : ∀ n x, x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n →
      f x ∈ (booleanScalarGradedBasis (V := V) (K := K)).piece n)
    (hboundary : ∀ x, booleanBoundaryMap (f x) = booleanBoundaryMap x) :
    Function.Bijective f := by
  let s := booleanScalarGradedBasis (V := V) (K := K)
  apply s.bijective_of_lower_cut_errors f
  intro i
  apply booleanBoundary_homogeneous_mem_cut
  · exact (s.piece (s.generatorDegree i)).sub_mem
      (hgrade _ _ (s.generator_mem_piece i)) (s.generator_mem_piece i)
  · rw [map_sub, hboundary, sub_self]

/-- The ordinary comparison is an actual equivalence. Its use here introduces
no presumed inverse for the new controlled lift. -/
theorem reverseParameterLift_bijective_of_same_boundary
    (L : BooleanBarycentricRing V K ≃ₗ[K] MvPolynomial V K)
    (hLp : IsParameterLinear booleanColorMap polynomialColorMap L.toLinearMap)
    (hLg : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → L x ∈ polynomialDegreePiece n)
    (f : MvPolynomial V K →ₗ[K] BooleanBarycentricRing V K)
    (hfp : IsParameterLinear polynomialColorMap booleanColorMap f)
    (hfg : ∀ n x, x ∈ polynomialDegreePiece n →
      f x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => chainOrdinaryDegree a.val) n)
    (hboundary : ∀ x, booleanBoundaryMap (f (L x)) = booleanBoundaryMap x) :
    Function.Bijective f := by
  let F : BooleanBarycentricRing V K →ₗ[MvPolynomial (Fin (Fintype.card V)) K]
      BooleanBarycentricRing V K := {
    toFun := fun x => f (L x)
    map_add' := by intro x y; rw [map_add, map_add]
    map_smul' := by
      intro a x
      change f (L (booleanColorMap a * x)) = booleanColorMap a * f (L x)
      exact (congrArg f (hLp a x)).trans (hfp a (L x)) }
  have hF : Function.Bijective F := booleanEndomorphism_bijective_of_identity_boundary F
    (by
      intro n x hx
      rw [booleanScalarGradedBasis_piece_eq] at hx ⊢
      exact hfg n _ (hLg n x hx)) hboundary
  constructor
  · intro x y hxy
    apply L.symm.injective
    apply hF.1
    change f (L (L.symm x)) = f (L (L.symm y))
    simpa only [LinearEquiv.apply_symm_apply] using hxy
  · intro y
    obtain ⟨x, hx⟩ := hF.2 y
    exact ⟨L x, hx⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerLocalLift.lean -/
section


section

/-! # Integral controlled local lifts for cyclic prime-power stabilizers

The input is an actual ordinary parameter-linear lift to the original
Boolean ring whose two prescribed quotient values are equivariant. The
output is a parameter-linear equivariant lift with those exact values and
ordinary degrees. No field, localization, or invertibility hypothesis is
used. Normalization and bijectivity follow from the actual boundary and
the top-coordinate kernel calculation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Nonempty W] [Group G] [Finite G] [IsCyclic G]
variable (K : Type*) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : LinearOrder (ZMod p × W) := primePowerVertexOrder p

include hρ hG hZ htranslations

/-- Actual full integral local lifting, with a supplied ordinary lift and
with both prescribed equations retained exactly. -/
theorem exists_primePower_controlled_parameter_lift
    (L : BooleanBarycentricRing (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
      MvPolynomial (ZMod p × W) K)
    (hL : ∀ n x, x ∈ PrimeBooleanDegreePiece p K n ↔ L x ∈ polynomialDegreePiece n)
    (β : MvPolynomial (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
      BooleanBarycentricRing (ZMod p × W) K)
    (hβ : ∀ n x, x ∈ polynomialDegreePiece n → β x ∈ PrimeBooleanDegreePiece p K n)
    (hboundary : ∀ g x,
      booleanBoundaryMap (β (MvPolynomial.rename (ρ g) x)) =
        booleanBoundaryMap (booleanVertexRelabelEquiv (ρ g) (β x)))
    (hfixed : ∀ g x,
      primeFixedFaceQuotient p K (β (MvPolynomial.rename (ρ g) x)) =
        primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (ρ g) (β x))) :
    ∃ F : MvPolynomial (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
        BooleanBarycentricRing (ZMod p × W) K,
      (∀ n x, x ∈ polynomialDegreePiece n → F x ∈ PrimeBooleanDegreePiece p K n) ∧
      (∀ x, booleanBoundaryMap (F x) = booleanBoundaryMap (β x)) ∧
      (∀ x, primeFixedFaceQuotient p K (F x) = primeFixedFaceQuotient p K (β x)) ∧
      (∀ g x, F (MvPolynomial.rename (ρ g) x) = booleanVertexRelabelEquiv (ρ g) (F x)) := by
  let s := polynomialScalarGradedBasis L
  let σ : CyclicRepresentation (PrimePowerParameterRing (W := W) p K) G
      (MvPolynomial (ZMod p × W) K) := polynomialParameterPermutationRepresentation.comp ρ
  let τ := primeBooleanParameterRepresentation p K ρ
  let υ := primeControlledParameterRepresentation p K ρ hρ
  let H := primeControlledParameterKernel (W := W) p K
  let T := PrimeBooleanDegreePiece (W := W) p K
  let a := H.mkQ.comp β
  have hs (n : ℕ) : s.piece n = polynomialDegreePiece n :=
    polynomialScalarGradedBasis_piece_eq L hL n
  have hσ : ∀ g n x, x ∈ s.piece n → σ g x ∈ s.piece n := by
    intro g n x hx
    rw [hs] at hx ⊢
    exact polynomialRename_degree (ρ g) n x hx
  have ha : RepresentationIntertwines σ υ a := by
    intro g x
    change H.mkQ (β (MvPolynomial.rename (ρ g) x)) =
      H.mkQ (booleanVertexRelabelEquiv (ρ g) (β x))
    exact (primeControlledParameterQuotient_eq_iff p K _ _).mpr ⟨hboundary g x, hfixed g x⟩
  let b : ∀ n, s.piece n →ₗ[K] T n := fun n =>
    LinearMap.codRestrict (T n) ((β.restrictScalars K).comp (s.piece n).subtype)
      (fun x => hβ n x.val (by simpa only [hs n] using x.property))
  have hqb : ∀ n, (ScalarGradedBasis.integralDegreeQuotient T H.mkQ n).comp (b n) =
      s.integralDegreeTarget a n := by intro n; rfl
  have hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j) := by
    intro j y hy
    apply (hL _ _).mpr
    rw [map_smul]
    change polynomialColorMap (MvPolynomial.monomial j.2 1) * L y ∈
      polynomialDegreePiece (colorOrdinaryDegree j.2 + colorOrdinaryDegree (descentColorExponent j.1))
    exact polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree j.2)
      ((hL _ y).mp hy)
  choose J e he using primeControlledParameterDegree_isCoinduced p K ρ hρ hG Z hZ htranslations
  let C : ℕ → Type _ := fun n => J n → K
  letI : ∀ n, AddCommGroup (C n) := fun _ => inferInstance
  letI : ∀ n, Module K (C n) := fun _ => inferInstance
  obtain ⟨F, hFg, hFq, hFe⟩ := s.exists_integralEquivariantGradedLift_of_split_ordinary_lifts
    σ τ υ T H.mkQ a hσ (primeBooleanParameterRepresentation_degree p K ρ)
    (primeControlledParameterQuotient_intertwines p K ρ hρ) hmult ha C b hqb
    (primeControlledParameterDegreeRetraction p K) (primeControlledParameterDegreeRetraction_retract p K)
    e he
  have hvalues (x : MvPolynomial (ZMod p × W) K) :
      booleanBoundaryMap (F x) = booleanBoundaryMap (β x) ∧
        primeFixedFaceQuotient p K (F x) = primeFixedFaceQuotient p K (β x) := by
    apply (primeControlledParameterQuotient_eq_iff p K _ _).mp
    exact LinearMap.congr_fun hFq x
  refine ⟨F, ?_, fun x => (hvalues x).1, fun x => (hvalues x).2, hFe⟩
  intro n x hx
  exact hFg n x (by simpa only [hs n] using hx)

/-- When the ordinary lift is normalized and agrees with an actual ordinary
comparison on the boundary, the constructed integral lift is an isomorphism. -/
theorem exists_primePower_controlled_local_equiv
    (L : BooleanBarycentricRing (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
      MvPolynomial (ZMod p × W) K)
    (hL : ∀ n x, x ∈ PrimeBooleanDegreePiece p K n ↔ L x ∈ polynomialDegreePiece n)
    (β : MvPolynomial (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
      BooleanBarycentricRing (ZMod p × W) K)
    (hβ : ∀ n x, x ∈ polynomialDegreePiece n → β x ∈ PrimeBooleanDegreePiece p K n)
    (hβone : β 1 = 1)
    (hβL : ∀ x, booleanBoundaryMap (β (L x)) = booleanBoundaryMap x)
    (hboundary : ∀ g x,
      booleanBoundaryMap (β (MvPolynomial.rename (ρ g) x)) =
        booleanBoundaryMap (booleanVertexRelabelEquiv (ρ g) (β x)))
    (hfixed : ∀ g x,
      primeFixedFaceQuotient p K (β (MvPolynomial.rename (ρ g) x)) =
        primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (ρ g) (β x))) :
    ∃ F : MvPolynomial (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
        BooleanBarycentricRing (ZMod p × W) K,
      (∀ n x, x ∈ polynomialDegreePiece n → F x ∈ PrimeBooleanDegreePiece p K n) ∧
      F 1 = 1 ∧
      (∀ x, booleanBoundaryMap (F x) = booleanBoundaryMap (β x)) ∧
      (∀ x, primeFixedFaceQuotient p K (F x) = primeFixedFaceQuotient p K (β x)) ∧
      (∀ g x, F (MvPolynomial.rename (ρ g) x) = booleanVertexRelabelEquiv (ρ g) (F x)) := by
  obtain ⟨F, hFg, hFb, hFπ, hFe⟩ := exists_primePower_controlled_parameter_lift
    p K ρ hρ hG Z hZ htranslations L hL β hβ hboundary hfixed
  have hbij : Function.Bijective F := reverseParameterLift_bijective_of_same_boundary
    (L.restrictScalars K) (fun a x => L.map_smul a x) (fun n x hx => (hL n x).mp hx)
    (F.restrictScalars K) (fun a x => F.map_smul a x) hFg
    (fun x => (hFb (L x)).trans (hβL x))
  have hone : F 1 = 1 := by
    let y := F 1 - β 1
    have hy : y ∈ PrimeBooleanDegreePiece (W := W) p K 0 :=
      (PrimeBooleanDegreePiece p K 0).sub_mem
        (hFg 0 1 polynomialDegreePiece_one) (hβ 0 1 polynomialDegreePiece_one)
    have hk : (⟨y, hy⟩ : PrimeBooleanDegreePiece (W := W) p K 0) ∈
        LinearMap.ker (primeControlledParameterDegreeMap p K 0) := by
      rw [primeControlledParameterDegreeKernel_eq]
      change booleanBoundaryMap (F 1 - β 1) = 0 ∧
        primeFixedFaceQuotient p K (F 1 - β 1) = 0
      rw [map_sub, map_sub, hFb, hFπ, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
    have hz := primeControlledParameterDegree_zero_below p K 0
      (Fintype.card_pos : 0 < Fintype.card (ZMod p × W)) ⟨⟨y, hy⟩, hk⟩
    have hzero : F 1 - β 1 = 0 := congrArg (fun z => z.val.val) hz
    exact (sub_eq_zero.mp hzero).trans hβone
  exact ⟨LinearEquiv.ofBijective F hbij, hFg, hone, hFb, hFπ, hFe⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarIdealAssembly.lean -/
section

section
/-! # Exact scalar ideal and cohomology from the actual factorial family

These final algebraic steps use a genuine invariant element of the comparison
module, with its scalar equation exposed. The construction of that element is
kept separate from the ideal equality and from the actual `H¹` consequence.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.Universal.ScalarFamilies
open Classical
universe u

section Simplex
variable {V K : Type u} [Fintype V] [CommRing K]
variable (K)

/-- The zero- and one-vertex cases require no averaging. -/
theorem exists_factorial_scalar_family_of_card_le_one
    (hd : Fintype.card V ≤ 1) :
    ∃ F : comparisonModule (P := Finset V) K,
      (∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F) ∧
        scalar K F = ((Fintype.card V - 1).factorial : K) := by
  letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hd
  let F := normalizedComparisonFamily K (simplex_isSimplicialPoset (V := V))
  refine ⟨F, ?_, ?_⟩
  · intro σ
    have hσ : σ = Equiv.refl V := by
      ext v
      exact Subsingleton.elim _ _
    rw [hσ, finsetOrderCongr_refl]
    apply Subtype.ext
    exact relabel_refl K F.val
  · have h : Fintype.card V - 1 = 0 := by omega
    simpa only [h, Nat.factorial_zero, Nat.cast_one] using
      normalizedComparisonFamily_scalar K (simplex_isSimplicialPoset (V := V))

/-- Necessity and one actual factorial-scalar witness give the exact ideal. -/
theorem simplex_invariantScalarIdeal_eq_of_family
    (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hscalar : scalar K F = ((Fintype.card V - 1).factorial : K)) :
    invariantScalarIdeal K (fun σ : Equiv.Perm V => finsetOrderCongr σ) simplexOrderAction_one simplexOrderAction_mul =
      Ideal.span {((Fintype.card V - 1).factorial : K)} := by
  apply le_antisymm
  · intro c hc
    obtain ⟨T, hT, hTc⟩ := (scalar_mem_invariantIdeal_iff K (fun σ : Equiv.Perm V => finsetOrderCongr σ)
      simplexOrderAction_one simplexOrderAction_mul c).mp hc
    apply Ideal.mem_span_singleton.mpr
    rw [← hTc]
    exact scalar_factorial_dvd T hT
  · apply Ideal.span_le.mpr
    intro c hc
    obtain rfl := Set.mem_singleton_iff.mp hc
    exact (scalar_mem_invariantIdeal_iff K (fun σ : Equiv.Perm V => finsetOrderCongr σ)
      simplexOrderAction_one simplexOrderAction_mul _).mpr ⟨F, hF, hscalar⟩

/-- The quotient is the actual cyclic submodule generated by the comparison
class in Mathlib group cohomology. -/
def simplex_obstructionSpanEquiv_of_family
    (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hscalar : scalar K F = ((Fintype.card V - 1).factorial : K)) :
    (K ⧸ Ideal.span {((Fintype.card V - 1).factorial : K)}) ≃ₗ[K]
      Submodule.span K {(comparisonObstruction K (simplex_isSimplicialPoset (V := V))
        (fun σ : Equiv.Perm V => finsetOrderCongr σ) simplexOrderAction_one simplexOrderAction_mul)} :=
  (Submodule.quotEquivOfEq _ _
    (simplex_invariantScalarIdeal_eq_of_family K F hF hscalar).symm).trans
      (comparisonObstructionSpanEquiv K (simplex_isSimplicialPoset (V := V))
        (fun σ : Equiv.Perm V => finsetOrderCongr σ) simplexOrderAction_one simplexOrderAction_mul)

end Simplex

section Universal
variable {P V K G : Type u} [PartialOrder P] [OrderBot P] [Fintype P]
  [Fintype V] [CommRing K] [Group G]
variable (K) (hs : IsSimplicialPoset P)
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

/-- One symmetric simplex family works for every simplicial poset of the rank
bound and every group of automorphisms, with no finiteness assumption on G. -/
theorem factorial_annihilates_of_simplexFamily
    (F : comparisonModule (P := Finset V) K)
    (hF : ∀ σ : Equiv.Perm V, relabelComparison K (finsetOrderCongr σ) F = F)
    (hscalar : scalar K F = ((Fintype.card V - 1).factorial : K))
    (hP : ∀ p : P, faceRank p ≤ Fintype.card V) :
    ((Fintype.card V - 1).factorial : K) •
      comparisonObstruction K hs act h₁ hmul = 0 := by
  have h := invariantFamily_annihilates K hs act h₁ hmul
    (transportedFamily F hF hP)
    (fun g => transportedFamily_fixed F hF hP (act g))
  rw [transportedFamily_scalar, hscalar] at h
  exact h

end Universal
end FourPapers.Universal.ScalarFamilies

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerOrdinaryPrescription.lean -/
section


section

/-! # Simultaneous ordinary lifting of the actual quotient prescription

The fixed-face prescription is the composite of the integral moment map
with the previously constructed comparison on the orbit simplex. Its
parameter linearity follows from the exact elementary-parameter identities.
Actual homogeneous corrections on the full parameter basis enforce this
prescription without changing any proper boundary value.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical MvPolynomial
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime]
variable {W : Type*} [Fintype W] [Nonempty W]
variable (K : Type*) [CommRing K]

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : LinearOrder (ZMod p × W) := primePowerVertexOrder p

/-- The target scalar action is the actual composite π∘θ. -/
theorem primeFixedMomentPrescription_parameter
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (hψ : ∀ r x, ψ (MvPolynomial.esymm W K (r+1) * x) = booleanRankParameter (r+1) * ψ x) :
    IsParameterLinear polynomialColorMap
      ((primeFixedFaceQuotient p K).comp booleanColorMap)
      (ψ.comp (primeOrbitMomentRetraction p K)) := by
  apply (isParameterLinear_iff_X _ _ _).mpr
  intro i x
  change ψ (primeOrbitMomentRetraction p K (polynomialColorMap (X i) * x)) =
    primeFixedFaceQuotient p K (booleanColorMap (X i)) * ψ (primeOrbitMomentRetraction p K x)
  simp only [polynomialColorMap, booleanColorMap, MvPolynomial.aeval_X]
  rw [← booleanRankParameter_color, primeOrbitMomentRetraction_parameter,
    primeFixedFaceQuotient_parameter]
  by_cases hi : p ∣ i.val + 1
  · rw [if_pos hi, if_pos hi]
    have hpos : 0 < (i.val + 1) / p :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hi) (Fact.out : p.Prime).pos
    have hidx : ((i.val + 1) / p - 1) + 1 = (i.val + 1) / p :=
      Nat.sub_add_cancel hpos
    simpa only [hidx] using hψ (((i.val + 1) / p) - 1) (primeOrbitMomentRetraction p K x)
  · rw [if_neg hi, if_neg hi, map_zero, zero_mul]

/-- The degree-zero top-boundary map is injective over every coefficient ring. -/
theorem booleanDegreeZero_boundary_injective
    (x y : BooleanBarycentricRing (ZMod p × W) K)
    (hx : x ∈ PrimeBooleanDegreePiece p K 0) (hy : y ∈ PrimeBooleanDegreePiece p K 0)
    (hxy : booleanBoundaryMap x = booleanBoundaryMap y) : x = y := by
  have hb : booleanBoundaryMap (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (booleanBoundaryMap_eq_zero_iff (x-y)).mp hb
  have hzero : z = 0 := booleanTopOrdinary_homogeneous_zero_below 0
    (Fintype.card_pos : 0 < Fintype.card (ZMod p × W)) z
    (by rw [hz]; exact (PrimeBooleanDegreePiece p K 0).sub_mem hx hy)
  apply sub_eq_zero.mp
  rw [← hz, hzero, mul_zero]

/-- Full ordinary simultaneous extension. The boundary hypothesis is exactly
the discrepancy equation derived from proper-face coherence, not an assumed
existence of the desired lift. -/
theorem exists_primePower_ordinary_prescribed_lift
    (L : BooleanBarycentricRing (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
      MvPolynomial (ZMod p × W) K)
    (hL : ∀ n x, x ∈ PrimeBooleanDegreePiece p K n ↔ L x ∈ polynomialDegreePiece n)
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (hψp : ∀ r x, ψ (MvPolynomial.esymm W K (r+1) * x) = booleanRankParameter (r+1) * ψ x)
    (hψg : ∀ n x, x ∈ polynomialDegreePiece n → ψ x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n)
    (hboundary : ∀ x, booleanBoundaryMap
      (ψ (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (L.symm x)) = 0) :
    ∃ β : MvPolynomial (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
        BooleanBarycentricRing (ZMod p × W) K,
      (∀ n x, x ∈ polynomialDegreePiece n → β x ∈ PrimeBooleanDegreePiece p K n) ∧
      (∀ x, booleanBoundaryMap (β x) = booleanBoundaryMap (L.symm x)) ∧
      (∀ x, primeFixedFaceQuotient p K (β x) = ψ (primeOrbitMomentRetraction p K x)) ∧
      β 1 = L.symm 1 := by
  let s := polynomialScalarGradedBasis L
  let T := PrimeBooleanDegreePiece (W := W) p K
  have hs (n : ℕ) : s.piece n = polynomialDegreePiece n :=
    polynomialScalarGradedBasis_piece_eq L hL n
  have hLg : ∀ n x, x ∈ polynomialDegreePiece n → L.symm x ∈ T n := by
    intro n x hx
    apply (hL n (L.symm x)).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hx
  let bφ : PrimePowerParameterRing (W := W) p K →ₐ[K] BooleanBoundaryRing (ZMod p × W) K :=
    booleanBoundaryMap.comp booleanColorMap
  let qφ : PrimePowerParameterRing (W := W) p K →ₐ[K] BooleanBarycentricRing W K :=
    (primeFixedFaceQuotient p K).comp booleanColorMap
  letI : Algebra (PrimePowerParameterRing (W := W) p K) (BooleanBoundaryRing (ZMod p × W) K) :=
    bφ.toRingHom.toAlgebra
  letI : Algebra (PrimePowerParameterRing (W := W) p K) (BooleanBarycentricRing W K) :=
    qφ.toRingHom.toAlgebra
  let b : BooleanBarycentricRing (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
      BooleanBoundaryRing (ZMod p × W) K := {
    toFun := booleanBoundaryMap
    map_add' := map_add booleanBoundaryMap
    map_smul' := by
      intro a x
      change booleanBoundaryMap (booleanColorMap a * x) =
        booleanBoundaryMap (booleanColorMap a) * booleanBoundaryMap x
      exact map_mul booleanBoundaryMap _ _ }
  let q : BooleanBarycentricRing (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
      BooleanBarycentricRing W K := {
    toFun := primeFixedFaceQuotient p K
    map_add' := map_add (primeFixedFaceQuotient p K)
    map_smul' := by
      intro a x
      change primeFixedFaceQuotient p K (booleanColorMap a * x) =
        primeFixedFaceQuotient p K (booleanColorMap a) * primeFixedFaceQuotient p K x
      exact map_mul (primeFixedFaceQuotient p K) _ _ }
  let a : MvPolynomial (ZMod p × W) K →ₗ[PrimePowerParameterRing (W := W) p K]
      BooleanBarycentricRing W K := {
    toFun := fun x => ψ (primeOrbitMomentRetraction p K x)
    map_add' := (ψ.comp (primeOrbitMomentRetraction p K)).map_add
    map_smul' := primeFixedMomentPrescription_parameter p K ψ hψp }
  have hmult : ∀ j y, y ∈ T (s.generatorDegree (s.parent j)) →
      s.multiplier j • y ∈ T (s.degree j) := by
    intro j y hy
    apply (hL _ _).mpr
    rw [map_smul]
    change polynomialColorMap (MvPolynomial.monomial j.2 1) * L y ∈
      polynomialDegreePiece (colorOrdinaryDegree j.2 + colorOrdinaryDegree (descentColorExponent j.1))
    exact polynomialDegreePiece_mul _ _ _ _ (polynomialColorMap_monomial_degree j.2)
      ((hL _ y).mp hy)
  have hc : ∀ i, ∃ y : BooleanBarycentricRing (ZMod p × W) K,
      y ∈ T (s.generatorDegree i) ∧ b y = 0 ∧
        q y = a (s.parameterBasis i) - q (L.symm (s.parameterBasis i)) := by
    intro i
    have hx : s.parameterBasis i ∈ polynomialDegreePiece (s.generatorDegree i) := by
      simpa only [hs] using s.generator_mem_piece i
    exact exists_fixedFace_boundary_correction p K (s.generatorDegree i)
      (ψ (primeOrbitMomentRetraction p K (s.parameterBasis i)) -
        primeFixedFaceQuotient p K (L.symm (s.parameterBasis i)))
      (hboundary (s.parameterBasis i))
      (primeFixedFace_discrepancy_degree p K (L.symm.restrictScalars K).toLinearMap ψ
        hLg hψg _ _ hx)
      (primeFixedFace_discrepancy_zero_of_degree_not_dvd p K
        (L.symm.restrictScalars K).toLinearMap ψ hLg _ _ hx)
  obtain ⟨β, hβg, hβb, hβq⟩ := s.exists_graded_boundary_quotient_lift T hmult b q
    L.symm.toLinearMap a (fun n x hx => hLg n x (by simpa only [hs n] using hx)) hc
  have hgrade : ∀ n x, x ∈ polynomialDegreePiece n → β x ∈ T n := by
    intro n x hx
    exact hβg n x (by simpa only [hs n] using hx)
  have hb (x) : booleanBoundaryMap (β x) = booleanBoundaryMap (L.symm x) :=
    LinearMap.congr_fun hβb x
  refine ⟨β, hgrade, hb, fun x => LinearMap.congr_fun hβq x, ?_⟩
  exact booleanDegreeZero_boundary_injective p K (β 1) (L.symm 1)
    (hgrade 0 1 polynomialDegreePiece_one) (hLg 0 1 polynomialDegreePiece_one) (hb 1)

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStableFaceStalks.lean -/
section

section
/-! # Moment and fixed-face maps on the original simplex stalks

The maps below start and finish in the paper's actual stalk rings.  Their
coordinates are the proved atom equivalences of full-orbit faces.  The
restriction and action squares therefore retain the original simplicial
face maps, including the empty face.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial

section RenameSquare
variable {A B C D K : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [CommRing K]

/-- The forward direction of the verified inverse-coordinate restriction square. -/
theorem primeOrbit_polynomialRenameRestrictionSquare
    (i : A ↪ B) (j : C ↪ D) (e : A ≃ C) (g : B ≃ D)
    (h : i.trans g.toEmbedding = e.toEmbedding.trans j) (f : MvPolynomial B K) :
    rename e (killCompl i.injective f) = killCompl j.injective (rename g f) := by
  have hi := ScalarFamilies.inverseEmbeddingSquare i j e g h
  have hh := ScalarFamilies.killComplRenameSquare j i e.symm g.symm hi f
  simpa only [Equiv.symm_symm] using hh.symm

end RenameSquare

variable (p : ℕ) [Fact p.Prime] {W : Type*} [Fintype W]
variable (K : Type*) [CommRing K]
local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _

/-- The integral moment map on the actual polynomial stalk of a stable face. -/
def primeOrbitStalkMoment (S : Finset W) :
    PolynomialStalk K (primeOrbitFace p S) →ₗ[K] PolynomialStalk K S :=
  (primeOrbitMomentRetraction p K).comp
    (MvPolynomial.rename (primeOrbitFaceVertexEquiv p S)).toLinearMap

@[simp] theorem primeOrbitStalkMoment_apply (S : Finset W)
    (f : PolynomialStalk K (primeOrbitFace p S)) :
    primeOrbitStalkMoment p K S f =
      primeOrbitMomentRetraction p K (MvPolynomial.rename (primeOrbitFaceVertexEquiv p S) f) := rfl

/-- The fixed-face quotient on the actual barycentric stalk of a stable face. -/
def primeOrbitStalkQuotient (S : Finset W) :
    BarycentricStalk K (primeOrbitFace p S) →ₐ[K] BarycentricStalk K S :=
  (primeFixedFaceQuotient p K).comp
    (booleanVertexRelabelEquiv (primeOrbitFaceVertexEquiv p S)).toAlgHom

@[simp] theorem primeOrbitStalkQuotient_apply (S : Finset W)
    (x : BarycentricStalk K (primeOrbitFace p S)) :
    primeOrbitStalkQuotient p K S x =
      primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (primeOrbitFaceVertexEquiv p S) x) := rfl

@[simp] theorem primeOrbitStalkMoment_one (S : Finset W) : primeOrbitStalkMoment p K S 1 = 1 := by
  rw [primeOrbitStalkMoment_apply, map_one, primeOrbitMomentRetraction_one]

theorem primeOrbitStalkMoment_parameter (S : Finset W) (i : ℕ)
    (f : PolynomialStalk K (primeOrbitFace p S)) :
    primeOrbitStalkMoment p K S (polynomialParameter K (primeOrbitFace p S) i * f) =
      if p ∣ i then polynomialParameter K S (i / p) * primeOrbitStalkMoment p K S f else 0 := by
  rw [primeOrbitStalkMoment_apply, map_mul, polynomialParameter, MvPolynomial.rename_esymm,
    primeOrbitMomentRetraction_parameter]
  rfl

theorem primeOrbitStalkQuotient_parameter (S : Finset W) (i : ℕ) :
    primeOrbitStalkQuotient p K S
      (booleanRankParameter (V := FaceVertex (primeOrbitFace p S)) (K := K) i) =
      if p ∣ i then booleanRankParameter (V := FaceVertex S) (K := K) (i / p) else 0 := by
  rw [primeOrbitStalkQuotient_apply, booleanVertexRelabelEquiv_parameter,
    primeFixedFaceQuotient_parameter]

theorem primeOrbitStalkMoment_degree (S : Finset W) (n : ℕ)
    (f : PolynomialStalk K (primeOrbitFace p S)) (hf : f ∈ polynomialDegreePiece n) :
    primeOrbitStalkMoment p K S f ∈ polynomialDegreePiece (n / p) :=
  primeOrbitMomentRetraction_mem_polynomialDegreePiece p K n _
    (polynomialRename_degree (primeOrbitFaceVertexEquiv p S) n f hf)

theorem primeOrbitStalkMoment_zero_of_degree_not_dvd (S : Finset W) (n : ℕ)
    (f : PolynomialStalk K (primeOrbitFace p S)) (hf : f ∈ polynomialDegreePiece n)
    (hn : ¬ p ∣ n) : primeOrbitStalkMoment p K S f = 0 :=
  primeOrbitMomentRetraction_zero_of_polynomialDegree_not_dvd p K n _
    (polynomialRename_degree (primeOrbitFaceVertexEquiv p S) n f hf) hn

theorem primeOrbitStalkQuotient_degree (S : Finset W) (n : ℕ)
    (x : BarycentricStalk K (primeOrbitFace p S))
    (hx : x ∈ basisOrdinaryDegreePiece
      (booleanChainBasis (V := FaceVertex (primeOrbitFace p S)) (K := K))
      (fun a => booleanOrdinaryDegree a.val) n) :
    primeOrbitStalkQuotient p K S x ∈ basisOrdinaryDegreePiece
      (booleanChainBasis (V := FaceVertex S) (K := K))
      (fun a => booleanOrdinaryDegree a.val) (n / p) :=
  primeFixedFaceQuotient_degree p K n _
    (booleanVertexRelabelEquiv_degree (primeOrbitFaceVertexEquiv p S) n x hx)

/-- The polynomial square uses the original face restrictions on both sides. -/
theorem primeOrbitStalkMoment_restriction {S T : Finset W} (h : S ⊆ T)
    (f : PolynomialStalk K (primeOrbitFace p T)) :
    primeOrbitStalkMoment p K S
        (polynomialRestriction K ((primeOrbitFace_subset_iff p S T).mpr h) f) =
      polynomialRestriction K h (primeOrbitStalkMoment p K T f) := by
  rw [primeOrbitStalkMoment_apply, primeOrbitStalkMoment_apply,
    polynomialRestriction_eq_killCompl, polynomialRestriction_eq_killCompl]
  rw [primeOrbit_polynomialRenameRestrictionSquare
    (faceVertexInclusion ((primeOrbitFace_subset_iff p S T).mpr h))
    (primeOrbitEmbedding p (faceVertexInclusion h))
    (primeOrbitFaceVertexEquiv p S) (primeOrbitFaceVertexEquiv p T)
    (primeOrbitFaceVertexEquiv_inclusion_square p h), primeOrbitMomentRetraction_restriction]

/-- The barycentric square also uses the original face restrictions. -/
theorem primeOrbitStalkQuotient_restriction {S T : Finset W} (h : S ⊆ T)
    (x : BarycentricStalk K (primeOrbitFace p T)) :
    primeOrbitStalkQuotient p K S
        (booleanRestriction (faceVertexInclusion ((primeOrbitFace_subset_iff p S T).mpr h)) x) =
      booleanRestriction (faceVertexInclusion h) (primeOrbitStalkQuotient p K T x) := by
  rw [primeOrbitStalkQuotient_apply, primeOrbitStalkQuotient_apply,
    ScalarFamilies.booleanRestrictionRelabelSquare
      (faceVertexInclusion ((primeOrbitFace_subset_iff p S T).mpr h))
      (primeOrbitEmbedding p (faceVertexInclusion h))
      (primeOrbitFaceVertexEquiv p S) (primeOrbitFaceVertexEquiv p T)
      (primeOrbitFaceVertexEquiv_inclusion_square p h), primeFixedFaceQuotient_restriction]

section Relabeling
variable (σ : Equiv.Perm W) (g : W → ZMod p)

theorem primeOrbitStalkMoment_relabel (S : Finset W)
    (f : PolynomialStalk K (primeOrbitFace p S)) :
    primeOrbitStalkMoment p K (finsetOrderCongr σ S)
        (MvPolynomial.rename (primeOrbitFaceStalkRelabel p σ g S) f) =
      polynomialStalkOrderEquiv K (finsetOrderCongr σ) S (primeOrbitStalkMoment p K S f) := by
  rw [primeOrbitStalkMoment_apply, primeOrbitStalkMoment_apply]
  have hr : MvPolynomial.rename (primeOrbitFaceVertexEquiv p (finsetOrderCongr σ S))
        (MvPolynomial.rename (primeOrbitFaceStalkRelabel p σ g S) f) =
      MvPolynomial.rename
        (primeOrbitRelabel p (faceVertexOrderEquiv (finsetOrderCongr σ) S)
          (fun a => g (simplexVertexEquiv S a).val))
        (MvPolynomial.rename (primeOrbitFaceVertexEquiv p S) f) := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
    apply congrArg (fun h : FaceVertex (primeOrbitFace p S) →
      (ZMod p × FaceVertex (finsetOrderCongr σ S)) => MvPolynomial.rename h f)
    funext v
    exact primeOrbitFaceVertexEquiv_relabel p σ g S v
  rw [hr, primeOrbitMomentRetraction_relabel]
  rfl

theorem primeOrbitStalkQuotient_relabel (S : Finset W)
    (x : BarycentricStalk K (primeOrbitFace p S)) :
    primeOrbitStalkQuotient p K (finsetOrderCongr σ S)
        (booleanVertexRelabelEquiv (primeOrbitFaceStalkRelabel p σ g S) x) =
      barycentricStalkOrderEquiv K (finsetOrderCongr σ) S (primeOrbitStalkQuotient p K S x) := by
  rw [primeOrbitStalkQuotient_apply, primeOrbitStalkQuotient_apply]
  have hr : booleanVertexRelabelEquiv (primeOrbitFaceVertexEquiv p (finsetOrderCongr σ S))
        (booleanVertexRelabelEquiv (primeOrbitFaceStalkRelabel p σ g S) x) =
      booleanVertexRelabelEquiv
        (primeOrbitRelabel p (faceVertexOrderEquiv (finsetOrderCongr σ) S)
          (fun a => g (simplexVertexEquiv S a).val))
        (booleanVertexRelabelEquiv (primeOrbitFaceVertexEquiv p S) x) := by
    rw [← booleanVertexRelabelEquiv_trans, ← booleanVertexRelabelEquiv_trans]
    apply congrArg (fun h : FaceVertex (primeOrbitFace p S) ≃
      (ZMod p × FaceVertex (finsetOrderCongr σ S)) => booleanVertexRelabelEquiv (K := K) h x)
    apply Equiv.ext
    intro v
    exact primeOrbitFaceVertexEquiv_relabel p σ g S v
  rw [hr, primeFixedFaceQuotient_relabel]
  rfl

end Relabeling
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkFamilies.lean -/
section


section

/-! # Linear families on the actual face stalks

All family operations act on genuine Boolean and polynomial stalk maps.
Relabeling uses the inverse order automorphism at the target face, avoiding
arbitrary identifications of vertex sets.  Coherence is an actual restriction
square, and the parameter and degree conditions are the original ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FourPapers.Universal


open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

abbrev StalkLinearFamily := ∀ p : P, BarycentricStalk K p →ₗ[K] PolynomialStalk K p

structure CoherentLinearMap (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p →ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)

def CoherentLinearMap.sectionMap {D E : ModuleDiagram K P} (f : CoherentLinearMap K D E) :
    D.sections →ₗ[K] E.sections where
  toFun x := ⟨fun p => f.component p (x.val p), by
    intro p q h
    rw [f.naturality, x.property p q h]⟩
  map_add' x y := by apply Subtype.ext; funext p; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; funext p; exact map_smul _ _ _

def stalkFamilyRelabel (e : P ≃o P) :
    StalkLinearFamily (P := P) K →ₗ[K] StalkLinearFamily (P := P) K where
  toFun F p := (polynomialStalkOrderEquiv K e.symm p).symm.toLinearMap.comp
    ((F (e.symm p)).comp (barycentricStalkOrderEquiv K e.symm p).toLinearMap)
  map_add' F H := by funext p; apply LinearMap.ext; intro x; simp
  map_smul' c F := by funext p; apply LinearMap.ext; intro x; simp

@[simp] theorem stalkFamilyRelabel_apply (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (p : P) (x : BarycentricStalk K p) :
    stalkFamilyRelabel K e F p x = (polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)) := rfl

theorem polynomialStalkOrderEquiv_trans_symm (e f : P ≃o P) (p : P)
    (x : PolynomialStalk K ((e.trans f) p)) :
    (polynomialStalkOrderEquiv K (e.trans f) p).symm x =
      (polynomialStalkOrderEquiv K e p).symm
        ((polynomialStalkOrderEquiv K f (e p)).symm x) := by
  apply (polynomialStalkOrderEquiv K (e.trans f) p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_trans,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

@[simp] theorem stalkFamilyRelabel_refl (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (OrderIso.refl P) F = F := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (OrderIso.refl P) p).symm
    (F p (barycentricStalkOrderEquiv K (OrderIso.refl P) p x)) = F p x
  apply (polynomialStalkOrderEquiv K (OrderIso.refl P) p).injective
  rw [AlgEquiv.apply_symm_apply, barycentricStalkOrderEquiv_refl,
    polynomialStalkOrderEquiv_refl]

theorem stalkFamilyRelabel_trans (e f : P ≃o P) (F : StalkLinearFamily (P := P) K) :
    stalkFamilyRelabel K (e.trans f) F = stalkFamilyRelabel K f (stalkFamilyRelabel K e F) := by
  funext p
  apply LinearMap.ext
  intro x
  change (polynomialStalkOrderEquiv K (f.symm.trans e.symm) p).symm
      (F (e.symm (f.symm p)) (barycentricStalkOrderEquiv K (f.symm.trans e.symm) p x)) = _
  rw [polynomialStalkOrderEquiv_trans_symm, barycentricStalkOrderEquiv_trans]
  rfl

def coherentStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p q (h : q ≤ p) x,
    polynomialRestriction K h (F p x) = F q (booleanRestriction (faceVertexInclusion h) x)}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p q h x
    change polynomialRestriction K h (F p x + H p x) = _
    rw [map_add, hF, hH]
    rfl
  smul_mem' := by
    intro c F hF p q h x
    change polynomialRestriction K h (c • F p x) = _
    rw [map_smul, hF]
    rfl

def parameterStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p r x, F p (booleanRankParameter (r + 1) * x) = polynomialParameter K p (r + 1) * F p x}
  zero_mem' := by intros; simp
  add_mem' := by
    intro F H hF hH p r x
    change F p (booleanRankParameter (r + 1) * x) + H p (booleanRankParameter (r + 1) * x) =
      polynomialParameter K p (r + 1) * (F p x + H p x)
    rw [hF, hH, mul_add]
  smul_mem' := by
    intro c F hF p r x
    change c • F p _ = polynomialParameter K p (r + 1) * (c • F p x)
    rw [hF, mul_smul_comm]

def gradedStalkFamilySubmodule : Submodule K (StalkLinearFamily (P := P) K) where
  carrier := {F | ∀ p n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n → F p x ∈ polynomialDegreePiece n}
  zero_mem' := by intro p n x hx; exact (polynomialDegreePiece n).zero_mem
  add_mem' := by intro F H hF hH p n x hx; exact (polynomialDegreePiece n).add_mem (hF p n x hx) (hH p n x hx)
  smul_mem' := by intro c F hF p n x hx; exact (polynomialDegreePiece n).smul_mem c (hF p n x hx)

def coherentGradedParameterStalkFamilies : Submodule K (StalkLinearFamily (P := P) K) :=
  coherentStalkFamilySubmodule K ⊓ (parameterStalkFamilySubmodule K ⊓ gradedStalkFamilySubmodule K)

theorem polynomialStalkOrderEquiv_symm_parameter (e : P ≃o P) (p : P) (r : ℕ) :
    (polynomialStalkOrderEquiv K e p).symm (polynomialParameter K (e p) r) =
      polynomialParameter K p r := by
  apply (polynomialStalkOrderEquiv K e p).injective
  rw [AlgEquiv.apply_symm_apply, polynomialStalkOrderEquiv_parameter]

theorem polynomialStalkOrderEquiv_symm_degree (e : P ≃o P) (p : P) (n : ℕ)
    (x : PolynomialStalk K (e p)) (hx : x ∈ polynomialDegreePiece n) :
    (polynomialStalkOrderEquiv K e p).symm x ∈ polynomialDegreePiece n :=
  polynomialRename_degree (faceVertexOrderEquiv e p).symm n x hx

theorem stalkFamilyRelabel_parameter (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ parameterStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ parameterStalkFamilySubmodule K := by
  intro p r x
  rw [stalkFamilyRelabel_apply, map_mul, barycentricStalkOrderEquiv_parameter,
    hF, map_mul, polynomialStalkOrderEquiv_symm_parameter]
  rfl

theorem stalkFamilyRelabel_graded (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ gradedStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ gradedStalkFamilySubmodule K := by
  intro p n x hx
  exact polynomialStalkOrderEquiv_symm_degree K e.symm p n _
    (hF (e.symm p) n _ (barycentricStalkOrderEquiv_degree K e.symm p n x hx))

theorem stalkFamilyRelabel_coherent (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (hF : F ∈ coherentStalkFamilySubmodule K) :
    stalkFamilyRelabel K e F ∈ coherentStalkFamilySubmodule K := by
  intro p q h x
  apply (polynomialStalkOrderEquiv K e.symm q).injective
  have hn := polynomialStalkOrderEquiv_restriction K e.symm h
    ((polynomialStalkOrderEquiv K e.symm p).symm
      (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))
  change polynomialStalkOrderEquiv K e.symm q
      (polynomialRestriction K h ((polynomialStalkOrderEquiv K e.symm p).symm
        (F (e.symm p) (barycentricStalkOrderEquiv K e.symm p x)))) =
    polynomialStalkOrderEquiv K e.symm q
      ((polynomialStalkOrderEquiv K e.symm q).symm
        (F (e.symm q) (barycentricStalkOrderEquiv K e.symm q
          (booleanRestriction (faceVertexInclusion h) x))))
  rw [← hn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hF,
    barycentricStalkOrderEquiv_restriction]

theorem stalkFamilyRelabel_normalized (e : P ≃o P) (F : StalkLinearFamily (P := P) K)
    (c : K) (hF : ∀ p, F p 1 = MvPolynomial.C c) :
    ∀ p, stalkFamilyRelabel K e F p 1 = MvPolynomial.C c := by
  intro p
  rw [stalkFamilyRelabel_apply, map_one, hF]
  exact (polynomialStalkOrderEquiv K e.symm p).symm.commutes c

section Action
variable {G : Type*} [Group G]
variable (act : G → P ≃o P)
  (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))

def stalkFamilyRepresentation : CyclicRepresentation K G (StalkLinearFamily (P := P) K) where
  toFun g := stalkFamilyRelabel K (act g)
  map_one' := by
    apply LinearMap.ext
    intro F
    rw [h₁, stalkFamilyRelabel_refl]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    rw [hmul, stalkFamilyRelabel_trans]
    rfl

def representationMulAction {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : CyclicRepresentation A G M) : MulAction G M where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [ρ.map_one]; rfl
  mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); rw [ρ.map_mul]; rfl

end Action
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicBoundaryIsomorphism.lean -/
section

section
/-! # Positive-degree boundary lifting without a previously known isomorphism

This is the graded lifting argument of Lemma 2.1.  The boundary comparison
is an actual isomorphism of the two top-parameter quotients.  Strong induction
on ordinary degree proves injectivity and surjectivity of any graded lift
commuting with the top parameters.  It neither compares the lift with an
already invertible map nor assumes a prescribed leading coefficient matrix.
-/
noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

section GradedLinearAlgebra

variable {K M N I J : Type*} [CommRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem ordinaryBasis_mem_piece (b : Module.Basis I K M) (w : I → ℕ) (i : I) :
    b i ∈ basisOrdinaryDegreePiece b w (w i) := by
  intro j hj
  by_cases h : i = j
  · subst j
    exact (hj rfl).elim
  · simp only [Module.Basis.repr_self, Finsupp.single_apply, if_neg h]

theorem ordinaryProjection_mem_piece (b : Module.Basis I K M) (w : I → ℕ)
    (n : ℕ) (x : M) :
    basisDegreeProjection b w n x ∈ basisOrdinaryDegreePiece b w n := by
  intro i hi
  rw [basisDegreeProjection_repr, if_neg hi]

theorem ordinaryProjection_natural (b : Module.Basis I K M) (c : Module.Basis J K N)
    (w : I → ℕ) (v : J → ℕ) (f : M →ₗ[K] N)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n) (n : ℕ) (x : M) :
    basisDegreeProjection c v n (f x) = f (basisDegreeProjection b w n x) := by
  have he : (basisDegreeProjection c v n).comp f = f.comp (basisDegreeProjection b w n) := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, basisDegreeProjection_basis]
    by_cases hi : w i = n
    · rw [if_pos hi]
      exact (basisDegreeProjection_eq_self_iff_mem c v n (f (b i))).mpr
        (hf n (b i) (hi ▸ ordinaryBasis_mem_piece b w i))
    · rw [if_neg hi, map_zero]
      apply c.repr.injective
      ext j
      rw [basisDegreeProjection_repr, map_zero, Finsupp.zero_apply]
      by_cases hj : v j = n
      · rw [if_pos hj]
        exact hf (w i) (b i) (ordinaryBasis_mem_piece b w i) j
          (fun h => hi (h.symm.trans hj))
      · rw [if_neg hj]
  exact LinearMap.congr_fun he x

variable {Q R : Type*} [AddCommGroup Q] [Module K Q]
  [AddCommGroup R] [Module K R]

/-- A degree-preserving top-parameter lift of an actual boundary isomorphism
is bijective.  All kernel and predecessor hypotheses refer to the given maps
and the given basis degrees; they do not assert any isomorphism of the lifts. -/
theorem gradedBoundaryLift_bijective
    (b : Module.Basis I K M) (c : Module.Basis J K N) (w : I → ℕ) (v : J → ℕ)
    (qM : M →ₗ[K] Q) (qN : N →ₗ[K] R) (boundary : Q ≃ₗ[K] R)
    (σ : M →ₗ[K] M) (τ : N →ₗ[K] N) (r : ℕ) (hr : 0 < r)
    (hτ : Function.Injective τ)
    (hkerM : ∀ x, qM x = 0 → ∃ a, σ a = x)
    (hkerN : ∀ y, qN y = 0 → ∃ a, τ a = y)
    (hσpred : ∀ n a, r ≤ n → σ a ∈ basisOrdinaryDegreePiece b w n →
      a ∈ basisOrdinaryDegreePiece b w (n - r))
    (hτpred : ∀ n a, r ≤ n → τ a ∈ basisOrdinaryDegreePiece c v n →
      a ∈ basisOrdinaryDegreePiece c v (n - r))
    (hσbelow : ∀ n a, n < r → σ a ∈ basisOrdinaryDegreePiece b w n → a = 0)
    (hτbelow : ∀ n a, n < r → τ a ∈ basisOrdinaryDegreePiece c v n → a = 0)
    (hboundary : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n →
      ∃ x, x ∈ basisOrdinaryDegreePiece b w n ∧ qN y = boundary (qM x))
    (f : M →ₗ[K] N)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n →
      f x ∈ basisOrdinaryDegreePiece c v n)
    (htop : ∀ x, f (σ x) = τ (f x))
    (hquot : ∀ x, qN (f x) = boundary (qM x)) : Function.Bijective f := by
  have hinj : ∀ n x, x ∈ basisOrdinaryDegreePiece b w n → f x = 0 → x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hx hfx
        have hqx : qM x = 0 := by
          apply boundary.injective
          rw [← hquot, hfx, map_zero, map_zero]
        obtain ⟨a, ha⟩ := hkerM x hqx
        have hσa : σ a ∈ basisOrdinaryDegreePiece b w n := ha.symm ▸ hx
        by_cases hrn : r ≤ n
        · have hfa : f a = 0 := by
            apply hτ
            rw [← htop, ha, hfx, map_zero]
          have ha0 := ih (n - r) (by omega) a (hσpred n a hrn hσa) hfa
          rw [← ha, ha0, map_zero]
        · have ha0 := hσbelow n a (Nat.lt_of_not_ge hrn) hσa
          rw [← ha, ha0, map_zero]
  have hsurj : ∀ n y, y ∈ basisOrdinaryDegreePiece c v n → ∃ x, f x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hy
        obtain ⟨x, hx, hbx⟩ := hboundary n y hy
        have hqdiff : qN (y - f x) = 0 := by rw [map_sub, hquot, hbx, sub_self]
        obtain ⟨a, ha⟩ := hkerN (y - f x) hqdiff
        have hτa : τ a ∈ basisOrdinaryDegreePiece c v n :=
          ha.symm ▸ (basisOrdinaryDegreePiece c v n).sub_mem hy (hgrade n x hx)
        by_cases hrn : r ≤ n
        · obtain ⟨z, hz⟩ := ih (n - r) (by omega) a (hτpred n a hrn hτa)
          refine ⟨x + σ z, ?_⟩
          rw [map_add, htop, hz, ha]
          abel
        · have ha0 := hτbelow n a (Nat.lt_of_not_ge hrn) hτa
          refine ⟨x, ?_⟩
          have hh : y - f x = 0 := by rw [← ha, ha0, map_zero]
          exact (sub_eq_zero.mp hh).symm
  have hzero : ∀ x, f x = 0 → x = 0 := by
    intro x hfx
    apply b.repr.injective
    ext i
    have hh : basisDegreeProjection b w (w i) x = 0 := by
      apply hinj (w i) _ (ordinaryProjection_mem_piece b w (w i) x)
      rw [← ordinaryProjection_natural b c w v f hgrade, hfx, map_zero]
    have hc := congrArg (fun z => b.repr z i) hh
    simpa only [basisDegreeProjection_repr, if_true, map_zero, Finsupp.zero_apply] using hc
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro y
    choose a ha using fun j : J => hsurj (v j) (c j) (ordinaryBasis_mem_piece c v j)
    refine ⟨∑ j ∈ (c.repr y).support, c.repr y j • a j, ?_⟩
    simp only [map_sum, map_smul, ha]
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using c.linearCombination_repr y

end GradedLinearAlgebra

section BooleanBoundary

variable {V K : Type*} [Fintype V] [LinearOrder V] [Nonempty V] [CommRing K]

/-- The actual degree piece in the Boolean top-parameter quotient. -/
def booleanBoundaryOrdinaryPiece (n : ℕ) : Submodule K (BooleanBoundaryRing V K) :=
  (basisOrdinaryDegreePiece booleanChainBasis (fun a => chainOrdinaryDegree a.val) n).map
    booleanBoundaryMap.toLinearMap

/-- The actual degree piece in the polynomial top-monomial quotient. -/
def polynomialBoundaryOrdinaryPiece (n : ℕ) : Submodule K (PolynomialBoundaryRing V K) :=
  (polynomialDegreePiece n).map polynomialBooleanBoundaryMap.toLinearMap

theorem polynomialOrdinaryPiece_eq_basis (n : ℕ) :
    polynomialDegreePiece (V := V) (K := K) n =
      basisOrdinaryDegreePiece (MvPolynomial.basisMonomials V K)
        (fun a => vertexDegree (fun v => a v)) n := by
  ext x
  rfl

theorem fullPolynomialTop_predecessor_degree (m : ℕ) (f : MvPolynomial V K)
    (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece (m + Fintype.card V)) :
    f ∈ polynomialDegreePiece m := by
  intro a ha
  have hdeg : vertexDegree (fun v => (fullExponent V + a) v) =
      Fintype.card V + vertexDegree (fun v => a v) := by
    change vertexDegree ((fun v => fullExponent V v) + (fun v => a v)) = _
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by rw [hdeg]; omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem fullPolynomialTop_zero_below (n : ℕ) (hn : n < Fintype.card V)
    (f : MvPolynomial V K) (hf : (∏ v : V, X v) * f ∈ polynomialDegreePiece n) : f = 0 := by
  ext a
  have hdeg : Fintype.card V ≤ vertexDegree (fun v => (fullExponent V + a) v) := by
    change Fintype.card V ≤ vertexDegree ((fun v => fullExponent V v) + (fun v => a v))
    rw [vertexDegree_add]
    simp [vertexDegree]
  have hh := hf (fullExponent V + a) (by omega)
  rw [← full_monomial_eq_prod, MvPolynomial.coeff_monomial_mul, one_mul] at hh
  exact hh

theorem parameterLinear_top
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (x : BooleanBarycentricRing V K) :
    f (booleanTop * x) = (∏ v : V, X v) * f x := by
  have hr : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hc : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have h := parameterLinear_intertwinesAllRanks f hf (Fintype.card V - 1) x
  have htop : MvPolynomial.esymm V K (Fintype.card V) = ∏ v : V, X v := by
    unfold MvPolynomial.esymm
    rw [← Finset.card_univ, Finset.powersetCard_self]
    simp
  simpa only [hc, booleanRankParameter_top, htop] using h

/-- Lemma 2.1 on the actual simplex rings.  The inverse boundary map is
assumed graded in the genuine quotient grading, as it is for any graded
boundary isomorphism.  No isomorphism of the full rings is assumed. -/
theorem booleanPolynomialLift_bijective_of_graded_boundary
    (boundary : LocalBoundaryComparison (V := V) (K := K))
    (hbgrade : ∀ n y, y ∈ polynomialBoundaryOrdinaryPiece (V := V) (K := K) n →
      boundary.toLinearEquiv.symm y ∈ booleanBoundaryOrdinaryPiece (V := V) (K := K) n)
    (f : BooleanBarycentricRing V K →ₗ[K] MvPolynomial V K)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => chainOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hquot : ∀ x, polynomialBooleanBoundaryMap (f x) =
      boundary.toLinearEquiv (booleanBoundaryMap x)) : Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis (MvPolynomial.basisMonomials V K)
    (fun a => chainOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    booleanBoundaryMap.toLinearMap polynomialBooleanBoundaryMap.toLinearMap boundary.toLinearEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (∏ v : V, X v)) (Fintype.card V)
    (Fintype.card_pos_iff.mpr inferInstance)
    (MvPolynomial.isRegular_prod_X (R := K) (Finset.univ : Finset V)).left
    (fun x hx => (booleanBoundaryMap_eq_zero_iff x).mp hx)
    (fun y hy => (polynomialBooleanBoundaryMap_eq_zero_iff y).mp hy)
    (fun n a hn ha => booleanTop_predecessor_degree (n - Fintype.card V) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card V) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => booleanTop_homogeneous_zero_below n hn a ha)
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by rwa [← polynomialOrdinaryPiece_eq_basis] at ha))
    ?_ f ?_ (parameterLinear_top f hf) hquot
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    have hb := hbgrade n (polynomialBooleanBoundaryMap y) ⟨y, hy', rfl⟩
    obtain ⟨x, hx, he⟩ := hb
    refine ⟨x, hx, ?_⟩
    change polynomialBooleanBoundaryMap y =
      boundary.toLinearEquiv (booleanBoundaryMap x)
    have hh := congrArg boundary.toLinearEquiv he
    simpa only [LinearEquiv.apply_symm_apply, AlgHom.toLinearMap_apply] using hh.symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx

end BooleanBoundary
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicCoherentBoundaryLift.lean -/
section

section
/-! # Ordinary graded extensions of coherent boundary maps

The input is a coherent family of actual linear maps, without any assumption
of invertibility.  The correction uses the established section of the genuine
proper-face restriction map.  Extending its values on the actual descent
basis gives a parameter-linear map with the prescribed restrictions.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

def linearCoherentBoundaryCorrection (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p :=
  (polynomialCarrierBoundaryExtension K hs p).comp
    ((e.sectionMap K).comp (stalkBoundaryRestriction (barycentricDiagram K) p))

theorem linearCoherentBoundaryCorrection_restrict (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p
      (linearCoherentBoundaryCorrection K hs p e x) =
      e.sectionMap K (stalkBoundaryRestriction (barycentricDiagram K) p x) :=
  polynomialCarrierBoundaryExtension_restrict K hs p _

theorem linearCoherentBoundaryCorrection_coefficient (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) (x : BarycentricStalk K p)
    (b : StandardFaceIndex P) :
    (polynomialStandardCoordinates K hs p (linearCoherentBoundaryCorrection K hs p e x)).val b =
      if hb : standardCarrier b < p then
        (polynomialStandardCoordinates K hs (standardCarrier b)
          (e.component ⟨standardCarrier b, hb⟩
            (booleanRestriction (faceVertexInclusion hb.le) x))).val b else 0 := by
  unfold linearCoherentBoundaryCorrection polynomialCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem linearCoherentBoundaryCorrection_standard_degree (p : P)
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentBoundaryCorrection K hs p e) := by
  intro a b hab
  rw [linearCoherentBoundaryCorrection_coefficient]
  by_cases hb : standardCarrier b < p
  · rw [dif_pos hb]
    have hres := barycentricStandardCoordinates_naturality K hs hb.le
      (barycentricStalkStandardBasis K hs p a)
    rw [barycentricStandardCoordinates_basis, coefficientRestriction_unit] at hres
    by_cases ha : standardCarrier a.val ≤ standardCarrier b
    · rw [dif_pos ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) =
            barycentricStalkStandardBasis K hs (standardCarrier b) ⟨a.val, ha⟩ := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, barycentricStandardCoordinates_basis]
      rw [hval]
      exact he ⟨standardCarrier b, hb⟩ ⟨a.val, ha⟩ b hab
    · rw [dif_neg ha] at hres
      have hval : booleanRestriction (K := K) (faceVertexInclusion hb.le)
          (barycentricStalkStandardBasis K hs p a) = 0 := by
        apply (barycentricStandardCoordinates K hs (standardCarrier b)).injective
        rw [← hres, map_zero]
      rw [hval, map_zero, map_zero]
      rfl
  · rw [dif_neg hb]

variable (p : P) [LinearOrder (FaceVertex p)]

def linearCoherentLocalExtension
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    BarycentricStalk K p →ₗ[K] PolynomialStalk K p := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  exact ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))).restrictScalars K

@[simp] theorem linearCoherentLocalExtension_basis
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) =
      linearCoherentBoundaryCorrection K hs p e (descentVector σ) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  change ((booleanColorBasis (V := FaceVertex p) (K := K)).constr
    (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
    (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ))) (descentVector σ) = _
  simpa only [booleanColorBasis_apply] using
    (Module.Basis.constr_basis (booleanColorBasis (V := FaceVertex p) (K := K))
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun τ => linearCoherentBoundaryCorrection K hs p e (descentVector τ)) σ)

theorem linearCoherentLocalExtension_parameter_mul
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IsParameterLinear booleanColorMap polynomialColorMap (linearCoherentLocalExtension K hs p e) := by
  letI := (polynomialColorMap (V := FaceVertex p) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (PolynomialStalk K p) :=
    IsScalarTower.of_algHom (polynomialColorMap (V := FaceVertex p) (K := K))
  let f :=
    (booleanColorBasis (V := FaceVertex p) (K := K)).constr
      (MvPolynomial (Fin (Fintype.card (FaceVertex p))) K)
      (fun σ => linearCoherentBoundaryCorrection K hs p e (descentVector σ))
  intro a x
  change f (booleanColorMap a * x) = polynomialColorMap a * f x
  exact f.map_smul a x

theorem linearCoherentLocalExtension_intertwinesAllRanks
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p))) :
    IntertwinesAllRanks (linearCoherentLocalExtension K hs p e) :=
  parameterLinear_intertwinesAllRanks _ (linearCoherentLocalExtension_parameter_mul K hs p e)

set_option backward.isDefEq.respectTransparency false in
theorem linearCoherentLocalExtension_naturality
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q ((booleanRankParameter (V := FaceVertex q.val) (K := K) (i + 1)) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (q : Set.Iio p) (x : BarycentricStalk K p) :
    polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x) := by
  let F : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (polynomialRestriction K q.property.le).toLinearMap.comp (linearCoherentLocalExtension K hs p e)
  let G : BarycentricStalk K p →ₗ[K] PolynomialStalk K q.val :=
    (e.component q).comp
      (booleanRestriction (K := K) (faceVertexInclusion q.property.le)).toLinearMap
  have hF : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change polynomialRestriction K q.property.le
      (linearCoherentLocalExtension K hs p e (booleanColorMap (X c) * z)) = _
    erw [linearCoherentLocalExtension_parameter_mul K hs p e, map_mul]
    rw [polynomialColorMap, MvPolynomial.aeval_X,
      polynomialParameterMap, MvPolynomial.aeval_X]
    change polynomialRestriction K q.property.le
      (esymm (FaceVertex p) K (c.val + 1)) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z) =
      esymm (FaceVertex q.val) K (c.val + 1) *
      polynomialRestriction K q.property.le (linearCoherentLocalExtension K hs p e z)
    congr 1
    exact polynomialRestriction_parameter K q.property.le (c.val + 1)
  have hG : IsParameterLinear booleanColorMap
      (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) G := by
    apply (isParameterLinear_iff_X _ _ _).mpr
    intro c z
    change e.component q (booleanRestriction (faceVertexInclusion q.property.le)
      (booleanColorMap (X c) * z)) = _
    erw [map_mul]
    have hb : booleanRestriction (K := K) (faceVertexInclusion q.property.le)
        (booleanColorMap (X c)) = booleanRankParameter (c.val + 1) := by
      have hc : booleanColorMap (K := K) (X c) = colorSum c := by
        rw [booleanColorMap, MvPolynomial.aeval_X]
        rfl
      have hcol := hc.trans (booleanRankParameter_color (K := K) c).symm
      exact (congrArg (booleanRestriction (K := K) (faceVertexInclusion q.property.le)) hcol).trans
        (booleanRestriction_rankParameter (K := K) (faceVertexInclusion q.property.le) (c.val + 1))
    erw [hb]
    rw [polynomialParameterMap, MvPolynomial.aeval_X]
    change e.component q (booleanRankParameter (c.val + 1) *
      booleanRestriction (faceVertexInclusion q.property.le) z) =
      polynomialParameter K q.val (c.val + 1) *
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) z)
    exact he q c.val (booleanRestriction (faceVertexInclusion q.property.le) z)
  have hfg : F = G := parameterLinear_ext_descent
    (polynomialParameterMap K (Fintype.card (FaceVertex p)) q.val) F G hF hG (by
      intro σ
      change polynomialRestriction K q.property.le
        (linearCoherentLocalExtension K hs p e (descentVector σ)) = _
      rw [linearCoherentLocalExtension_basis]
      have h := congrArg (fun y : ((polynomialDiagram K).restrict (Set.Iio p)).sections => y.val q)
        (linearCoherentBoundaryCorrection_restrict K hs p e (descentVector σ))
      exact h)
  exact DFunLike.congr_fun hfg x

variable {p}

theorem linearCoherentLocalExtension_descent_degree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (σ : VertexOrdering (Fintype.card (FaceVertex p)) (FaceVertex p)) :
    linearCoherentLocalExtension K hs p e (descentVector σ) ∈
      polynomialDegreePiece (colorOrdinaryDegree (descentColorExponent σ)) := by
  intro b hb
  let a := descentChainIndex σ
  let c : BooleanChainExponent (FaceVertex p) := chainVertexEquiv.symm b
  have hcb : chainVertexMap c.val = b := chainVertexEquiv.apply_symm_apply b
  have hne : standardOrdinaryDegree ((standardInsideEquiv hs p) c).val ≠
      standardOrdinaryDegree ((standardInsideEquiv hs p) a).val := by
    erw [standardOrdinaryDegree_inside, standardOrdinaryDegree_inside, descentChainIndex_degree,
      ← vertexDegree_eq_chainOrdinaryDegree, hcb]
    exact hb
  have h := linearCoherentBoundaryCorrection_standard_degree K hs p e he
    ((standardInsideEquiv hs p) a) ((standardInsideEquiv hs p) c).val hne
  erw [barycentricStalkStandardBasis_local, ← descentVector_eq_chainBasis,
    polynomialStandardCoordinates_chain, hcb] at h
  change (linearCoherentLocalExtension K hs p e (descentVector σ)).coeff b = 0
  rw [linearCoherentLocalExtension_basis]
  exact h

theorem linearCoherentLocalExtension_hasStandardDegree (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q)) :
    HasStandardDegree K hs p (linearCoherentLocalExtension K hs p e) := by
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := parameterLinear_chain_degree (linearCoherentLocalExtension K hs p e)
      (linearCoherentLocalExtension_parameter_mul K hs p e)
      (linearCoherentLocalExtension_descent_degree K hs p e he) u (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p
      (linearCoherentLocalExtension K hs p e (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p
        (linearCoherentLocalExtension K hs p e (barycentricStalkStandardBasis K hs p a))).property b hb

theorem linearCoherentLocalExtension_graded (p : P) [LinearOrder (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (n : ℕ) (x : BarycentricStalk K p)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    linearCoherentLocalExtension K hs p e x ∈ polynomialDegreePiece n :=
  parameterLinear_ordinary_degree _ (linearCoherentLocalExtension_parameter_mul K hs p e)
    (linearCoherentLocalExtension_descent_degree K hs p e he) n x hx

theorem hasStandardDegree_of_ordinary_degree (p : P)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) :
    HasStandardDegree K hs p f := by
  letI : LinearOrder (FaceVertex p) :=
    LinearOrder.lift' (Fintype.equivFin (FaceVertex p)) (Fintype.equivFin (FaceVertex p)).injective
  intro a b hab
  by_cases hb : standardCarrier b ≤ p
  · let u : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm a
    let v : BooleanChainExponent (FaceVertex p) := (standardInsideEquiv hs p).symm ⟨b, hb⟩
    have hu : (standardInsideEquiv hs p) u = a := (standardInsideEquiv hs p).apply_symm_apply a
    have hv : (standardInsideEquiv hs p) v = ⟨b, hb⟩ :=
      (standardInsideEquiv hs p).apply_symm_apply ⟨b, hb⟩
    have hdeg : vertexDegree (fun w => chainVertexMap v.val w) ≠ chainOrdinaryDegree u.val := by
      rw [vertexDegree_eq_chainOrdinaryDegree,
        ← standardOrdinaryDegree_inside hs p u, ← standardOrdinaryDegree_inside hs p v, hu, hv]
      exact hab
    have h := hf (chainOrdinaryDegree u.val) (booleanChainBasis u)
      (ordinaryBasis_mem_piece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) u)
      (chainVertexMap v.val) hdeg
    have hcoord := polynomialStandardCoordinates_chain K hs p (f (booleanChainBasis u)) v
    rw [hv] at hcoord
    have hsource : barycentricStalkStandardBasis K hs p a = booleanChainBasis u :=
      hu ▸ barycentricStalkStandardBasis_local K hs p u
    rw [hsource]
    exact hcoord.trans h
  · exact (Finsupp.mem_supported' K _).mp
      (polynomialStandardCoordinates K hs p (f (barycentricStalkStandardBasis K hs p a))).property b hb

theorem polynomialDegreePiece_zero_eq_C {V : Type*} [Fintype V]
    (f : MvPolynomial V K) (hf : f ∈ polynomialDegreePiece 0) : f = MvPolynomial.C (f.coeff 0) := by
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  · rw [MvPolynomial.coeff_C_of_ne_zero ha]
    apply hf a
    intro hd
    apply ha
    ext v
    have hv : a v ≤ vertexDegree (fun w => a w) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    change a v = 0
    omega

/-- The ordinary extension has the same constant normalization as all its
proper-face components.  Positive rank supplies the proper bottom face. -/
theorem linearCoherentLocalExtension_normalized (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q))
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    linearCoherentLocalExtension K hs p e 1 = 1 := by
  let σ := weightOrdering (fun _ : FaceVertex p => 0)
  have hdes : descentVector (K := K) σ = 1 := by
    simp [descentVector, σ, weightOrdering_zero_no_descents]
  have hdeg : colorOrdinaryDegree (descentColorExponent σ) = 0 := by
    rw [descentOrdinaryDegree_eq_zero_iff]
    exact weightOrdering_zero_no_descents
  have hdegree := linearCoherentLocalExtension_descent_degree K hs p e hegrade σ
  rw [hdes, hdeg] at hdegree
  have hC := polynomialDegreePiece_zero_eq_C K _ hdegree
  have hp : (⊥ : P) < p := by
    have hr : 0 < faceRank p := by
      rw [← card_faceVertex p]
      exact Fintype.card_pos
    apply bot_lt_iff_ne_bot.mpr
    intro he
    rw [he, faceRank_bot] at hr
    exact (Nat.lt_irrefl 0) hr
  let q : Set.Iio p := ⟨⊥, hp⟩
  have hn := linearCoherentLocalExtension_naturality K hs p e heparam q 1
  rw [hC] at hn
  simp only [polynomialRestriction_C, map_one, heone] at hn
  have hc' : (linearCoherentLocalExtension K hs p e 1).coeff 0 = 1 := by
    apply MvPolynomial.C_injective (FaceVertex (⊥ : P)) K
    exact hn.trans (MvPolynomial.C_1).symm
  rw [hC, hc', MvPolynomial.C_1]

include hs in
/-- A normalized graded parameter-linear extension of an arbitrary coherent
normalized graded boundary family.  This is the actual local choice needed
for the orbit induction; no boundary invertibility is assumed. -/
theorem exists_linearCoherentLocalExtension (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    ∃ f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p,
      IsParameterLinear booleanColorMap polynomialColorMap f ∧
      (∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
        e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) ∧
      (∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n) ∧ f 1 = 1 := by
  have hd : ∀ q : Set.Iio p, HasStandardDegree K hs q.val (e.component q) :=
    fun q => hasStandardDegree_of_ordinary_degree K hs q.val (e.component q) (hegrade q)
  exact ⟨linearCoherentLocalExtension K hs p e,
    linearCoherentLocalExtension_parameter_mul K hs p e,
    linearCoherentLocalExtension_naturality K hs p e heparam,
    linearCoherentLocalExtension_graded K hs p e hd,
    linearCoherentLocalExtension_normalized K hs p e heparam hd heone⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/SupportCarrier.lean -/
section

section

/-! # The unique supporting face of a polynomial monomial inside a Boolean interval -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The vertices occurring with positive exponent. -/
def exponentVertices {p : P} (a : FaceVertex p →₀ ℕ) : Finset P :=
  a.support.image Subtype.val

theorem exponentVertices_subset {p : P} (a : FaceVertex p →₀ ℕ) :
    exponentVertices a ⊆ faceVertices p := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  exact mem_faceVertices.mpr w.property

/-- The carrier is chosen inside the fixed Boolean interval; distinct global
faces with identical vertices are never identified. -/
def exponentCarrier (hs : IsSimplicialPoset P) {p : P} (a : FaceVertex p →₀ ℕ) : P :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).val

theorem exponentCarrier_le (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a ≤ p :=
  ((existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose).property

@[simp] theorem exponentCarrier_vertices (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : faceVertices (exponentCarrier hs a) = exponentVertices a :=
  (existsUnique_subface hs p (exponentVertices a) (exponentVertices_subset a)).choose_spec.1

theorem exponentCarrier_le_iff (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    exponentCarrier hs a ≤ q ↔ ∀ v ∈ a.support, v.val ≤ q := by
  rw [← faceVertices_subset_iff hs (exponentCarrier_le hs a) hqp,
    exponentCarrier_vertices]
  constructor
  · intro h v hv
    exact (mem_faceVertices.mp (h (Finset.mem_image.mpr ⟨v, hv, rfl⟩))).2
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact mem_faceVertices.mpr ⟨w.property.1, h w hw⟩

theorem exponentCarrier_eq_top_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a = p ↔ a.support = univ := by
  constructor
  · intro h
    have hv : exponentVertices a = faceVertices p := by rw [← exponentCarrier_vertices hs a, h]
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hm : v.val ∈ exponentVertices a := hv ▸ mem_faceVertices.mpr v.property
    obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hm
    have he : w = v := Subtype.ext hEq
    exact he ▸ hw
  · intro h
    apply faceVertices_injective_below hs (exponentCarrier_le hs a) le_rfl
    rw [exponentCarrier_vertices]
    ext v
    simp only [exponentVertices, h, Finset.mem_image, mem_univ, true_and, mem_faceVertices]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩

theorem exponentCarrier_lt_iff (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) : exponentCarrier hs a < p ↔ a.support ≠ univ := by
  rw [lt_iff_le_and_ne]
  simp only [exponentCarrier_le, true_and]
  exact not_congr (exponentCarrier_eq_top_iff hs a)

/-- Pull an exponent vector back along a genuine face inclusion. -/
def restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ) :
    FaceVertex q →₀ ℕ :=
  Finsupp.comapDomain (faceVertexInclusion hqp) a (faceVertexInclusion hqp).injective.injOn

@[simp] theorem restrictExponent_apply {p q : P} (hqp : q ≤ p)
    (a : FaceVertex p →₀ ℕ) (v : FaceVertex q) :
    restrictExponent hqp a v = a (faceVertexInclusion hqp v) := rfl

theorem extend_restrictExponent {p q : P} (hqp : q ≤ p) (a : FaceVertex p →₀ ℕ)
    (ha : ∀ v ∈ a.support, v.val ≤ q) :
    (restrictExponent hqp a).mapDomain (faceVertexInclusion hqp) = a := by
  apply Finsupp.mapDomain_comapDomain _ (faceVertexInclusion hqp).injective a
  intro v hv
  refine ⟨⟨v.val, v.property.1, ha v hv⟩, ?_⟩
  exact Subtype.ext rfl

theorem extend_restrictExponent_carrier (hs : IsSimplicialPoset P) {p : P}
    (a : FaceVertex p →₀ ℕ) :
    (restrictExponent (exponentCarrier_le hs a) a).mapDomain
      (faceVertexInclusion (exponentCarrier_le hs a)) = a := by
  apply extend_restrictExponent
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs a) a).mp le_rfl

theorem exponentCarrier_extend_le (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) ≤ q := by
  apply (exponentCarrier_le_iff hs hqp _).mpr
  intro v hv
  have hsupp := Finsupp.mapDomain_support (f := faceVertexInclusion hqp) (s := a)
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hsupp hv)
  exact w.property.2

/-- Pullback after extension is compatible with nested actual face inclusions. -/
theorem restrictExponent_extend_of_le {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q)
    (a : FaceVertex q →₀ ℕ) :
    restrictExponent (hrq.trans hqp) (a.mapDomain (faceVertexInclusion hqp)) =
      restrictExponent hrq a := by
  ext v
  change (a.mapDomain (faceVertexInclusion hqp))
      (faceVertexInclusion hqp (faceVertexInclusion hrq v)) =
    a (faceVertexInclusion hrq v)
  exact Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective a _

theorem support_le_exponentCarrier_extend (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q ≤ p) (a : FaceVertex q →₀ ℕ) :
    ∀ v ∈ a.support, v.val ≤ exponentCarrier hs (a.mapDomain (faceVertexInclusion hqp)) := by
  intro v hv
  let b := a.mapDomain (faceVertexInclusion hqp)
  have hbv : faceVertexInclusion hqp v ∈ b.support := by
    rw [Finsupp.mem_support_iff]
    simpa only [b, Finsupp.mapDomain_apply_of_injective (faceVertexInclusion hqp).injective]
      using Finsupp.mem_support_iff.mp hv
  exact (exponentCarrier_le_iff hs (exponentCarrier_le hs b) b).mp le_rfl
    (faceVertexInclusion hqp v) hbv

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicStalkBoundary.lean -/
section

section
/-! # The actual proper-face boundary and graded lifting

These maps are restriction to the inverse limit of all proper faces.  Their
kernels are exactly multiplication by the top rank parameter.  The Boolean
boundary has an explicit graded section, obtained in the already established
standard monomial coordinates.  Thus the positive-degree lifting argument
applies directly to coherent maps of actual stalk diagrams.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical Finset MvPolynomial
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

include hs in
theorem polynomialStalkBoundary_eq_zero_iff (p : P) (f : PolynomialStalk K p) :
    stalkBoundaryRestriction (polynomialDiagram K) p f = 0 ↔
      ∃ g : PolynomialStalk K p, polynomialTop K p * g = f := by
  constructor
  · intro hf
    have hm : f ∈ Ideal.span {∏ v : FaceVertex p, (X v : PolynomialStalk K p)} := by
      apply (mem_full_product_ideal_iff (FaceVertex p) K f).mpr
      intro a ha
      have hq : exponentCarrier hs a < p := (exponentCarrier_lt_iff hs a).mpr ha
      have hres := congrArg (fun x => x.val ⟨exponentCarrier hs a, hq⟩) hf
      change polynomialRestriction K hq.le f = 0 at hres
      have hc := congrArg (fun z : PolynomialStalk K (exponentCarrier hs a) =>
        z.coeff (restrictExponent (exponentCarrier_le hs a) a)) hres
      rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl,
        extend_restrictExponent_carrier hs a, MvPolynomial.coeff_zero] at hc
      exact hc
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hm
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    funext q
    change polynomialRestriction K q.property.le (polynomialTop K p * g) = 0
    rw [map_mul, polynomialRestriction_top K hs q.property, zero_mul]

theorem booleanChainCarrier_lt_of_top_zero (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanChainExponent (FaceVertex p)) (ha : a.val booleanTopFace = 0) :
    standardCarrier ((standardInsideEquiv hs p) a).val < p := by
  let b := ((standardInsideEquiv hs p) a).val
  have hproper : ∀ F ∈ b.val.support, faceRank F.val < faceRank p := by
    intro F hF
    change F ∈ (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).support at hF
    rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hF
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hF
    have hGt : G.val ≠ Finset.univ := by
      intro h
      have he : G = booleanTopFace := Subtype.ext h
      subst G
      exact Finsupp.mem_support_iff.mp hG ha
    rw [faceRank_booleanFaceInclusion, ← card_faceVertex p]
    simpa only [Finset.card_univ] using
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hGt)
  have hr : faceRank (standardCarrier b) < faceRank p := by
    rcases standardCarrier_mem_or_bot b with h | ⟨F, hF, he⟩
    · rw [h, faceRank_bot, ← card_faceVertex p]
      exact Fintype.card_pos
    · rw [he]
      exact hproper F hF
  apply lt_of_le_of_ne ((standardInsideEquiv hs p) a).property
  intro he
  exact (ne_of_lt hr) (congrArg faceRank he)

theorem barycentricStalkBoundary_coefficient_zero (p : P) (x : BarycentricStalk K p)
    (hx : stalkBoundaryRestriction (barycentricDiagram K) p x = 0)
    (a : StandardFaceIndex P) (ha : standardCarrier a < p) :
    (barycentricStandardCoordinates K hs p x).val a = 0 := by
  have hres := congrArg (fun z => z.val ⟨standardCarrier a, ha⟩) hx
  change booleanRestriction (K := K) (faceVertexInclusion ha.le) x = 0 at hres
  have hc := congrArg (fun z => z.val a)
    (barycentricStandardCoordinates_naturality K hs ha.le x)
  rw [coefficientRestriction_apply, if_pos le_rfl, hres, map_zero] at hc
  exact hc

include hs in
theorem barycentricStalkBoundary_eq_zero_iff (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) :
    stalkBoundaryRestriction (barycentricDiagram K) p x = 0 ↔
      ∃ y : BarycentricStalk K p, booleanTop * y = x := by
  constructor
  · intro hx
    apply (booleanBoundaryMap_eq_zero_iff x).mp
    apply (standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr.injective
    ext a
    rw [map_zero, Finsupp.zero_apply]
    change ((standardMonomialBasis (K := K) (CoordinateBoundary IsChainExponent booleanTopFace)
      (coordinateBoundary_divisorClosed IsChainExponent isChainExponent_divisorClosed
        booleanTopFace)).repr (coordinateBoundaryMap IsChainExponent booleanTopFace x)) a = 0
    rw [coordinateBoundaryMap_coefficient]
    let c : BooleanChainExponent (FaceVertex p) := ⟨a.val, a.property.1⟩
    let b := (standardInsideEquiv hs p) c
    have hb : standardCarrier b.val < p :=
      booleanChainCarrier_lt_of_top_zero hs p c a.property.2
    have hz := barycentricStalkBoundary_coefficient_zero K hs p x hx b.val hb
    rw [barycentricStandardCoordinates_apply_of_inside K hs p x b.val b.property] at hz
    have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = c :=
      (standardInsideEquiv hs p).symm_apply_apply c
    rw [hid] at hz
    simpa only [booleanChainBasis, c] using hz
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    funext q
    have hn : ¬ Function.Surjective (faceVertexInclusion q.property.le) := by
      intro hsurj
      have hc := Fintype.card_le_of_surjective _ hsurj
      rw [card_faceVertex, card_faceVertex] at hc
      exact (not_le_of_gt (faceRank_strictMono hs q.property)) hc
    change booleanRestriction (K := K) (faceVertexInclusion q.property.le)
      (booleanTop * y) = 0
    rw [map_mul, booleanRestriction_top _ hn, zero_mul]

def barycentricCarrierBoundaryExtension (p : P) :
    ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections →ₗ[K]
      BarycentricStalk K p :=
  (barycentricStandardCoordinates K hs p).symm.toLinearMap.comp
    ((coefficientBoundaryExtension standardCarrier p).comp
      (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv.toLinearMap))

theorem barycentricCarrierBoundaryExtension_restrict (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections) :
    stalkBoundaryRestriction (barycentricDiagram K) p
      (barycentricCarrierBoundaryExtension K hs p x) = x := by
  apply (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv).injective
  rw [stalkBoundaryRestriction_naturality]
  change stalkBoundaryRestriction (coefficientDiagram K standardCarrier) p
    (barycentricStandardCoordinates K hs p
      ((barycentricStandardCoordinates K hs p).symm
        (coefficientBoundaryExtension standardCarrier p
          (((barycentricCoefficientEquiv K hs).restrict (Set.Iio p)).sectionEquiv x)))) = _
  rw [LinearEquiv.apply_symm_apply, coefficientBoundaryExtension_restrict]

theorem barycentricCarrierBoundaryExtension_coefficient (p : P)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (a : StandardFaceIndex P) :
    (barycentricStandardCoordinates K hs p (barycentricCarrierBoundaryExtension K hs p x)).val a =
      if ha : standardCarrier a < p then
        (barycentricStandardCoordinates K hs (standardCarrier a)
          (x.val ⟨standardCarrier a, ha⟩)).val a else 0 := by
  unfold barycentricCarrierBoundaryExtension
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coefficientBoundaryExtension_apply]
  rfl

theorem standardOrdinaryDegree_inside_orderFree (p : P)
    (a : BooleanChainExponent (FaceVertex p)) :
    standardOrdinaryDegree ((standardInsideEquiv hs p) a).val = booleanOrdinaryDegree a.val := by
  change (Finsupp.mapDomain (booleanFaceInclusion hs p) a.val).sum
    (fun F n => n * faceRank F.val) = _
  rw [Finsupp.sum_mapDomain_index (fun F => by simp) (fun F i j => by simp only [add_mul])]
  simp only [faceRank_booleanFaceInclusion, booleanOrdinaryDegree]

theorem barycentricCarrierBoundaryExtension_graded (p : P) (n : ℕ)
    (x : ((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections)
    (hx : ∀ q : Set.Iio p, x.val q ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    barycentricCarrierBoundaryExtension K hs p x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n := by
  intro a ha
  let b := (standardInsideEquiv hs p) a
  have hc := barycentricStandardCoordinates_apply_of_inside K hs p
    (barycentricCarrierBoundaryExtension K hs p x) b.val b.property
  have hid : (standardInsideEquiv hs p).symm ⟨b.val, b.property⟩ = a :=
    (standardInsideEquiv hs p).symm_apply_apply a
  rw [hid] at hc
  rw [← hc, barycentricCarrierBoundaryExtension_coefficient]
  split_ifs with hb
  · rw [barycentricStandardCoordinates_apply_of_inside K hs (standardCarrier b.val)
      (x.val ⟨standardCarrier b.val, hb⟩) b.val le_rfl]
    apply hx ⟨standardCarrier b.val, hb⟩
    have he := standardOrdinaryDegree_inside_orderFree hs (standardCarrier b.val)
      ((standardInsideEquiv hs (standardCarrier b.val)).symm ⟨b.val, le_rfl⟩)
    rw [Equiv.apply_symm_apply] at he
    intro hdeg
    exact ha ((standardOrdinaryDegree_inside_orderFree hs p a).symm.trans
      (he.trans hdeg))
  · rfl

theorem polynomialRestriction_degree {p q : P} (hqp : q ≤ p) (n : ℕ)
    (f : PolynomialStalk K p) (hf : f ∈ polynomialDegreePiece n) :
    polynomialRestriction K hqp f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [polynomialRestriction_eq_killCompl, MvPolynomial.coeff_killCompl]
  apply hf
  rwa [vertexDegree_mapDomain]

theorem stalkLinearEquiv_symm_graded (p : P)
    (e : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p)
    (he : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e x ∈ polynomialDegreePiece n)
    (n : ℕ) (y : PolynomialStalk K p) (hy : y ∈ polynomialDegreePiece n) :
    e.symm y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
  apply (basisDegreeProjection_eq_self_iff_mem booleanChainBasis
    (fun a => booleanOrdinaryDegree a.val) n (e.symm y)).mp
  apply e.injective
  have hg : ∀ m x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) m →
      e x ∈ basisOrdinaryDegreePiece (MvPolynomial.basisMonomials (FaceVertex p) K)
        (fun a => vertexDegree (fun v => a v)) m := by
    intro m x hx
    exact he m x hx
  have hproj := ordinaryProjection_natural booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K) (fun a => booleanOrdinaryDegree a.val)
    (fun a => vertexDegree (fun v => a v)) e.toLinearMap hg n (e.symm y)
  have hh : e (e.symm y) ∈ basisOrdinaryDegreePiece
      (MvPolynomial.basisMonomials (FaceVertex p) K)
      (fun a => vertexDegree (fun v => a v)) n := by
    intro a ha
    change (e (e.symm y)).coeff a = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hy a ha
  simpa only [LinearEquiv.coe_coe] using hproj.symm.trans
    ((basisDegreeProjection_eq_self_iff_mem _ _ _ _).mpr hh)

/-- Top multiplication in the actual stalk coordinates, with no auxiliary
vertex order in the statement or in its equality instances. -/
theorem barycentricTop_shift_coefficient (p : P) [Nonempty (FaceVertex p)]
    (x : BarycentricStalk K p) (a : BooleanChainExponent (FaceVertex p)) :
    booleanChainBasis.repr (booleanTop * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) =
      booleanChainBasis.repr x a := by
  change (standardMonomialBasis IsChainExponent isChainExponent_divisorClosed).repr
      (monomialCoordinate IsChainExponent booleanTopFace * x)
      (coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a) = _
  rw [monomialCoordinate_mul_repr]
  exact Finsupp.mapDomain_apply_of_injective
    (coordinateExponentShift_injective IsChainExponent booleanTopFace booleanTop_isFreeCoordinate) _ _

theorem barycentricTop_degree_shift (p : P) [Nonempty (FaceVertex p)]
    (a : BooleanFace (FaceVertex p) →₀ ℕ) :
    booleanOrdinaryDegree (a + Finsupp.single booleanTopFace 1) =
      booleanOrdinaryDegree a + Fintype.card (FaceVertex p) := by
  unfold booleanOrdinaryDegree
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ i j => by simp only [add_mul])]
  simp [booleanTopFace]

theorem barycentricTop_predecessor_degree (p : P) [Nonempty (FaceVertex p)]
    (m : ℕ) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) (m + Fintype.card (FaceVertex p))) :
    x ∈ basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) m := by
  intro a ha
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ m + Fintype.card (FaceVertex p) := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    exact fun he => ha (Nat.add_right_cancel he)
  have hh := hx b hb
  rwa [barycentricTop_shift_coefficient] at hh

theorem barycentricTop_homogeneous_zero_below (p : P) [Nonempty (FaceVertex p)]
    (n : ℕ) (hn : n < Fintype.card (FaceVertex p)) (x : BarycentricStalk K p)
    (hx : booleanTop * x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) : x = 0 := by
  apply booleanChainBasis.repr.injective
  ext a
  let b := coordinateExponentShift IsChainExponent booleanTopFace booleanTop_isFreeCoordinate a
  have hb : booleanOrdinaryDegree b.val ≠ n := by
    change booleanOrdinaryDegree (a.val + Finsupp.single booleanTopFace 1) ≠ _
    rw [barycentricTop_degree_shift]
    omega
  have hh := hx b hb
  rw [barycentricTop_shift_coefficient] at hh
  exact hh

include hs in
/-- The actual coherent local lifting theorem.  The boundary comparison is
the isomorphism of proper-face inverse limits induced by the already
constructed lower-face isomorphisms.  Grading of their inverses is derived
from their forward grading, and no full-stalk comparison is presupposed. -/
theorem coherentStalkLift_bijective (p : P) [LinearOrder (FaceVertex p)]
    [Nonempty (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (he : ∀ (q : Set.Iio p) n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → e.component q x ∈ polynomialDegreePiece n)
    (f : BarycentricStalk K p →ₗ[K] PolynomialStalk K p)
    (hf : IsParameterLinear booleanColorMap polynomialColorMap f)
    (hgrade : ∀ n x, x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n → f x ∈ polynomialDegreePiece n)
    (hres : ∀ (q : Set.Iio p) x, polynomialRestriction K q.property.le (f x) =
      e.component q (booleanRestriction (faceVertexInclusion q.property.le) x)) :
    Function.Bijective f := by
  apply gradedBoundaryLift_bijective booleanChainBasis
    (MvPolynomial.basisMonomials (FaceVertex p) K)
    (fun a => booleanOrdinaryDegree a.val) (fun a => vertexDegree (fun v => a v))
    (Q := ↥(((barycentricDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (R := ↥(((polynomialDiagram (P := P) K).restrict (Set.Iio p)).sections))
    (stalkBoundaryRestriction (barycentricDiagram K) p)
    (stalkBoundaryRestriction (polynomialDiagram K) p) e.sectionEquiv
    (LinearMap.mulLeft K booleanTop) (LinearMap.mulLeft K (polynomialTop K p))
    (Fintype.card (FaceVertex p)) (Fintype.card_pos_iff.mpr inferInstance)
    (polynomialTop_mul_injective K p)
    (fun x hx => (barycentricStalkBoundary_eq_zero_iff K hs p x).mp hx)
    (fun y hy => (polynomialStalkBoundary_eq_zero_iff K hs p y).mp hy)
    (fun n a hn ha => barycentricTop_predecessor_degree K p (n - Fintype.card (FaceVertex p)) a
      (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop] using ha))
    (fun n a hn ha => by
      rw [← polynomialOrdinaryPiece_eq_basis] at ha ⊢
      exact fullPolynomialTop_predecessor_degree (n - Fintype.card (FaceVertex p)) a
        (by simpa only [Nat.sub_add_cancel hn, LinearMap.mulLeft_apply,
        polynomialTop, booleanOrdinaryDegree, chainOrdinaryDegree] using ha))
    (fun n a hn ha => barycentricTop_homogeneous_zero_below K p n hn a
      (by simpa only [LinearMap.mulLeft_apply] using ha))
    (fun n a hn ha => fullPolynomialTop_zero_below n hn a
      (by simpa only [LinearMap.mulLeft_apply, polynomialTop, ← polynomialOrdinaryPiece_eq_basis] using ha))
    ?_ f ?_ (parameterLinear_top f hf) ?_
  · intro n y hy
    have hy' : y ∈ polynomialDegreePiece n := by
      rwa [← polynomialOrdinaryPiece_eq_basis] at hy
    let z := e.sectionEquiv.symm (stalkBoundaryRestriction (polynomialDiagram K) p y)
    refine ⟨barycentricCarrierBoundaryExtension K hs p z, ?_, ?_⟩
    · apply barycentricCarrierBoundaryExtension_graded
      intro q
      exact stalkLinearEquiv_symm_graded K q.val (e.component q) (he q) n
        (polynomialRestriction K q.property.le y)
        (polynomialRestriction_degree K q.property.le n y hy')
    · rw [barycentricCarrierBoundaryExtension_restrict]
      exact (e.sectionEquiv.apply_symm_apply _).symm
  · intro n x hx
    rw [← polynomialOrdinaryPiece_eq_basis]
    exact hgrade n x hx
  · intro x
    apply Subtype.ext
    funext q
    exact hres q x

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicReverseLocalExtension.lean -/
section


section

/-! # Ordinary local extension in the paper's direction

The actual normalized boundary equivalence is first extended by the verified
Boolean-to-polynomial construction. The boundary-kernel theorem proves that
this particular extension is bijective. Inverting it gives an ordinary local
polynomial-to-Boolean lift with its genuine restriction squares, parameter
identities and ordinary grading. No averaging or scalar division occurs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)

include hs in
/-- An actual reverse local equivalence extending the inverse boundary family. -/
theorem exists_reverseCoherentLocalExtension (p : P)
    [LinearOrder (FaceVertex p)] [Nonempty (FaceVertex p)]
    (e : CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)))
    (heparam : ∀ (q : Set.Iio p) (i : ℕ) (x : BarycentricStalk K q.val),
      e.component q (booleanRankParameter (i + 1) * x) =
        polynomialParameter K q.val (i + 1) * e.component q x)
    (hegrade : ∀ (q : Set.Iio p) n x,
      x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) n →
      e.component q x ∈ polynomialDegreePiece n)
    (heone : ∀ q : Set.Iio p, e.component q 1 = 1) :
    ∃ f : PolynomialStalk K p ≃ₗ[K] BarycentricStalk K p,
      IsParameterLinear polynomialColorMap booleanColorMap f.toLinearMap ∧
      (∀ (q : Set.Iio p) x,
        booleanRestriction (faceVertexInclusion q.property.le) (f x) =
          (e.component q).symm (polynomialRestriction K q.property.le x)) ∧
      (∀ n x, x ∈ polynomialDegreePiece n →
        f x ∈ basisOrdinaryDegreePiece booleanChainBasis
          (fun a => booleanOrdinaryDegree a.val) n) ∧ f 1 = 1 := by
  let E : CoherentLinearMap K ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)) := {
    component := fun q => (e.component q).toLinearMap
    naturality := e.naturality }
  obtain ⟨g, hgp, hgr, hgd, hgone⟩ := exists_linearCoherentLocalExtension K hs p E
    heparam hegrade heone
  let L : BarycentricStalk K p ≃ₗ[K] PolynomialStalk K p :=
    LinearEquiv.ofBijective g (coherentStalkLift_bijective K hs p e hegrade g hgp hgd hgr)
  refine ⟨L.symm, ?_, ?_, ?_, ?_⟩
  · intro a x
    apply L.injective
    have hh := hgp a (L.symm x)
    change L (L.symm (polynomialColorMap a * x)) = _
    rw [LinearEquiv.apply_symm_apply]
    have hcancel : g (L.symm x) = x := L.apply_symm_apply x
    exact (congrArg (fun y : PolynomialStalk K p => polynomialColorMap a * y)
      hcancel.symm).trans hh.symm
  · intro q x
    apply (e.component q).injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := hgr q (L.symm x)
    change polynomialRestriction K q.property.le (L (L.symm x)) = _ at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  · intro n x hx
    exact stalkLinearEquiv_symm_graded K p L hgd n x hx
  · apply L.injective
    change L (L.symm 1) = L 1
    rw [LinearEquiv.apply_symm_apply]
    exact hgone.symm

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/ScalarRankBoundary.lean -/
section

section
/-! # The actual lower-face boundary of a controlled rank stage

Already constructed `R → B` components are inverted only after their actual
bijectivity is known. This gives the coherent `B → R` boundary required by the
ordinary extension theorem, with parameter identities, grading and the exact
original lower-face components retained.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- Inverse grading for a genuine polynomial-to-barycentric equivalence. -/
theorem reverseStalkLinearEquiv_symm_graded (p : P)
    (e : PolynomialStalk K p ≃ₗ[K] BarycentricStalk K p)
    (he : ∀ n x, x ∈ polynomialDegreePiece n → e x ∈
      basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) n)
    (n : ℕ) (y : BarycentricStalk K p)
    (hy : y ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n) :
    e.symm y ∈ polynomialDegreePiece n := by
  apply (basisDegreeProjection_eq_self_iff_mem
    (MvPolynomial.basisMonomials (FaceVertex p) K)
    (fun a => vertexDegree (fun v => a v)) n (e.symm y)).mp
  apply e.injective
  have hg : ∀ m x, x ∈ basisOrdinaryDegreePiece
      (MvPolynomial.basisMonomials (FaceVertex p) K)
      (fun a => vertexDegree (fun v => a v)) m →
      e x ∈ basisOrdinaryDegreePiece booleanChainBasis
        (fun a => booleanOrdinaryDegree a.val) m := fun m x hx => he m x hx
  have hproj := ordinaryProjection_natural
    (MvPolynomial.basisMonomials (FaceVertex p) K) booleanChainBasis
    (fun a => vertexDegree (fun v => a v)) (fun a => booleanOrdinaryDegree a.val)
    e.toLinearMap hg n (e.symm y)
  have hh : e (e.symm y) ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n := by
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  simpa only [LinearEquiv.coe_coe] using hproj.symm.trans
    ((basisDegreeProjection_eq_self_iff_mem _ _ _ _).mpr hh)

namespace ScalarFamilies
variable (Control : ∀ p : P, (PolynomialStalk K p →ₗ[K] BarycentricStalk K p) → Prop)
variable {G : Type*} [Group G]
variable (act : G → P ≃o P) (h₁ : act 1 = OrderIso.refl P)
  (hmul : ∀ g h, act (g * h) = (act h).trans (act g))
variable (n : ℕ) (old : RankStage K Control act h₁ hmul n)

def rankStageComponent (q : equivariantRankCut (fun p : P => faceRank p) n) :
    PolynomialStalk K q.val →ₗ[K] BarycentricStalk K q.val :=
  rankStageValue K Control act h₁ hmul n old q q.val

theorem rankStageComponent_good (q : equivariantRankCut (fun p : P => faceRank p) n) :
    (∀ r x, rankStageComponent K Control act h₁ hmul n old q
      (polynomialParameter K q.val (r + 1) * x) =
      booleanRankParameter (r + 1) * rankStageComponent K Control act h₁ hmul n old q x) ∧
    (∀ j x, x ∈ polynomialDegreePiece j →
      rankStageComponent K Control act h₁ hmul n old q x ∈
        basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) j) ∧
    rankStageComponent K Control act h₁ hmul n old q 1 = 1 ∧
    Control q.val (rankStageComponent K Control act h₁ hmul n old q) := by
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  exact ⟨(old.good q).2.1 q.val, (old.good q).2.2.1 q.val,
    (old.good q).2.2.2.1, (old.good q).2.2.2.2⟩

def rankStageInverseIndex (g : G)
    (q : equivariantRankCut (fun p : P => faceRank p) n) :
    equivariantRankCut (fun p : P => faceRank p) n :=
  ⟨(act g).symm q.val, by
    change faceRank ((act g).symm q.val) < n
    rw [faceRank_eq_of_orderIso]
    exact q.property⟩

/-- Equivariance of the actual old component, expressed with the inverse
order map so that the dependent stalk types agree without any casts. -/
theorem rankStageComponent_inverse_naturality (g : G)
    (q : equivariantRankCut (fun p : P => faceRank p) n)
    (x : PolynomialStalk K q.val) :
    barycentricStalkOrderEquiv K (act g).symm q.val
      (rankStageComponent K Control act h₁ hmul n old q x) =
    rankStageComponent K Control act h₁ hmul n old (rankStageInverseIndex act n g q)
      (polynomialStalkOrderEquiv K (act g).symm q.val x) := by
  letI := orderAction act h₁ hmul
  letI := familyAction K act h₁ hmul
  let q' := rankStageInverseIndex act n g q
  have hindex : (⟨act g q'.val, by
      change faceRank (act g q'.val) < n
      rw [faceRank_eq_of_orderIso]
      exact q'.property⟩ : equivariantRankCut (fun p : P => faceRank p) n) = q := by
    apply Subtype.ext
    exact (act g).apply_symm_apply q.val
  have hv := old.equivariant g q'
  change old.value ⟨act g q'.val, _⟩ = relabel K (act g) (old.value q') at hv
  rw [hindex] at hv
  have hx := congrArg (fun F : Family (P := P) K => F q.val x) hv
  apply (barycentricStalkOrderEquiv K (act g).symm q.val).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  exact hx

variable (hbij : ∀ q f, Control q f → Function.Bijective f)

def rankStageComponentEquiv (q : equivariantRankCut (fun p : P => faceRank p) n) :
    PolynomialStalk K q.val ≃ₗ[K] BarycentricStalk K q.val :=
  LinearEquiv.ofBijective (rankStageComponent K Control act h₁ hmul n old q)
    (hbij q.val _ (rankStageComponent_good K Control act h₁ hmul n old q).2.2.2)

variable (hs : IsSimplicialPoset P) (p : P) (hp : faceRank p = n)

def rankStageLowerIndex (q : Set.Iio p) : equivariantRankCut (fun p : P => faceRank p) n :=
  ⟨q.val, by
    change faceRank q.val < n
    rw [← hp]
    exact faceRank_strictMono hs q.property⟩

def rankStageReverseBoundary :
    CoherentEquiv ((polynomialDiagram (P := P) K).restrict (Set.Iio p))
      ((barycentricDiagram K).restrict (Set.Iio p)) where
  component q := rankStageComponentEquiv K Control act h₁ hmul n old hbij
    (rankStageLowerIndex n hs p hp q)
  naturality r q h x := by
    letI := orderAction act h₁ hmul
    letI := familyAction K act h₁ hmul
    by_cases he : q = r
    · subst q
      simp only [ModuleDiagram.restrict, polynomialDiagram, barycentricDiagram,
        polynomialRestriction_refl, faceVertexInclusion_refl, booleanRestriction_refl,
        AlgHom.id_apply, AlgHom.toLinearMap_apply]
    · have hlt : q.val < r.val := lt_of_le_of_ne h (fun hh => he (Subtype.ext hh))
      exact old.compatible (rankStageLowerIndex n hs p hp r)
        (rankStageLowerIndex n hs p hp q) hlt h x

/-- The actual inverse boundary supplied to the ordinary local extension. -/
def rankStageBoundaryEquiv :
    CoherentEquiv ((barycentricDiagram (P := P) K).restrict (Set.Iio p))
      ((polynomialDiagram K).restrict (Set.Iio p)) :=
  (rankStageReverseBoundary K Control act h₁ hmul n old hbij hs p hp).symm

@[simp] theorem rankStageBoundaryEquiv_symm_apply (q : Set.Iio p)
    (x : PolynomialStalk K q.val) :
    ((rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp).component q).symm x =
      rankStageComponent K Control act h₁ hmul n old (rankStageLowerIndex n hs p hp q) x := rfl

theorem rankStageBoundaryEquiv_parameter (q : Set.Iio p) (r : ℕ)
    (x : BarycentricStalk K q.val) :
    (rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp).component q
      (booleanRankParameter (r + 1) * x) =
      polynomialParameter K q.val (r + 1) *
        (rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp).component q x := by
  let L : PolynomialStalk K q.val ≃ₗ[K] BarycentricStalk K q.val := rankStageComponentEquiv K Control act h₁ hmul n old hbij
    (rankStageLowerIndex n hs p hp q)
  change L.symm (booleanRankParameter (r + 1) * x) =
    polynomialParameter K q.val (r + 1) * L.symm x
  apply L.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := (rankStageComponent_good K Control act h₁ hmul n old
    (rankStageLowerIndex n hs p hp q)).1 r (L.symm x)
  change L (polynomialParameter K q.val (r + 1) * L.symm x) =
    booleanRankParameter (r + 1) * L (L.symm x) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem rankStageBoundaryEquiv_graded (q : Set.Iio p) (j : ℕ)
    (x : BarycentricStalk K q.val)
    (hx : x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) j) :
    (rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp).component q x ∈
      polynomialDegreePiece j :=
  reverseStalkLinearEquiv_symm_graded K q.val
    (rankStageComponentEquiv K Control act h₁ hmul n old hbij
      (rankStageLowerIndex n hs p hp q))
    (rankStageComponent_good K Control act h₁ hmul n old
      (rankStageLowerIndex n hs p hp q)).2.1 j x hx

theorem rankStageBoundaryEquiv_one (q : Set.Iio p) :
    (rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp).component q 1 = 1 := by
  let L : PolynomialStalk K q.val ≃ₗ[K] BarycentricStalk K q.val := rankStageComponentEquiv K Control act h₁ hmul n old hbij
    (rankStageLowerIndex n hs p hp q)
  change L.symm 1 = 1
  apply L.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (rankStageComponent_good K Control act h₁ hmul n old
    (rankStageLowerIndex n hs p hp q)).2.2.1.symm

include hbij in
/-- A concrete ordinary local equivalence with exactly the old lower-face
maps. No equivariance or quotient prescription is added at this step. -/
theorem exists_rankStage_ordinaryLocal
    [LinearOrder (FaceVertex p)] [Nonempty (FaceVertex p)] :
    ∃ f : PolynomialStalk K p ≃ₗ[K] BarycentricStalk K p,
      IsParameterLinear polynomialColorMap booleanColorMap f.toLinearMap ∧
      (∀ (q : Set.Iio p) x,
        booleanRestriction (faceVertexInclusion q.property.le) (f x) =
          rankStageComponent K Control act h₁ hmul n old
            (rankStageLowerIndex n hs p hp q) (polynomialRestriction K q.property.le x)) ∧
      (∀ j x, x ∈ polynomialDegreePiece j → f x ∈
        basisOrdinaryDegreePiece booleanChainBasis (fun a => booleanOrdinaryDegree a.val) j) ∧
      f 1 = 1 := by
  obtain ⟨f, hf, hb, hg, h1⟩ := exists_reverseCoherentLocalExtension K hs p
    (rankStageBoundaryEquiv K Control act h₁ hmul n old hbij hs p hp)
    (rankStageBoundaryEquiv_parameter K Control act h₁ hmul n old hbij hs p hp)
    (rankStageBoundaryEquiv_graded K Control act h₁ hmul n old hbij hs p hp)
    (rankStageBoundaryEquiv_one K Control act h₁ hmul n old hbij hs p hp)
  exact ⟨f, hf, hb, hg, h1⟩

end ScalarFamilies
end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicPrimePowerPrescribedLocal.lean -/
section


section

/-! # A complete local extension with the actual orbit prescription

This combines ordinary correction and integral equivariant lifting. The
prescribed map is literally ψ∘E, the retained boundary is literally the
ordinary inverse comparison, and the resulting map is proved bijective.
The hypotheses are only the boundary compatibility and the already built
comparison on the orbit simplex.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourPapers.Universal
open Classical
open scoped CyclicParameterAction

variable (p : ℕ) [Fact p.Prime]
variable {W G : Type*} [Fintype W] [Nonempty W] [Group G] [Finite G] [IsCyclic G]
variable (K : Type*) [CommRing K]
variable (ρ : G →* Equiv.Perm (ZMod p × W))
variable (hρ : ∀ g, CommutesPrimeTranslations p (ρ g))
variable (hG : IsPGroup p G) (Z : Subgroup G) (hZ : Nat.card Z = p)
variable (htranslations : ∀ t : ZMod p, ∃ z : Z,
  ρ z.val = primeOrbitRelabel p (Equiv.refl W) (fun _ => t))

local instance (priority := 2000) : DecidableEq W := Classical.decEq _
local instance (priority := 2000) : DecidableEq (ZMod p × W) := Classical.decEq _
local instance (priority := 2000) : LinearOrder (ZMod p × W) := primePowerVertexOrder p

theorem booleanBoundary_relabel_congr (e : Equiv.Perm (ZMod p × W))
    (x y : BooleanBarycentricRing (ZMod p × W) K)
    (hxy : booleanBoundaryMap x = booleanBoundaryMap y) :
    booleanBoundaryMap (booleanVertexRelabelEquiv e x) =
      booleanBoundaryMap (booleanVertexRelabelEquiv e y) := by
  have hz : booleanBoundaryMap (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, htop⟩ := (booleanBoundaryMap_eq_zero_iff (x-y)).mp hz
  have hzero : booleanBoundaryMap (booleanVertexRelabelEquiv e (x-y)) = 0 := by
    apply (booleanBoundaryMap_eq_zero_iff _).mpr
    refine ⟨booleanVertexRelabelEquiv e z, ?_⟩
    rw [← htop, map_mul, booleanVertexRelabel_top]
  rw [map_sub, map_sub] at hzero
  exact sub_eq_zero.mp hzero

include hG hZ htranslations

/-- The actual controlled local step for cyclic prime-power stabilizers. -/
theorem exists_primePower_prescribed_local_equiv
    (L : BooleanBarycentricRing (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
      MvPolynomial (ZMod p × W) K)
    (hL : ∀ n x, x ∈ PrimeBooleanDegreePiece p K n ↔ L x ∈ polynomialDegreePiece n)
    (hLone : L 1 = 1)
    (ψ : MvPolynomial W K →ₗ[K] BooleanBarycentricRing W K)
    (hψp : ∀ r x, ψ (MvPolynomial.esymm W K (r+1) * x) = booleanRankParameter (r+1) * ψ x)
    (hψg : ∀ n x, x ∈ polynomialDegreePiece n → ψ x ∈ basisOrdinaryDegreePiece booleanChainBasis
      (fun a => booleanOrdinaryDegree a.val) n)
    (hψe : ∀ g x, ψ (MvPolynomial.rename (primeOrbitParentAction p ρ hρ g) x) =
      booleanVertexRelabelEquiv (primeOrbitParentAction p ρ hρ g) (ψ x))
    (hdiscrepancy : ∀ x, booleanBoundaryMap
      (ψ (primeOrbitMomentRetraction p K x) - primeFixedFaceQuotient p K (L.symm x)) = 0)
    (hboundary : ∀ g x,
      booleanBoundaryMap (L.symm (MvPolynomial.rename (ρ g) x)) =
        booleanBoundaryMap (booleanVertexRelabelEquiv (ρ g) (L.symm x))) :
    ∃ F : MvPolynomial (ZMod p × W) K ≃ₗ[PrimePowerParameterRing (W := W) p K]
        BooleanBarycentricRing (ZMod p × W) K,
      (∀ n x, x ∈ polynomialDegreePiece n → F x ∈ PrimeBooleanDegreePiece p K n) ∧
      F 1 = 1 ∧
      (∀ x, booleanBoundaryMap (F x) = booleanBoundaryMap (L.symm x)) ∧
      (∀ x, primeFixedFaceQuotient p K (F x) = ψ (primeOrbitMomentRetraction p K x)) ∧
      (∀ g x, F (MvPolynomial.rename (ρ g) x) = booleanVertexRelabelEquiv (ρ g) (F x)) := by
  obtain ⟨β, hβg, hβb, hβπ, hβone⟩ := exists_primePower_ordinary_prescribed_lift
    p K L hL ψ hψp hψg hdiscrepancy
  have hβeqb (g : G) (x : MvPolynomial (ZMod p × W) K) :
      booleanBoundaryMap (β (MvPolynomial.rename (ρ g) x)) =
        booleanBoundaryMap (booleanVertexRelabelEquiv (ρ g) (β x)) := by
    exact (hβb _).trans ((hboundary g x).trans
      (booleanBoundary_relabel_congr p K (ρ g) (β x) (L.symm x) (hβb x)).symm)
  have hβeqπ (g : G) (x : MvPolynomial (ZMod p × W) K) :
      primeFixedFaceQuotient p K (β (MvPolynomial.rename (ρ g) x)) =
        primeFixedFaceQuotient p K (booleanVertexRelabelEquiv (ρ g) (β x)) := by
    rw [hβπ, primeOrbitMomentRetraction_centralizer p K (ρ g) (hρ g)]
    change ψ (MvPolynomial.rename (primeOrbitParentAction p ρ hρ g)
      (primeOrbitMomentRetraction p K x)) = _
    rw [hψe]
    rw [primeOrbitParentAction_normalForm p ρ hρ g, primeFixedFaceQuotient_relabel, hβπ]
  have hβ₁ : β 1 = 1 := by
    rw [hβone]
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, hLone]
  obtain ⟨F, hFg, hFone, hFb, hFπ, hFe⟩ := exists_primePower_controlled_local_equiv
    p K ρ hρ hG Z hZ htranslations L hL β hβg hβ₁
    (fun x => (hβb (L x)).trans (congrArg booleanBoundaryMap (L.symm_apply_apply x)))
    hβeqb hβeqπ
  exact ⟨F, hFg, hFone, fun x => (hFb x).trans (hβb x),
    fun x => (hFπ x).trans (hβπ x), hFe⟩

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralAveraging.lean -/
section


section

/-! # Integral affine averaging without division

This is the argument of Lemma A.8.  The group order is never inverted: the
errors of a point fixed modulo the group order are first divided inside the
given lattice, and their sum is the correction to an integral fixed point.
-/

noncomputable section

namespace FourPapers.Universal

open scoped BigOperators

variable {K G M N : Type*} [CommRing K] [Group G] [Fintype G]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem representation_sum_fixed (ρ : CyclicRepresentation K G M) (h : G) (x : M) :
    ρ h (∑ g : G, ρ g x) = ∑ g : G, ρ g x := by
  rw [map_sum]
  calc
    ∑ g : G, ρ h (ρ g x) = ∑ g : G, ρ (h * g) x := by
      apply Finset.sum_congr rfl
      intro g hg
      exact (congrArg (fun f : M →ₗ[K] M => f x) (ρ.map_mul h g)).symm
    _ = ∑ g : G, ρ g x :=
      Fintype.sum_equiv (Equiv.mulLeft h) (fun g => ρ (h * g) x)
        (fun g => ρ g x) (fun _ => rfl)

/-- The explicit correction has norm equal to the ordinary group norm. -/
theorem affineCorrection_norm (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    Fintype.card G • (x + ∑ g : G, v g) = ∑ g : G, ρ g x := by
  rw [nsmul_add, Finset.smul_sum]
  simp only [hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]

/-- Lemma A.8 in linear ambient coordinates.  Injectivity of multiplication by
the group order is exactly the torsion-free fact used from the integral
lattice. -/
theorem affineCorrection_fixed (ρ : CyclicRepresentation K G M) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g) :
    ∀ h, ρ h (x + ∑ g : G, v g) = x + ∑ g : G, v g := by
  intro h
  apply hregular
  change Fintype.card G • (ρ h (x + ∑ g : G, v g)) = Fintype.card G • (x + ∑ g : G, v g)
  rw [← map_nsmul, affineCorrection_norm ρ x v hv, representation_sum_fixed]

/-- The integral correction stays in the same affine fiber whenever each
divided error lies in the restriction kernel. -/
theorem exists_fixedPoint_sameFiber (ρ : CyclicRepresentation K G M)
    (q : M →ₗ[K] N) (x : M) (v : G → M)
    (hregular : Function.Injective (fun y : M => Fintype.card G • y))
    (hv : ∀ g, ρ g x = x + Fintype.card G • v g)
    (hqv : ∀ g, q (v g) = 0) :
    ∃ y : M, (∀ g, ρ g y = y) ∧ q y = q x := by
  refine ⟨x + ∑ g : G, v g, affineCorrection_fixed ρ x v hregular hv, ?_⟩
  simp [hqv]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegralHom.lean -/
section


section

/-! # Integral affine correction on parameter-linear maps

Conjugation gives an honest representation on the module of parameter-linear
maps.  The integral correction is therefore applied to the actual maps, not
to independently averaged values on a chosen basis.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical
open scoped BigOperators

variable {A G M N : Type*} [CommRing A] [Group G]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def parameterHomRepresentation (ρ : CyclicRepresentation A G M)
    (τ : CyclicRepresentation A G N) : CyclicRepresentation ℤ G (M →ₗ[A] N) where
  toFun g := {
    toFun f := (τ g).comp (f.comp (ρ g⁻¹))
    map_add' := by intro f h; ext x; simp
    map_smul' := by intro c f; ext x; simp }
  map_one' := by ext f x; simp
  map_mul' g h := by
    ext f x
    change τ (g * h) (f (ρ (g * h)⁻¹ x)) =
      τ g (τ h (f (ρ h⁻¹ (ρ g⁻¹ x))))
    rw [mul_inv_rev, ρ.map_mul, τ.map_mul]
    rfl

@[simp] theorem parameterHomRepresentation_apply
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (g : G) (f : M →ₗ[A] N) (x : M) :
    parameterHomRepresentation ρ τ g f x = τ g (f (ρ g⁻¹ x)) := rfl

theorem parameterHomRepresentation_fixed_iff
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) :
    (∀ g, parameterHomRepresentation ρ τ g f = f) ↔ RepresentationIntertwines ρ τ f := by
  constructor
  · intro h g x
    have hh := congrArg (fun F : M →ₗ[A] N => F (ρ g x)) (h g)
    have hinv : ρ g⁻¹ (ρ g x) = x := by
      change (ρ g⁻¹ * ρ g) x = x
      rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
      rfl
    change τ g (f (ρ g⁻¹ (ρ g x))) = f (ρ g x) at hh
    rw [hinv] at hh
    exact hh.symm
  · intro h g
    ext x
    change τ g (f (ρ g⁻¹ x)) = f x
    rw [h]
    change (τ g * τ g⁻¹) (f x) = f x
    rw [← τ.map_mul, mul_inv_cancel, τ.map_one]
    rfl

variable [Fintype G]

theorem parameterHom_nsmul_injective
    (hN : Function.Injective (fun y : N => Fintype.card G • y)) :
    Function.Injective (fun f : M →ₗ[A] N => Fintype.card G • f) := by
  intro f h he
  ext x
  apply hN
  exact congrArg (fun F : M →ₗ[A] N => F x) he

/-- Lemma A.8 applied to actual parameter-linear maps, with exact preservation
of a boundary map and any separately specified homogeneous submodules. -/
theorem exists_integralEquivariant_map_correction
    {Q : Type*} [AddCommGroup Q] (q : N →ₗ[ℤ] Q)
    (ρ : CyclicRepresentation A G M) (τ : CyclicRepresentation A G N)
    (f : M →ₗ[A] N) (v : G → M →ₗ[A] N)
    (hN : Function.Injective (fun y : N => Fintype.card G • y))
    (hv : ∀ g, parameterHomRepresentation ρ τ g f = f + Fintype.card G • v g)
    (hqv : ∀ g x, q (v g x) = 0)
    (S : ℕ → Submodule ℤ M) (T : ℕ → Submodule ℤ N)
    (hfgrade : ∀ n x, x ∈ S n → f x ∈ T n)
    (hvgrade : ∀ g n x, x ∈ S n → v g x ∈ T n)
    (x₀ : M) (hv₀ : ∀ g, v g x₀ = 0) :
    ∃ F : M →ₗ[A] N,
      RepresentationIntertwines ρ τ F ∧
      (∀ x, q (F x) = q (f x)) ∧
      (∀ n x, x ∈ S n → F x ∈ T n) ∧ F x₀ = f x₀ := by
  let F : M →ₗ[A] N := f + ∑ g, v g
  have hfixed : ∀ g, parameterHomRepresentation ρ τ g F = F :=
    affineCorrection_fixed (parameterHomRepresentation ρ τ) f v
      (parameterHom_nsmul_injective hN) hv
  refine ⟨F, (parameterHomRepresentation_fixed_iff ρ τ F).mp hfixed, ?_, ?_, ?_⟩
  · intro x
    change q (f x + (∑ g, v g) x) = q (f x)
    simp [hqv]
  · intro n x hx
    change f x + (∑ g, v g) x ∈ T n
    apply (T n).add_mem (hfgrade n x hx)
    rw [LinearMap.sum_apply]
    exact (T n).sum_mem (fun g _ => hvgrade g n x hx)
  · change f x₀ + (∑ g, v g) x₀ = f x₀
    simp [hv₀]

end FourPapers.Universal

end
end
end

/- BEGIN FourPapers/Universal/CyclicIntegerCoefficients.lean -/
section


section

/-! # Exact integer coefficient lifting and division

The integer-to-modular steps are coefficientwise identities in the actual
multivariate polynomial rings.  Homogeneous lifts retain the original
exponent vectors; division is used only after divisibility has been proved.
-/

noncomputable section
set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {V : Type*}

def liftZModPolynomial (p : ℕ) (f : MvPolynomial V (ZMod p)) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ZMod p => (c.val : ℤ)) (by simp) f.coeff)

@[simp] theorem liftZModPolynomial_coeff (p : ℕ) (f : MvPolynomial V (ZMod p))
    (a : V →₀ ℕ) :
    (liftZModPolynomial p f).coeff a = ((f.coeff a).val : ℤ) := rfl

theorem liftZModPolynomial_map (p : ℕ) [NeZero p] (f : MvPolynomial V (ZMod p)) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (liftZModPolynomial p f) = f := by
  ext a
  rw [MvPolynomial.coeff_map, liftZModPolynomial_coeff]
  change (((f.coeff a).val : ℤ) : ZMod p) = f.coeff a
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

def divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ) : MvPolynomial V ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun c : ℤ => c / (p : ℤ)) (by simp) f.coeff)

@[simp] theorem divideIntegerPolynomial_coeff (p : ℕ) (f : MvPolynomial V ℤ)
    (a : V →₀ ℕ) :
    (divideIntegerPolynomial p f).coeff a = f.coeff a / (p : ℤ) := rfl

theorem nsmul_divideIntegerPolynomial (p : ℕ) (f : MvPolynomial V ℤ)
    (hf : MvPolynomial.map (Int.castRingHom (ZMod p)) f = 0) :
    p • divideIntegerPolynomial p f = f := by
  ext a
  have hc := congrArg (fun h : MvPolynomial V (ZMod p) => h.coeff a) hf
  rw [MvPolynomial.coeff_map] at hc
  change (f.coeff a : ZMod p) = 0 at hc
  have hd : (p : ℤ) ∣ f.coeff a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hc
  rw [MvPolynomial.coeff_smul, divideIntegerPolynomial_coeff, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_of_dvd hd

theorem integerPolynomial_nsmul_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (fun f : MvPolynomial V ℤ => p • f) := by
  intro f g hfg
  ext a
  have h := congrArg (fun h : MvPolynomial V ℤ => h.coeff a) hfg
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, nsmul_eq_mul, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (by exact_mod_cast hp) h

variable [Fintype V] [LinearOrder V]

theorem liftZModPolynomial_degree (p n : ℕ) (f : MvPolynomial V (ZMod p))
    (hf : f ∈ polynomialDegreePiece n) :
    liftZModPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [liftZModPolynomial_coeff, hf a ha]
  simp

theorem divideIntegerPolynomial_degree (p n : ℕ) (f : MvPolynomial V ℤ)
    (hf : f ∈ polynomialDegreePiece n) :
    divideIntegerPolynomial p f ∈ polynomialDegreePiece n := by
  intro a ha
  rw [divideIntegerPolynomial_coeff, hf a ha]
  simp

theorem integerPolynomial_degree_of_nsmul {p n : ℕ} (hp : p ≠ 0)
    (f : MvPolynomial V ℤ) (hf : p • f ∈ polynomialDegreePiece n) :
    f ∈ polynomialDegreePiece n := by
  intro a ha
  have hh := hf a ha
  rw [MvPolynomial.coeff_smul, nsmul_eq_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hp)

end FourPapers.Universal

end
end
end


-- Close only the anonymous source scopes reopened by the next shard.

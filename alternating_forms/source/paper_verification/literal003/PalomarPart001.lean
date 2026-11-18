module

public import paper_verification.literal003.PalomarPart000
import all paper_verification.literal003.PalomarPart000
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.SetTheory.Cardinal.Finite
public import paper_verification.literal002
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import paper_verification.literal001
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import paper_verification.literal000
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option Elab.async false

section TAF_LiteralSource_0208
/- Original module: TauCeti.LinearAlgebra.CliffordAlgebra.Contraction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.

/-!
# Contraction against the `ℤ/2`-grading, and the change of form on right factors

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance because an
anisotropic vector orthogonal to a polarization acts on a spinor module by its scalar coordinate
times the grade involution. More precisely, contraction is a derivation twisted by the grade
involution, `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`, the graded Leibniz rule of an odd
operator.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so `evenOdd Q (i + 1)` and `evenOdd Q (i - 1)` are the same submodule; the statement below
names the first.

The parity statement is proved by induction over the grading; its base case is read off by
`CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
`CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`, which are general facts about the
grading and live with it.

Mathlib's `CliffordAlgebra.changeForm` is built by folding from the left, so Mathlib describes
it on left factors only (`CliffordAlgebra.changeForm_ι_mul`). The second half of this file supplies
the right-handed description `CliffordAlgebra.changeForm_mul_ι`, which rests on the graded
Leibniz rules for a contraction meeting a vector factor on the far side and on the commutation of
left with right contraction, left as a `TODO` in Mathlib. From it, `changeForm` commutes with
reversion when the bilinear form is symmetric; and since contraction anticommutes with the grade
involution, `changeForm` commutes with the grade involution for every bilinear form. In particular
`CliffordAlgebra.equivExterior` intertwines both operations with those of the exterior algebra.

## Main results

* `CliffordAlgebra.contractLeft_map`: contraction is natural under quadratic isometries.

* `CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**.
* `CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.
* `CliffordAlgebra.contractLeft_mul`: the graded Leibniz rule
  `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.
* `CliffordAlgebra.contractLeft_mul_ι` and `CliffordAlgebra.contractRight_ι_mul`: the graded
  Leibniz rules for a vector factor on the far side.
* `CliffordAlgebra.contractRight_contractLeft`: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`.
* `CliffordAlgebra.contractLeft_prod_map_ι_eq_zero`: a contraction kills a product of vectors in
  its kernel.
* `CliffordAlgebra.changeForm_mul_ι`: `changeForm` on a right vector factor.
* `CliffordAlgebra.changeForm_involute` and `CliffordAlgebra.changeForm_reverse`: `changeForm`
  commutes with the grade involution, and with reversion for a symmetric form.
* `CliffordAlgebra.equivExterior_involute` and `CliffordAlgebra.equivExterior_reverse`: the same
  for the isomorphism with the exterior algebra.
* `CliffordAlgebra.equivExterior_mem_evenOdd_iff`: that isomorphism preserves the `ℤ/2`-grading.
* `CliffordAlgebra.equivExterior_ι_mul` and `CliffordAlgebra.equivExterior_mul_ι`: that
  isomorphism on left and right vector factors.
* `CliffordAlgebra.equivExterior_prod_map_ι_of_pairwise_isOrtho`: that isomorphism sends a product
  of pairwise orthogonal vectors to their exterior product.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/

public section


universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

section Naturality

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Contraction against a linear functional commutes with the algebra map induced by a
quadratic isometry, after pulling back the functional. -/
theorem contractLeft_map (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂)
    (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, contractLeft_ι_mul, hx, map_sub,
      map_smul, LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap]

end Naturality

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) := by
  -- Two parity facts, used to keep the indices in `ZMod 2` honest.
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  have hshift : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_range_ι_pow_zero hv
      simp
    · obtain ⟨a, rfl⟩ := exists_ι_of_mem_range_ι_pow_one hv
      rw [contractLeft_ι, hone]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h₂ : ι Q m₂ * x ∈ evenOdd Q (i + 1) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) hx
    have h₁ : contractLeft d (ι Q m₂ * x) ∈ evenOdd Q i := by
      rw [contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hx) ?_
      simpa only [hshift] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) ih
    rw [mul_assoc, contractLeft_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ h₂) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₁) h₁

/-- **The graded Leibniz rule for contraction.** Contraction against `d` is a derivation twisted
by the grade involution: `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.  On a homogeneous
multivector `x` of degree `n` the involution is the sign `(-1) ^ n`, which gives the familiar
odd-derivation rule. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) = contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; abel
  | ι_mul x a hx =>
    rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, neg_mul, mul_assoc]
    abel

/-- **The graded Leibniz rule for a right vector factor.** Contraction against `d` passes through
a right factor `ι Q m`, at the cost of the term `d m • involute x` produced by contracting that
factor itself after it has moved past `x`. -/
theorem contractLeft_mul_ι (d : Module.Dual R M) (x : CliffordAlgebra Q) (m : M) :
    contractLeft d (x * ι Q m) = contractLeft d x * ι Q m + d m • involute x := by
  rw [contractLeft_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The graded Leibniz rule for right contraction and a left vector factor**, the mirror image of
`CliffordAlgebra.contractLeft_mul_ι` under reversion: `(ι Q a * x) ⌊ d` is
`ι Q a * (x ⌊ d) + d a • involute x`. -/
theorem contractRight_ι_mul (d : Module.Dual R M) (a : M) (x : CliffordAlgebra Q) :
    contractRight (ι Q a * x) d = ι Q a * contractRight x d + d a • involute x := by
  simp [contractRight_eq, contractLeft_mul_ι, reverse_involute_commute.eq]

/-- **Left and right contraction commute**: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`. This is the statement
left as a `TODO` after `CliffordAlgebra.contractRight_comm` in Mathlib. -/
theorem contractRight_contractLeft (d d' : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractRight (contractLeft d x) d' = contractLeft d (contractRight x d') := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x a hx =>
    simp [contractLeft_ι_mul, contractRight_ι_mul, hx, involute_contractLeft]
    abel

/-- Contraction against a functional `d` kills a product of vectors that `d` annihilates. -/
theorem contractLeft_prod_map_ι_eq_zero (d : Module.Dual R M) {l : List M}
    (h : ∀ m ∈ l, d m = 0) : contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h a List.mem_cons_self, zero_smul,
      ih fun m hm ↦ h m (List.mem_cons_of_mem a hm), mul_zero, sub_zero]

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}
  (h : B.toQuadraticMap = Q' - Q)

/-- **`changeForm` and a right vector factor**: the right-handed counterpart of Mathlib's
`CliffordAlgebra.changeForm_ι_mul`, in which the correction term contracts from the right against
the functional `B.flip m = B · m`. No symmetry of `B` is needed. -/
theorem changeForm_mul_ι (x : CliffordAlgebra Q) (m : M) :
    changeForm h (x * ι Q m) =
      changeForm h x * ι Q' m - contractRight (changeForm h x) (B.flip m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.commutes, changeForm_ι_mul, changeForm_algebraMap, contractLeft_algebraMap,
      contractRight_algebraMap, sub_zero, sub_zero, Algebra.commutes]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, LinearMap.add_apply]
    abel
  | ι_mul x a hx =>
    simp [mul_assoc, changeForm_ι_mul, hx, contractLeft_mul_ι, contractRight_contractLeft,
      contractRight_ι_mul, mul_sub, sub_mul]
    abel

/-- **`changeForm` commutes with the grade involution**, for every bilinear form `B`. -/
@[simp]
theorem changeForm_involute (x : CliffordAlgebra Q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_ι_mul, hx, involute_contractLeft]
    abel

/-- **`changeForm` commutes with reversion** when the bilinear form `B` is symmetric. This covers
`CliffordAlgebra.equivExterior`, whose bilinear form is the symmetric
`QuadraticMap.associated (-Q)`. -/
theorem changeForm_reverse (hB : LinearMap.IsSymm B) (x : CliffordAlgebra Q) :
    changeForm h (reverse x) = reverse (changeForm h x) := by
  have hflip : B.flip=B := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact hB.eq b a
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_mul_ι, hx, changeForm_ι_mul, contractRight_eq,hflip]

end changeForm

section equivExterior

variable [Invertible (2 : R)] (Q)

/-- `CliffordAlgebra.equivExterior` on a left vector factor: the specialization of Mathlib's
`CliffordAlgebra.changeForm_ι_mul` to the bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_ι_mul (m : M) (x : CliffordAlgebra Q) :
    equivExterior Q (ι Q m * x) =
      ExteriorAlgebra.ι R m * equivExterior Q x -
        contractLeft (QuadraticMap.associated (-Q) m) (equivExterior Q x) :=
  changeForm_ι_mul changeForm.associated_neg_proof m x

/-- `CliffordAlgebra.equivExterior` on a right vector factor: the specialization of
`CliffordAlgebra.changeForm_mul_ι` to the symmetric bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_mul_ι (x : CliffordAlgebra Q) (m : M) :
    equivExterior Q (x * ι Q m) =
      equivExterior Q x * ExteriorAlgebra.ι R m -
        contractRight (equivExterior Q x) (QuadraticMap.associated (-Q) m) := by
  rw [← QuadraticMap.associated_flip]
  exact changeForm_mul_ι changeForm.associated_neg_proof x m

/-- `CliffordAlgebra.equivExterior` intertwines the grade involutions.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, where `CliffordAlgebra.changeForm_involute` applies. -/
theorem equivExterior_involute (x : CliffordAlgebra Q) :
    equivExterior Q (involute x) = involute (equivExterior Q x) :=
  changeForm_involute changeForm.associated_neg_proof x

/-- **`CliffordAlgebra.equivExterior` preserves the `ℤ/2`-grading**: a Clifford element has
parity `i` exactly when its image in the exterior algebra has parity `i`. -/
theorem equivExterior_mem_evenOdd_iff {i : ZMod 2} {x : CliffordAlgebra Q} :
    equivExterior Q x ∈ evenOdd (0 : QuadraticForm R M) i ↔ x ∈ evenOdd Q i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · rw [← involute_eq_self_iff, ← involute_eq_self_iff, ← equivExterior_involute,
      (equivExterior Q).injective.eq_iff]
  · rw [← involute_eq_neg_iff, ← involute_eq_neg_iff, ← equivExterior_involute, ← map_neg,
      (equivExterior Q).injective.eq_iff]

/-- `CliffordAlgebra.equivExterior` intertwines reversion, because the bilinear form
`QuadraticMap.associated (-Q)` it changes the form by is symmetric.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_reverse (x : CliffordAlgebra Q) :
    equivExterior Q (reverse x) = reverse (equivExterior Q x) :=
  changeForm_reverse changeForm.associated_neg_proof (QuadraticForm.associated_isSymm R (-Q)) x

/-- **`CliffordAlgebra.equivExterior` sends a product of pairwise orthogonal vectors to their
exterior product.** Each correction term of `CliffordAlgebra.equivExterior_ι_mul` contracts the
later factors against the first, and vanishes by orthogonality. No hypothesis on `Q` is needed;
in particular `Q` may be degenerate. -/
theorem equivExterior_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    equivExterior Q (l.map (ι Q)).prod = (l.map (ExteriorAlgebra.ι R)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, equivExterior_ι_mul, ih hl.2,
      contractLeft_prod_map_ι_eq_zero, sub_zero, List.map_cons, List.prod_cons]
    intro m hm
    simp [hl.1 m hm]

end equivExterior

end CliffordAlgebra
end
end TAF_LiteralSource_0208

section TAF_LiteralSource_0209
/- Original module: TauCeti.LinearAlgebra.ExteriorPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module, and that exterior powers of projective
modules are projective.

It then builds the surjection `exteriorPower.fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M` that is
left inverse, up to the factor `n!`, to Mathlib's antisymmetrization
`exteriorPower.toTensorPower`: composing the antisymmetrization with it is `n! • id` on the exterior
power, while composing the two the other way round is the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. Consequently the antisymmetrization is injective once `n!` is a
unit in the base ring, and its image is the image of that operator. That is the statement a Young
symmetrizer of a one-column shape consumes.

Finally, it describes images of exterior powers under induced maps: inside the exterior algebra,
the image of `⋀ⁿ M` under `f` is the `n`th power of the degree-one image of `f`, and over a field an
injective map embeds `⋀ⁿ V` with its binomial dimension.

## Main definitions

* `exteriorPower.fromTensorPower` is the canonical surjection of the tensor power onto the
  exterior power.
## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.instProjective`: exterior powers of projective modules are projective.
* `exteriorPower.fromTensorPower_comp_toTensorPower`: antisymmetrizing and projecting back is
  multiplication by `n!`, whence `exteriorPower.toTensorPower_injective`.
* `exteriorPower.ιMulti_ne_zero_iff`: over a field, an exterior product of vectors is nonzero
  exactly when the vectors are linearly independent.
* `exteriorPower.toTensorPower_injective_of_free`: antisymmetrization is injective for free
  modules in every characteristic, without factorial invertibility.
* `exteriorPower.range_toTensorPower`: the image of the antisymmetrization is the image of the
  antisymmetrization operator on the tensor power.
* `exteriorPower.map_bijective`: a bijective linear map induces bijections of exterior powers.
* `exteriorPower.toTensorPower_comp_map` and `exteriorPower.map_comp_fromTensorPower`: the
  antisymmetrization and the canonical surjection are natural in the module.
* `TauCeti.ExteriorAlgebra.exteriorPower_map_map`: the image of `⋀ⁿ M` in the exterior algebra
  under the map induced by `f` is the `n`th power of the degree-one image of `f`.
* `TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one` and
  `TauCeti.ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one`: the first exterior power consists of
  the vectors, and `ExteriorAlgebra.ιInv` recovers the vector from its image.
* `TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower` and `TauCeti.ExteriorAlgebra.wedgeLeft`:
  left multiplication by a vector carries `⋀ⁿ M` into `⋀ⁿ⁺¹ M`, packaged as the linear map
  `v ↦ m ∧ v` with values in degree `n + 1`.
* `TauCeti.exteriorPower.finrank_range_map`: over a field, the image of `⋀ⁿ V` under the map
  induced by an injective linear map has dimension `(dim V).choose n`.
* `TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero`: over a field, a vector lies in
  the span of a linearly independent family exactly when its product with the exterior product of
  the family vanishes.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

/-! ### Antisymmetrization of free modules -/

section Free

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Pairing with a pure exterior product of linear forms factors through the
antisymmetrization into the tensor power. -/
theorem pairingDual_ιMulti_apply {n : ℕ} (g : Fin n → Module.Dual R M) (x : ⋀[R]^n M) :
    pairingDual R M n (ιMulti R n g) x =
      TensorPower.multilinearMapToDual R M n g (toTensorPower R M n x) := by
  simp [pairingDual, alternatingMapToDual]

/-- Antisymmetrization embeds every exterior power of a free module into its tensor power,
over any commutative ring, without requiring the factorial to be invertible. -/
theorem toTensorPower_injective_of_free [Module.Free R M] {n : ℕ} :
    Function.Injective (toTensorPower R M n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  -- Each exterior-basis coordinate factors through antisymmetrization.
  intro x y h
  apply (b.exteriorPower n).repr.injective
  ext s
  rw [basis_repr_apply, basis_repr_apply]
  simp only [ιMultiDual, ιMulti_family, pairingDual_ιMulti_apply, h]

end Free

/-! ### Projectivity -/

section Projective

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Exterior powers of a projective module are projective: `⋀[R]^n M` is a direct summand of the
exterior power of the free module `M →₀ R`. -/
instance instProjective [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  refine .of_split (map n s) (map n (Finsupp.linearCombination R id)) ?_
  rw [← map_comp, hs, map_id]

end Projective

/-! ### The exterior power as a quotient of the tensor power -/

section FromTensorPower

variable [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

variable (R M) in
/-- **The canonical surjection of the tensor power onto the exterior power**, sending a pure
tensor to the corresponding exterior product.

Mathlib's `exteriorPower.toTensorPower` runs the other way, by antisymmetrization; antisymmetrizing
and then projecting back is `n!` on the exterior power, while projecting and then antisymmetrizing
is the antisymmetrization operator `∑_σ sgn(σ) σ` on the tensor power. -/
noncomputable def fromTensorPower : (⨂[R]^n M) →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti R n).toMultilinearMap

@[simp]
theorem fromTensorPower_tprod (m : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod R m) = ιMulti R n m :=
  PiTensorProduct.lift.tprod m

theorem fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod R v, fromTensorPower_tprod n v⟩

/-- Antisymmetrizing an exterior product and projecting it back multiplies by `n!`: each of the
`n!` signed reorderings returns the same exterior product. -/
@[simp]
theorem fromTensorPower_comp_toTensorPower :
    (fromTensorPower R M n) ∘ₗ (toTensorPower R M n) =
      n.factorial • LinearMap.id (R := R) (M := ⋀[R]^n M) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) * ((Equiv.Perm.sign σ : ℤ)) = 1 := fun σ => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have h : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) • ιMulti R n (fun i => v (σ i)) = ιMulti R n v := fun σ => by
    rw [← Function.comp_def v σ, (ιMulti R n).map_perm, Units.smul_def, smul_smul, hsq, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_apply_ιMulti, map_sum]
  simp only [Units.smul_def, map_zsmul, fromTensorPower_tprod, h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- The antisymmetrization is injective as soon as `n!` is a unit in the base ring, for instance
over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit (n.factorial : R)) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the canonical surjection by `u⁻¹` makes it a left inverse of the antisymmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • fromTensorPower R M n) ?_
  rw [LinearMap.smul_comp, fromTensorPower_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← hu, u.inv_mul, one_smul]

/-- Projecting a tensor to the exterior power and antisymmetrizing it back is the
antisymmetrization operator `∑_σ sgn(σ) σ` of the tensor power. -/
theorem toTensorPower_comp_fromTensorPower :
    (toTensorPower R M n) ∘ₗ (fromTensorPower R M n) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, Function.comp_apply, fromTensorPower_tprod,
    toTensorPower_apply_ιMulti, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
  simp [Units.smul_def, Equiv.Perm.inv_def]

/-- The antisymmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R N n) ∘ₗ (map n f) =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (toTensorPower R M n) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  simp [Units.smul_def, Function.comp_def]

/-- The canonical surjection is natural in the module. -/
theorem map_comp_fromTensorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (map n f) ∘ₗ (fromTensorPower R M n) =
      (fromTensorPower R N n) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [Function.comp_def]

/-- The image of the antisymmetrization is the image of the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R M n) =
      LinearMap.range (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap) := by
  rw [← toTensorPower_comp_fromTensorPower, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fromTensorPower_surjective n), Submodule.map_top]

end FromTensorPower

/-! ### Exterior products over a field -/

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Over a field, the exterior product of `n` vectors is nonzero exactly when they are linearly
independent. -/
theorem ιMulti_ne_zero_iff {n : ℕ} (v : Fin n → V) :
    ιMulti K n v ≠ 0 ↔ LinearIndependent K v := by
  refine ⟨fun h ↦ by_contra fun hv ↦ h ((ιMulti K n).map_linearDependent v hv), fun hv ↦ ?_⟩
  -- The only `n`-element subset of `Fin n` is enumerated by the identity.
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ⇑(Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hs)) = id := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique hs (fun _ ↦ Finset.mem_univ _) strictMono_id).symm
  simpa [ιMulti_family, he] using (ιMulti_family_linearIndependent_field (n := n) hv).ne_zero
    (Set.powersetCard.ofCard hs)

end Field

/-! ### Bijectivity of induced maps -/

section Bijective

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- A bijective linear map induces a bijective map on every exterior power. -/
theorem map_bijective {n : ℕ} {f : M →ₗ[R] N} (hf : Function.Bijective f) :
    Function.Bijective (map n f) :=
  ⟨map_injective (LinearEquiv.ofBijective f hf).symm.toLinearMap (by ext; simp),
    map_surjective hf.2⟩

end Bijective

end exteriorPower

namespace TauCeti

namespace ExteriorAlgebra

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- Inside the exterior algebra, the image of the `n`th exterior power under the map induced by
`f` is the `n`th power of the degree-one image of the range of `f`. -/
theorem exteriorPower_map_map (n : ℕ) (f : M →ₗ[R] N) :
    (⋀[R]^n M).map (_root_.ExteriorAlgebra.map f).toLinearMap =
      ((LinearMap.range f).map (_root_.ExteriorAlgebra.ι R)) ^ n := by
  rw [_root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    _root_.ExteriorAlgebra.ι_range_map_map]

/-- A vector lies in the first exterior power. -/
theorem ι_mem_exteriorPower_one (m : M) : _root_.ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ m

/-- An element of the first exterior power is the vector `ExteriorAlgebra.ιInv` reads off from
it. -/
theorem ι_ιInv_of_mem_exteriorPower_one {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^1 M) :
    _root_.ExteriorAlgebra.ι R (_root_.ExteriorAlgebra.ιInv x) = x := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  rw [_root_.ExteriorAlgebra.ι_leftInverse]

/-- Left multiplication by a vector raises the exterior degree by one: it carries the `n`-th
exterior power into the `(n + 1)`-th. -/
theorem ι_mul_mem_exteriorPower (m : M) {n : ℕ} {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    _root_.ExteriorAlgebra.ι R m * x ∈ ⋀[R]^(n + 1) M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) hx

/-- Exterior multiplication `v ↦ m ∧ v` by a vector `m`, from the `n`-th exterior power to the
`(n + 1)`-th. Mathlib's `exteriorPower.wedge R M 1 n` is the same product with values in degree
`1 + n`, which is not definitionally `n + 1`; this form composes with maps out of `⋀ⁿ⁺¹ M`. -/
def wedgeLeft (m : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R m)).restrict fun _ hx ↦
    ι_mul_mem_exteriorPower m hx

/-- `wedgeLeft m n` is left multiplication by `ι R m` in the exterior algebra. -/
@[simp]
theorem coe_wedgeLeft_apply (m : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft m n x : _root_.ExteriorAlgebra R M) = _root_.ExteriorAlgebra.ι R m * x :=
  (rfl)

/-- `wedgeLeft m n` prepends `m` to a wedge product of vectors: `m ∧ (v₀ ∧ ⋯ ∧ vₙ₋₁)`. -/
@[simp]
theorem wedgeLeft_ιMulti (m : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft m n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R (n + 1) (Fin.cons m v) := by
  ext
  simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

end ExteriorAlgebra

namespace exteriorPower

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W]

/-- Over a field, the image of the `n`th exterior power of a finite-dimensional space under the
map induced by an injective linear map has dimension `(dim V).choose n`. -/
theorem finrank_range_map {f : V →ₗ[K] W} (hf : Function.Injective f) (n : ℕ) :
    Module.finrank K (LinearMap.range (_root_.exteriorPower.map n f)) =
      (Module.finrank K V).choose n := by
  rw [LinearMap.finrank_range_of_inj (_root_.exteriorPower.map_injective_field hf),
    _root_.exteriorPower.finrank_eq]

omit [Module.Finite K V] in
/-- Over a field, a vector lies in the span of a linearly independent family of `n` vectors exactly
when its product with the exterior product of the family vanishes in the exterior algebra. -/
theorem mem_span_range_iff_ι_mul_ιMulti_eq_zero {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (w : V) :
    w ∈ Submodule.span K (Set.range v) ↔
      _root_.ExteriorAlgebra.ι K w * (_root_.exteriorPower.ιMulti K n v : ExteriorAlgebra K V) =
        0 := by
  have hcons : w ∈ Submodule.span K (Set.range v) ↔
      ¬LinearIndependent K (Fin.cons w v : Fin (n + 1) → V) := by
    rw [linearIndependent_finCons]
    tauto
  rw [hcons, ← _root_.exteriorPower.ιMulti_ne_zero_iff, not_not, ← ZeroMemClass.coe_eq_zero,
    _root_.exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_succ_apply,
    _root_.exteriorPower.ιMulti_apply_coe]
  simp [Matrix.vecTail, Function.comp_def]

end exteriorPower

end TauCeti
end
end TAF_LiteralSource_0209

section TAF_LiteralSource_0210
/- Original module: TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.

Each of the two halves acts on an exterior basis vector by a single coordinate move, up to the
shuffle sign that carries the moved coordinate to the front: contraction erases the coordinate
from the index set, and left multiplication inserts it, each vanishing when the index set is on
the wrong side of that move. Creation after contraction at distinct coordinates therefore
replaces an occupied coordinate with an unoccupied one, with the product of their shuffle signs.

The grade involution is diagonal for the exterior basis as well: it multiplies an exterior
monomial, and so the basis vector indexed by `s`, by the parity of its degree.

Every basis vector is the product of the exterior-algebra generators of its index set, in
increasing order; for index sets with one or two elements this is also recorded in the explicit
forms `TauCeti.ExteriorAlgebra.basis_singleton` and `TauCeti.ExteriorAlgebra.basis_pair`.

Independently of a basis, `ExteriorAlgebra.contractLeft_map` states naturality under a linear
map: pull back the contracting functional and then map the contracted element. This follows
from the general quadratic-isometry statement `CliffordAlgebra.contractLeft_map`.

Independently of a basis, the grade involution is the sign `(-1) ^ n` on the `n`-th exterior power,
a contraction carries the `(n + 1)`-th exterior power into the `n`-th, and a vector graded-commutes
with every multivector: `ι m * x = involute x * ι m`.  Together with the graded Leibniz rule
`CliffordAlgebra.contractLeft_mul`, these say that a contraction is an odd derivation of degree
`-1` of the graded-commutative exterior algebra. On a wedge product of vectors it is the alternating
sum of deletions (`TauCeti.ExteriorAlgebra.contractLeft_ιMulti`); this is the differential of the
Koszul complex.

In degree at least the rank, contraction loses no information: if `d m = 1` and
`finrank R M ≤ n`, every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. Hence two forms killed by `d` multiply to
zero once their degrees add up to the rank, and in rank at most four a two-form `x` satisfies
`x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. This is the algebra behind the splitting of a two-form on a product
`ℝ × Y` along the unit normal of the factor `Y`.

On `M × R`, with `e = (0, 1)`, every element `z` of the exterior algebra splits as `a + e ∧ b`,
where `a` and `b` are the images in `⋀ M` of `z` and of its contraction by the second coordinate
(`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`). This is the
decomposition `⋀ᵏ⁺¹ (M × R) ≅ ⋀ᵏ⁺¹ M ⊕ e ∧ ⋀ᵏ M` used to adjoin one element to a Koszul complex.
In this splitting, the contraction by `φ + x · snd` acts as `d(a + e ∧ b) = (d a + x b) - e ∧ d b`
(`ExteriorAlgebra.map_fst_contractLeft_coprod`,
`ExteriorAlgebra.contractLeft_map_fst_contractLeft_snd`).
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An exterior-basis vector is the product of its generators in increasing order**: the basis
vector indexed by `s` is `ι (b i₁) * ⋯ * ι (b iₖ)` for `s.sort = [i₁, …, iₖ]`. -/
theorem _root_.Module.Basis.exteriorAlgebra_eq_prod_map_sort {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s = ((s.sort.map b).map (ExteriorAlgebra.ι R)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  congr 1
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard]
  exact congrArg (fun i ↦ ExteriorAlgebra.ι R (b i)) (Finset.orderEmbOfFin_apply _ _ _)

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  refine contractLeft_prod_map_ι_eq_zero _ fun m hm ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff]
  rintro rfl
  exact absurd ((Finset.mem_sort _).mp hj) hi

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

/-- **The grade involution acts on an exterior-basis vector by the parity of its index set.** The
basis vector indexed by `s` is the monomial on `s.card` generators. -/
@[simp]
theorem involute_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (b.ExteriorAlgebra s) =
      (-1 : R) ^ s.card • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  exact involute_ιMulti _

private def basisEraseSignOfErase {I : Type w} [LinearOrder I]
    (i : I) (t : Finset I) (hi : i ∉ t) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t' : Set.powersetCard I t.card := ⟨t, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t') (by simp [u, t', hi])).sign

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  basisEraseSignOfErase i (s.erase i) (by simp)

private theorem basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem
    {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) (hi : i ∈ s) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  let n := (s.erase i).card
  have hsCard : s.card = n + 1 := by
    simpa [n] using (Finset.card_erase_add_one hi).symm
  -- Enumerate `s` in increasing order. The position `k` of `i` counts precisely the entries
  -- which the shuffle crosses when it moves the singleton `{i}` to the front.
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i := by
    exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) =
      (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr ⟨fun h ↦ k.succAbove_ne j (e.injective (h.trans hek.symm)),
        Finset.orderEmbOfFin_mem s hsCard _⟩
    · exact e.strictMono.comp (Fin.strictMono_succAbove k)
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hsCard' : s.card = 1 + n := hsCard.trans (Nat.add_comm n 1)
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) hsCard' : Set.powersetCard I (1 + n)) := by
    apply Subtype.ext
    simp [u, t, hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  let p' : Equiv.Perm (Fin (n + 1)) := c.symm.trans (p.trans c)
  -- After reconciling the two cardinality presentations, this shuffle is the inverse cycle
  -- which moves position `k` to the front and shifts the preceding positions one step right.
  have hec : (fun q ↦ e (c q)) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop := by
    apply Finset.orderEmbOfFin_unique
    · intro q
      have hdval : (Set.powersetCard.disjUnion hdisj).val = s :=
        congrArg Subtype.val hunion
      rw [hdval]
      exact Finset.orderEmbOfFin_mem s hsCard (c q)
    · intro a b hab
      apply e.strictMono
      simpa [c, Fin.ext_iff] using hab
  have hp : p' = k.cycleRange.symm := by
    apply Equiv.ext
    intro j
    apply e.injective
    -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    -- The disjoint-union permutation enumerates the singleton first and the erased set second.
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    -- Expose the function represented by the increasing enumeration before applying `hec`.
    change (fun q ↦ e (c q)) (p (c.symm j)) = _
    rw [hec]
    let x : (Set.powersetCard.disjUnion hdisj).val :=
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm (c.symm j)))
    have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop (p (c.symm j)) = x := by
      have hpApply : p (c.symm j) =
          (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).symm x := rfl
      rw [hpApply]
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).apply_symm_apply x)
    rw [hx]
    cases j using Fin.cases with
    | zero =>
        have hzero : finSumFinEquiv.symm (c.symm 0) = Sum.inl (0 : Fin 1) := by
          apply finSumFinEquiv.injective
          apply Fin.ext
          rfl
        simp only [x, hzero, Fin.cons_zero]
        -- Coercing the disjoint-union subtype reveals the singleton entry.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        -- The unique increasing enumeration of a singleton is constant at its element.
        change Finset.orderEmbOfFin {i} (Finset.card_singleton i) 0 = i
        exact Finset.orderEmbOfFin_singleton i 0
    | succ q =>
        have hsucc : finSumFinEquiv.symm (c.symm q.succ) = Sum.inr q := by
          apply finSumFinEquiv.injective
          rw [finSumFinEquiv.apply_symm_apply]
          apply Fin.ext
          simp [c]
          omega
        simp only [x, hsucc, Fin.cons_succ]
        -- Coercing the right summand reveals the increasing enumeration of `s.erase i`.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inr ((Set.powersetCard.orderIsoOfFin t) q))) =
            (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rw [Equiv.Finset.disjUnionEquiv_inr]
        dsimp only [Set.powersetCard.orderIsoOfFin, t]
        change (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q =
          (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rfl
  have hsign : Equiv.Perm.sign p' = Equiv.Perm.sign p := by
    simp [p']
  rw [basisEraseSign]
  -- Unfolding the local permutation exposes the sign computed above.
  change Equiv.Perm.sign p = _
  rw [← hsign, hp, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  congr 1
  -- The initial segment below `k` is order-isomorphic to the elements of `s` strictly below `i`,
  -- so its cardinality is the exponent in the claimed sign.
  have himage : Finset.image e (Finset.Iio k) = s.filter (fun j ↦ j < i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hsCard j, hek ▸ e.strictMono hj⟩
    · rintro ⟨hxs, hxi⟩
      let j : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨x, hxs⟩
      refine ⟨j, ?_, ?_⟩
      · exact e.lt_iff_lt.mp (by simpa [e, j, k] using hxi)
      · exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨x, hxs⟩)
  rw [← Fin.card_Iio k, ← himage, Finset.card_image_of_injective _ e.injective]

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. This formula also applies when `i ∉ s`: inserting
`i` changes neither the erased set defining the shuffle nor the indices strictly below `i`. -/
@[simp]
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  by_cases hi : i ∈ s
  · exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i s hi
  · have hsign : basisEraseSign i (insert i s) = basisEraseSign i s := by
      simp [basisEraseSign, hi]
    have hfilter : (insert i s).filter (fun j ↦ j < i) = s.filter (fun j ↦ j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hji' | hjs, hji⟩
        · exact ((ne_of_lt hji) hji').elim
        · exact ⟨hjs, hji⟩
      · exact fun h ↦ ⟨Or.inr h.1, h.2⟩
    rw [← hsign, ← hfilter]
    exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i (insert i s)
      (Finset.mem_insert_self i s)

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  simp [b.exteriorAlgebra_eq_prod_map_sort]

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,
    Finset.sort_insert _ (by simpa using hij.le) (by simpa using hij.ne)]
  simp

/-- Multiplying the basis vector for `i` by the basis vector for `s.erase i` reconstructs the
basis vector for `s`, with the shuffle sign that moves `i` to the front. -/
theorem basis_singleton_mul_basis_erase {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
      basisEraseSign i s • b.ExteriorAlgebra s := by
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, u, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b u t hdisj
  rw [hunion] at hprod
  simpa [basisEraseSign, basisEraseSignOfErase, u, t] using hprod

/-- **Creating a basis coordinate inserts it into the index set**, with the shuffle sign that
moves it to the front; it is zero when the coordinate is already present, since a repeated
generator squares to zero. -/
@[simp]
theorem ι_mul_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0
        else basisEraseSign i (insert i s) • b.ExteriorAlgebra (insert i s) := by
  classical
  rw [← basis_singleton]
  split_ifs with hi
  · exact ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1) (⟨s, rfl⟩ : Set.powersetCard I s.card)
      (by simp [hi])
  · have h := basis_singleton_mul_basis_erase b i (insert i s) (Finset.mem_insert_self i s)
    rwa [Finset.erase_insert hi] at h

/-- Contracting an exterior-basis vector erases the contracted coordinate, with the shuffle sign
that moves that coordinate to the front; it is zero when the coordinate is absent. -/
@[simp]
theorem contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  split_ifs with hi
  · have hprod' := basis_singleton_mul_basis_erase b i s hi
    have hcontract : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
        (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra (s.erase i) := by
      rw [basis_singleton, contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_coord_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign
    · rw [hsign, one_smul] at hprod' ⊢
      rw [← hprod']
      exact hcontract
    · have hprodNeg : b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
          -b.ExteriorAlgebra s := by
        rw [hsign] at hprod'
        simpa using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      rw [hsign]
      simpa using h
  · exact contractLeft_coord_basis_eq_zero_of_not_mem b i s hi

/-- Creating an unoccupied coordinate after contracting an occupied one replaces that
coordinate in an exterior-basis vector, with the product of the two shuffle signs. -/
theorem ι_mul_contractLeft_coord_basis_of_not_mem_of_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i j : I) (s : Finset I) (hi : i ∉ s) (hj : j ∈ s) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord j) (b.ExteriorAlgebra s) =
      (basisEraseSign j s * basisEraseSign i (insert i (s.erase j))) •
        b.ExteriorAlgebra (insert i (s.erase j)) := by
  classical
  simp [contractLeft_coord_basis, ι_mul_basis, hi, hj, mul_smul_comm, smul_smul]

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate.

This is not a `simp` lemma because `contractLeft_coord_basis` is the canonical normal form for
the contraction in its left-hand side. -/
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [contractLeft_coord_basis]
  split_ifs with hi
  · rw [← basis_singleton]
    rw [mul_smul_comm]
    rw [basis_singleton_mul_basis_erase b i s hi]
    let n := (s.filter fun j ↦ j < i).card
    have hsignSq : ((-1 : ℤˣ) ^ n) * ((-1 : ℤˣ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [basisEraseSign_eq_neg_one_pow_card_filter_lt, smul_smul, hsignSq, one_smul]
  · rw [mul_zero]

/-! ### Exterior powers under the grade involution and contraction -/

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- Contraction annihilates the zeroth exterior power, the scalars. -/
theorem contractLeft_eq_zero_of_mem_exteriorPower_zero (d : Module.Dual R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x = 0 := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact contractLeft_algebraMap (Q := (0 : QuadraticForm R M)) d r

/-- **Contraction lowers the exterior degree by one**: it carries the `(n + 1)`-th exterior power
into the `n`-th. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih

/-- **Contraction of a wedge product of vectors** is the alternating sum of the contractions of
its factors: `d ⌋ (v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i d(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (v i)) •
        ExteriorAlgebra.ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hrem (i : Fin (n + 1)) : ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
        ExteriorAlgebra.ι R (v 0) *
          ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      ext j
      simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1),
      Finset.mul_sum]
    simp [hrem, pow_succ, sub_eq_add_neg, Matrix.vecTail, Fin.tail,
      Function.comp_def]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction against a functional commutes with an exterior-algebra map after pulling
back the functional. -/
theorem contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R N)) d (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f
        (contractLeft (Q := (0 : QuadraticForm R M)) (d ∘ₗ f) x) := by
  -- The exterior-algebra map is the zero-quadratic-form case of the Clifford-algebra map.
  exact CliffordAlgebra.contractLeft_map { f with map_app' := fun _ => rfl } d x

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction in degree at least the rank -/

variable [Module.Free R M] [Module.Finite R M]

/-- **A form of degree at least the rank is divisible by any vector `m` with `d m = 1`**: if
`d m = 1` and `finrank R M ≤ n`, then every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. -/
theorem eq_ι_mul_contractLeft_of_finrank_le {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {n : ℕ} (hn : Module.finrank R M ≤ n) {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    x = ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x := by
  -- `m ∧ x` lies above the rank, so it vanishes, and contracting it by `d` gives the claim.
  have h0 : ι R m * x = 0 := ZeroMemClass.coe_eq_zero.mpr <|
    exteriorPower.eq_zero_of_finrank_lt (1 + n) (by omega)
      ⟨_, SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) hx⟩
  have h := congrArg (contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  rwa [contractLeft_ι_mul, hdm, one_smul, map_zero, sub_eq_zero] at h

/-- **Forms killed by a contraction multiply to zero in degree at least the rank**: if `d m = 1`,
the forms `x ∈ ⋀ᵏ M` and `y ∈ ⋀ˡ M` satisfy `d ⌋ x = 0` and `d ⌋ y = 0`, and
`finrank R M ≤ k + l`, then `x ∧ y = 0`. -/
theorem mul_eq_zero_of_contractLeft_eq_zero {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {k l : ℕ} (hkl : Module.finrank R M ≤ k + l) {x y : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) (hy : y ∈ ⋀[R]^l M)
    (hdx : contractLeft (Q := (0 : QuadraticForm R M)) d x = 0)
    (hdy : contractLeft (Q := (0 : QuadraticForm R M)) d y = 0) : x * y = 0 := by
  rw [eq_ι_mul_contractLeft_of_finrank_le hdm hkl (SetLike.mul_mem_graded hx hy), contractLeft_mul,
    hdx, hdy, zero_mul, mul_zero, add_zero, mul_zero]

/-- **The square of a two-form in rank at most four.** If `d m = 1` and `finrank R M ≤ 4`, a
two-form `x` satisfies `x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. -/
theorem mul_self_eq_two_smul_mul_ι_mul_contractLeft {d : Module.Dual R M} {m : M}
    (hdm : d m = 1) (h4 : Module.finrank R M ≤ 4) {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^2 M) :
    x * x = 2 • (x * (ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x)) := by
  -- Write `x = m ∧ a + b` with `a = d ⌋ x`. Then `d ⌋ b = 0`, so `b ∧ b = 0` in rank at most
  -- four; also `(m ∧ a) ∧ (m ∧ a) = 0`, and the two-forms `m ∧ a` and `b` commute.
  -- The contraction `d ⌋ x` is a vector `a`.
  obtain ⟨a, ha⟩ : ∃ a, ι R a = contractLeft (Q := (0 : QuadraticForm R M)) d x :=
    ⟨_, ι_ιInv_of_mem_exteriorPower_one (contractLeft_mem_exteriorPower d (n := 1) hx)⟩
  rw [← ha]
  set g := ι R m * ι R a with hg
  have hgmem : g ∈ ⋀[R]^2 M :=
    SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) (ι_mem_exteriorPower_one a)
  -- The remainder `b = x - m ∧ a` is a two-form killed by `d`.
  set b := x - g with hb
  have hbmem : b ∈ ⋀[R]^2 M := sub_mem hx hgmem
  have hdb : contractLeft (Q := (0 : QuadraticForm R M)) d b = 0 := by
    have hda : contractLeft (Q := (0 : QuadraticForm R M)) d (ι R a) = 0 := by
      rw [ha, contractLeft_contractLeft]
    rw [hb, map_sub, hg, contractLeft_ι_mul, hdm, one_smul, hda, mul_zero, sub_zero, ha,
      sub_self]
  have hbb : b * b = 0 :=
    mul_eq_zero_of_contractLeft_eq_zero hdm (by omega) hbmem hbmem hdb hdb
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := R) a m
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι R m * (ι R a * ι R m) * ι R a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv : involute (Q := (0 : QuadraticForm R M)) b = b := by
    rw [involute_of_mem_exteriorPower hbmem]
    simp
  have hcomm : g * b = b * g := by
    rw [hg, mul_assoc, ι_mul_eq_involute_mul a b, hinv, ← mul_assoc, ι_mul_eq_involute_mul m b,
      hinv, mul_assoc]
  have hx' : x = b + g := (sub_add_cancel x g).symm
  rw [hx', add_mul, mul_add, mul_add, hbb, hgg, hcomm, add_mul, hgg, two_smul]
  abel

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Splitting off a free coordinate -/

/-- **Splitting off a free coordinate.** In the exterior algebra of `M × R`, with `e = (0, 1)`,
every element `z` is `a + e ∧ b`, where `a` is the image of `z` under `⋀ M × R → ⋀ M → ⋀ (M × R)`
and `b` is the image of the contraction of `z` by the second coordinate. -/
theorem map_inl_map_fst_add_ι_inr_mul_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.inl R M R) (map (LinearMap.fst R M R) z) +
        ι R (LinearMap.inr R M R 1) * map (LinearMap.inl R M R) (map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, mul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel
  | ι_mul z m ih =>
    -- Write `m = (m₁, 0) + m₂ e`; then `e ∧ e = 0` and `(m₁, 0) ∧ e = -(e ∧ (m₁, 0))`.
    have hm : ι R m = ι R (LinearMap.inl R M R m.1) + m.2 • ι R (LinearMap.inr R M R 1) := by
      rw [← map_smul, ← map_add]; congr 1; ext <;> simp
    have he := ι_sq_zero (R := R) (LinearMap.inr R M R (1 : R))
    have hc := eq_neg_of_add_eq_zero_right <|
      ι_add_mul_swap (R := R) (LinearMap.inr R M R (1 : R)) (LinearMap.inl R M R m.1)
    -- `left_induction` states the step with `CliffordAlgebra.ι 0`, which is `ι R` by definition.
    change _ = ι R m * z
    rw [contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, map_apply_ι]
    conv_rhs => rw [← ih, hm]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc, he, hc,
      smul_zero, add_zero, neg_mul, LinearMap.fst_apply, LinearMap.snd_apply]
    abel

/-! ### Contractions on `M × R` in the splitting `a + e ∧ b` -/

/-- The contraction by `φ.coprod ψ` on the image of `⋀ M` in `⋀ (M × N)` is the contraction
by `φ`. -/
theorem contractLeft_coprod_map_inl {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R M) (ψ : Module.Dual R N) (w : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R (M × N))) (φ.coprod ψ)
        (map (LinearMap.inl R M N) w) =
      map (LinearMap.inl R M N) (contractLeft (Q := (0 : QuadraticForm R M)) φ w) := by
  rw [contractLeft_map, LinearMap.coprod_inl]

/-- The contraction by `φ + x · snd` on `e ∧ w`, with `e = (0, 1)`: `d(e ∧ w) = x w - e ∧ d w`. -/
theorem contractLeft_coprod_ι_inr_mul (φ : Module.Dual R M) (x : R)
    (w : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x)) (ι R (LinearMap.inr R M R 1) * w) =
        x • w - ι R (LinearMap.inr R M R 1) *
          contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) w := by
  rw [contractLeft_ι_mul]
  simp

/-- Projection onto the first factor retracts the induced map of exterior algebras. -/
theorem leftInverse_map_fst_map_inl {N : Type*} [AddCommGroup N] [Module R N] :
    Function.LeftInverse (map (LinearMap.fst R M N)) (map (LinearMap.inl R M N)) :=
  leftInverse_map_iff.2 fun _ ↦ rfl

/-- The `⋀ M`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the `⋀ M`-component of `d z` is `d a + x b`. -/
theorem map_fst_contractLeft_coprod (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (φ.coprod (LinearMap.toSpanSingleton R R x)) z) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R) z) +
        x • map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z) := by
  conv_lhs => rw [← map_inl_map_fst_add_ι_inr_mul_contractLeft_snd z]
  rw [map_add, contractLeft_coprod_map_inl, contractLeft_coprod_ι_inr_mul,
    contractLeft_coprod_map_inl]
  simp only [LinearMap.coe_inr, map_add, map_sub, map_smul, map_mul, map_apply_ι,
    LinearMap.fst_apply, map_zero, zero_mul, sub_zero]
  rw [leftInverse_map_fst_map_inl, leftInverse_map_fst_map_inl]

/-- The `e`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the contraction `d b` is minus the
`e`-component of `d z`. -/
theorem contractLeft_map_fst_contractLeft_snd (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      -map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) z)) := by
  have hD := map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)
  rw [contractLeft_contractLeft, map_zero, map_zero, mul_zero, add_zero] at hD
  rw [← leftInverse_map_fst_map_inl (R := R) (M := M) (N := R) (contractLeft _ _),
    ← contractLeft_coprod_map_inl φ (LinearMap.toSpanSingleton R R x),
    hD, contractLeft_comm, map_neg]

end ExteriorAlgebra
end
end TAF_LiteralSource_0210

section TAF_LiteralSource_0211
/- Original module: PaperVerification.AlternatingFormsLefschetz -/


/-!
# Full symplectic prefix division

This file proves surjectivity of exterior multiplication by the standard
paired two-form from degree `d-1` to degree `d+1` in `2d` variables.  It is
the existence assertion in Lemma 3.1, for every size and every homogeneous
element, using the literal exterior operators.  The explicit Boolean
inverse is developed separately in `AlternatingFormsBoolean` and
`AlternatingFormsExteriorStraightening`.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open PaperVerification.Fermion
open PaperVerification.Fermion.Exterior
open scoped BigOperators

section DegreeLowering

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) R V)

local notation "E" => ExteriorAlgebra R V

theorem lowering_eq_zero_of_degree_lt_two {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (hr : r < 2) : lowering b w = 0 := by
  rw [lowering, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inr i))
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R V)) (b.coord (.inl i)) w) = 0
  rcases r with _ | r
  · have hz := TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inl i)) hw
    rw [hz, map_zero]
  · have hr0 : r = 0 := by omega
    subst r
    exact TauCeti.ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero
      (b.coord (.inr i))
      (TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower (b.coord (.inl i)) hw)

theorem lowering_mem_sub_two {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) :
    lowering b w ∈ ⋀[R]^(r - 2) V := by
  by_cases hr : r < 2
  · rw [lowering_eq_zero_of_degree_lt_two b hw hr]
    exact zero_mem _
  · have hr' : r = (r - 2) + 1 + 1 := by omega
    rw [lowering, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i hi
    change annihilation (b.coord (.inr i)) (annihilation (b.coord (.inl i)) w) ∈ _
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    apply TauCeti.ExteriorAlgebra.contractLeft_mem_exteriorPower
    simpa only [← hr'] using hw

theorem lowering_pow_mem {r : ℕ} {w : E} (hw : w ∈ ⋀[R]^r V) (j : ℕ) :
    (lowering b ^ j) w ∈ ⋀[R]^(r - 2 * j) V := by
  induction j with
  | zero => simpa using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert lowering_mem_sub_two b ih using 1 <;> congr 1 <;> omega

/-- Actual degree lowering proves nilpotence; it is not postulated as an
extra property of the exterior representation. -/
theorem lowering_pow_eq_zero_of_degree_lt {r : ℕ} {w : E}
    (hw : w ∈ ⋀[R]^r V) (j : ℕ) (hrj : r < 2 * j) : (lowering b ^ j) w = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    by_cases hr : r < 2 * j
    · rw [ih hr, map_zero]
    · exact lowering_eq_zero_of_degree_lt_two b (lowering_pow_mem b hw j) (by omega)

/-- The second orientation of the actual `sl₂` relations. -/
theorem swappedRaisingLowering :
    RaisingLowering (raising b) (lowering b) (-weight b) :=
  PaperVerification.Fermion.Exterior.loweringRaising b

/-- Exterior multiplication by the symplectic two-form is injective below
the middle degree.  The factorial hypothesis is sufficient over arbitrary
commutative coefficient rings and is automatic in characteristic zero
fields. -/
theorem raising_injective_below_middle
    (hfac : IsUnit ((Fintype.card ι).factorial : R))
    {r : ℕ} (hr : r < Fintype.card ι) {w : E}
    (hw : w ∈ ⋀[R]^r V) (hraise : raising b w = 0) : w = 0 := by
  let d := Fintype.card ι
  have hr2 : r ≤ 2 * d := by dsimp [d]; omega
  apply primitive_eq_zero_of_degree_gt (raising b) (lowering b) (-weight b)
    (swappedRaisingLowering b) d (2 * d - r) hfac (by dsimp [d]; omega)
    w hraise
  · rw [LinearMap.neg_apply, weight_homogeneous b r w hw, ← neg_smul]
    congr 1
    dsimp [d]
    rw [Nat.cast_sub hr2, Nat.cast_mul, Nat.cast_ofNat]
    ring
  · intro j hj
    apply lowering_pow_eq_zero_of_degree_lt b hw j
    omega

end DegreeLowering

section PrefixDivision

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis (ι ⊕ ι) K V)

local notation "E" => ExteriorAlgebra K V

/-- The standard paired two-form in the genuine second exterior power. -/
noncomputable def symplecticTwoForm : ⋀[K]^2 V :=
  ∑ i, exteriorPower.ιMulti K 2 ![b (.inl i), b (.inr i)]

theorem raising_eq_symplecticTwoForm_mul (w : E) :
    raising b w = (symplecticTwoForm b : E) * w := by
  simp only [raising, pairRaise, LinearMap.sum_apply, Module.End.mul_apply,
    creation_apply, symplecticTwoForm, Submodule.coe_sum,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, mul_one, Finset.sum_mul, mul_assoc]

/-- Exterior multiplication with its true homogeneous domain and codomain. -/
noncomputable def raisingDegreeMap (r : ℕ) : (⋀[K]^r V) →ₗ[K] ⋀[K]^(r + 2) V :=
  (raising b).restrict fun _ hw => raising_mem_add_two b hw

theorem raisingDegreeMap_injective
    (hfac : IsUnit ((Fintype.card ι).factorial : K))
    (r : ℕ) (hr : r < Fintype.card ι) :
    Function.Injective (raisingDegreeMap b r) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply raising_injective_below_middle b hfac hr (x - y).property
  rw [Submodule.coe_sub, map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hxy)

include b in
/-- The middle complementary exterior powers have the same dimension. -/
theorem prefix_wedge_dimensions (hd : 0 < Fintype.card ι) :
    Module.finrank K (⋀[K]^(Fintype.card ι - 1) V) =
      Module.finrank K (⋀[K]^(Fintype.card ι - 1 + 2) V) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  rw [exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis b, Fintype.card_sum]
  have hle : Fintype.card ι - 1 + 2 ≤ Fintype.card ι + Fintype.card ι := by omega
  have hsub : Fintype.card ι + Fintype.card ι - (Fintype.card ι - 1 + 2) =
      Fintype.card ι - 1 := by omega
  simpa only [hsub] using Nat.choose_symm hle

/-- The complete prefix map is an isomorphism, for every positive number
of pairs. -/
theorem prefix_wedge_bijective (hd : 0 < Fintype.card ι)
    (hfac : IsUnit ((Fintype.card ι).factorial : K)) :
    Function.Bijective (raisingDegreeMap b (Fintype.card ι - 1)) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  have hinj := raisingDegreeMap_injective b hfac (Fintype.card ι - 1) (by omega)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (prefix_wedge_dimensions b hd)).mp hinj⟩

/-- Lemma 3.1's division existence for every homogeneous prefix element,
including every squarefree monomial, over every characteristic-zero field.
No bound is imposed on the number of variables. -/
theorem prefix_division_exists [CharZero K] (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (symplecticTwoForm b : E) * η = (w : E) := by
  by_cases hd : 0 < Fintype.card ι
  · have hfac : IsUnit ((Fintype.card ι).factorial : K) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    let w' : ⋀[K]^(Fintype.card ι - 1 + 2) V :=
      ⟨w, by convert w.property using 1 <;> congr 1 <;> omega⟩
    obtain ⟨η, hη⟩ := (prefix_wedge_bijective b hd hfac).surjective w'
    refine ⟨η, ?_⟩
    rw [← raising_eq_symplecticTwoForm_mul]
    exact congrArg Subtype.val hη
  · have hd0 : Fintype.card ι = 0 := by omega
    have hw0 : (w : E) = 0 := homogeneous_eq_zero_of_card_lt b
      (Fintype.card ι + 1) (by simp [Fintype.card_sum, hd0]) w w.property
    exact ⟨0, by simp [hw0]⟩

/-- Prefix division remains inside the prefix variables after inclusion
in any larger vector space.  The witness is the image of an element of the
smaller exterior power, not an arbitrary ambient quotient representative. -/
theorem prefix_division_map_exists [CharZero K]
    {M : Type*} [AddCommGroup M] [Module K M] (φ : V →ₗ[K] M)
    (w : ⋀[K]^(Fintype.card ι + 1) V) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) V,
      (ExteriorAlgebra.map φ (symplecticTwoForm b) : ExteriorAlgebra K M) *
          ExteriorAlgebra.map φ η = ExteriorAlgebra.map φ w := by
  obtain ⟨η, hη⟩ := prefix_division_exists b w
  exact ⟨η, by simpa only [map_mul] using congrArg (ExteriorAlgebra.map φ) hη⟩

end PrefixDivision

section PrefixMonomials

variable {K M ι : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation of the formal paired generators at arbitrary ambient
vectors.  In the application the vectors are the first `2h` path variables. -/
noncomputable def pairedEvaluation (u v : ι → M) : (ι ⊕ ι → K) →ₗ[K] M :=
  (Pi.basisFun K (ι ⊕ ι)).constr K (Sum.elim u v)

@[simp] theorem pairedEvaluation_basis (u v : ι → M) (i : ι ⊕ ι) :
    pairedEvaluation u v (Pi.basisFun K (ι ⊕ ι) i) = Sum.elim u v i := by
  simp [pairedEvaluation]

/-- Evaluation carries the literal paired quadratic to the literal ambient
matching quadratic.  The finite sum is evaluated term by term. -/
theorem pairedEvaluation_symplectic (u v : ι → M) :
    ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm (Pi.basisFun K (ι ⊕ ι)) :
        ExteriorAlgebra K (ι ⊕ ι → K))=
      ∑ i,ExteriorAlgebra.ι K (u i)*ExteriorAlgebra.ι K (v i) := by
  simp only [symplecticTwoForm,Submodule.coe_sum,map_sum,
    exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ExteriorAlgebra.ιMulti_apply,List.ofFn_succ,List.ofFn_zero,
    List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_one,pairedEvaluation_basis,Sum.elim_inl,Sum.elim_inr,mul_one]

set_option maxHeartbeats 1000000 in
/-- The full squarefree-monomial assertion of Lemma 3.1, expressed without
an arbitrary choice of ordering of the odd and even halves.  The tuple may
even repeat variables; the alternating product then vanishes.  The witness
is explicitly required to use only the prescribed prefix variables. -/
theorem prefix_monomial_division (u v : ι → M)
    (a : Fin (Fintype.card ι + 1) → ι ⊕ ι) :
    ∃ η : ⋀[K]^(Fintype.card ι - 1) M,
      η ∈ LinearMap.range (exteriorPower.map (Fintype.card ι - 1) (pairedEvaluation u v)) ∧
      (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) * η =
        ExteriorAlgebra.ιMulti K (Fintype.card ι + 1) (Sum.elim u v ∘ a) := by
  let b := Pi.basisFun K (ι ⊕ ι)
  let w : ⋀[K]^(Fintype.card ι + 1) (ι ⊕ ι → K) :=
    exteriorPower.ιMulti K (Fintype.card ι + 1) (b ∘ a)
  let φ : (ι ⊕ ι → K) →ₗ[K] M := pairedEvaluation (K := K) u v
  obtain ⟨η, hη⟩ := prefix_division_map_exists b φ w
  let e : (⋀[K]^(Fintype.card ι - 1) (ι ⊕ ι → K)) →ₗ[K]
      (⋀[K]^(Fintype.card ι - 1) M) := exteriorPower.map (Fintype.card ι - 1) φ
  refine ⟨e η,LinearMap.mem_range_self e η,?_⟩
  change (∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i)) *
    (exteriorPower.map (Fintype.card ι - 1) φ η : ExteriorAlgebra K M)=_
  have hform := pairedEvaluation_symplectic (K := K) u v
  change (ExteriorAlgebra.map (pairedEvaluation (K := K) u v)
      (symplecticTwoForm b) : ExteriorAlgebra K M) *
        ExteriorAlgebra.map (pairedEvaluation (K := K) u v) η=
      ExteriorAlgebra.map (pairedEvaluation (K := K) u v) w at hη
  rw [hform] at hη
  simpa only [exteriorPower.coe_map, w, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Function.comp_def, b, φ,
    pairedEvaluation_basis] using hη

end PrefixMonomials

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0211

section TAF_LiteralSource_0212
/- Original module: PaperVerification.AlternatingFormsOddExteriorCutoff -/


/-!
# The actual exterior quotient in every degree above the odd middle

The first canonical form already kills every exterior degree greater than
`k+1` in `2k+1` variables.  An increasing word of that length has its first
`k+1` letters among the first `2k` variables.  The full symplectic-prefix
division theorem applies to precisely those letters; the complete remaining
suffix is retained.  Thus this cutoff concerns the generated exterior ideal,
not a polynomial presentation or an anticipated dimension formula.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K] {k r s : ℕ}

private theorem odd_long_prefix_bound
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) (i : Fin (k+1)) :
    (I.val (Fin.castAdd (r+1) i)).val<2*k := by
  have hi : Fin.castAdd (r+1) i < Fin.natAdd (k+1) (0 : Fin (r+1)) := by
    change i.val<k+1+0
    simpa only [Nat.add_zero] using i.isLt
  have hstrict := I.property hi
  have hlast := (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).isLt
  change (I.val (Fin.castAdd (r+1) i)).val<
    (I.val (Fin.natAdd (k+1) (0 : Fin (r+1)))).val at hstrict
  omega

set_option pp.all true in
/-- Normalize the finite prefix size before entering a dependent Plücker-index
context.  This is the same division theorem, with the cardinality of `Fin k`
written as `k`. -/
private theorem odd_prefix_division (u v : Fin k → (Fin (2*k+1) → K)) :
    ∀ b : Fin (k+1) → Fin k ⊕ Fin k,
      ∃ η : ⋀[K]^(k-1) (Fin (2*k+1) → K),
        η ∈ LinearMap.range (exteriorPower.map (k-1) (pairedEvaluation u v)) ∧
        (∑ j : Fin k, ExteriorAlgebra.ι K (u j) * ExteriorAlgebra.ι K (v j)) *
          (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
          ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
  have h := prefix_monomial_division (K := K) u v
  rw [Fintype.card_fin] at h
  exact h

/-- The literal increasing word is a multiple of the first canonical
quadratic, with every suffix letter preserved. -/
theorem odd_long_word_division
    (I : PluckerIndex (k+1+(r+1)) (2*k+1)) :
    ∃ a : ExteriorAlgebra K (Fin (2*k+1) → K),
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))) :
        ExteriorAlgebra K (Fin (2*k+1) → K))*a=
          indexExteriorWord (List.ofFn I.val) := by
  let z := Pi.basisFun K (Fin (2*k+1))
  let u : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathFirstLeft j)
  let v : Fin k → (Fin (2*k+1) → K) := fun j => z (oddPathMiddle j)
  let a : Fin (k+1) → Fin (2*k) := fun i =>
    ⟨(I.val (Fin.castAdd (r+1) i)).val,odd_long_prefix_bound I i⟩
  let b : Fin (k+1) → Fin k ⊕ Fin k := fun i => (evenOddPrefixEquiv k).symm (a i)
  have htuple : Sum.elim u v ∘ b=
      fun i => z (I.val (Fin.castAdd (r+1) i)) := by
    funext i
    have he : evenOddPrefixEquiv k (b i)=a i :=
      (evenOddPrefixEquiv k).apply_symm_apply (a i)
    change Sum.elim u v (b i)=_
    rcases hb : b i with j | j
    · rw [hb] at he
      change z (oddPathFirstLeft j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inl,a,oddPathFirstLeft] using congrArg Fin.val he
    · rw [hb] at he
      change z (oddPathMiddle j)=_
      congr 1
      apply Fin.ext
      simpa only [evenOddPrefixEquiv_inr,a,oddPathMiddle] using congrArg Fin.val he
  have hdiv := odd_prefix_division (K := K) u v
  obtain ⟨η,hηsupport,hη⟩ := hdiv b
  have hη' : (∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j)) *
      (η : ExteriorAlgebra K (Fin (2*k+1) → K)) =
      ExteriorAlgebra.ιMulti K (k+1) (Sum.elim u v ∘ b) := by
    exact hη
  have hform : (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))=
      ∑ j : Fin k,ExteriorAlgebra.ι K (u j)*ExteriorAlgebra.ι K (v j) := by
    simp only [oddPathFirstQuadratic,matchingQuadratic_coe,u,v]
  have hprefix :
      (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
        (η : ExteriorAlgebra K (Fin (2*k+1) → K))=
        indexExteriorWord (List.ofFn (fun i : Fin (k+1) => I.val (Fin.castAdd (r+1) i))) := by
    rw [hform,hη',htuple]
    simp only [ExteriorAlgebra.ιMulti_apply,indexExteriorWord,List.map_ofFn,z,
      List.map_map,Function.comp_def]
  let L := List.ofFn (fun i : Fin (r+1) => I.val (Fin.natAdd (k+1) i))
  refine ⟨(η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L,?_⟩
  change (oddPathFirstQuadratic (K := K) z : ExteriorAlgebra K (Fin (2*k+1) → K))*
    ((η : ExteriorAlgebra K (Fin (2*k+1) → K))*indexExteriorWord L)=_
  rw [←mul_assoc,hprefix,←indexExteriorWord_append]
  congr 1
  exact (List.ofFn_add (f := I.val)).symm

private theorem odd_exteriorDegreeRelations_eq_top_add
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (r : ℕ) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g
      (k+1+(r+1))=⊤ := by
  apply eq_top_iff.mpr
  rw [←(exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨I,rfl⟩
  change ((exteriorPluckerBasis (K := K) (k+1+(r+1)) (2*k+1) I) :
    ExteriorAlgebra K (Fin (2*k+1) → K))∈exteriorRelationIdeal _ g
  obtain ⟨a,ha⟩ := odd_long_word_division (K := K) I
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,0,?_⟩
  rw [zero_mul,add_zero,
    ←(twoForm_commute (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) a).eq,ha]
  rw [exteriorPluckerBasis_apply]
  simp only [indexExteriorWord,exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply,List.map_ofFn,List.map_map,Function.comp_def]

/-- Full high-degree vanishing for the actual generated exterior ideal.
The second quadratic may be arbitrary; no upper bound on `s` is imposed. -/
theorem odd_exteriorDegreeRelations_eq_top
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s=⊤ := by
  let r := s-(k+2)
  have he : s=k+1+(r+1) := by dsimp only [r]; omega
  rw [he]
  exact odd_exteriorDegreeRelations_eq_top_add g r

theorem odd_exteriorQuotientDegree_subsingleton
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Subsingleton (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s) := by
  change Subsingleton ((⋀[K]^s (Fin (2*k+1) → K))⧸exteriorDegreeRelations _ g s)
  rw [odd_exteriorDegreeRelations_eq_top g hs]
  infer_instance

theorem odd_exteriorQuotientDegree_finrank_eq_zero
    (g : ⋀[K]^2 (Fin (2*k+1) → K)) (hs : k+1<s) :
    Module.finrank K (ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) g s)=0 := by
  letI := odd_exteriorQuotientDegree_subsingleton g hs
  exact Module.finrank_zero_of_subsingleton

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0212

section TAF_LiteralSource_0213
/- Original module: PaperVerification.AlternatingFormsOddExteriorBasis -/


/-!
# The complete good-monomial exterior basis for the canonical odd pencil

The index inequalities are written without truncated subtraction, so they
retain their meaning in every degree, including degrees above the middle.
Degrees zero and one use the proved absence of quadratic-generated relations;
the middle range uses the actual linear Plücker comparison and lifted standard
basis; all higher degrees use the actual generated-ideal cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K]

/-- The printed good-index inequalities, in zero-based coordinates and with
the upper inequality moved across the subtraction. -/
def GoodOddIndex (k s : ℕ) :=
  {I : PluckerIndex s (2*k+1) // ∀ i,
    2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}

instance goodOddIndex_fintype (k s : ℕ) : Fintype (GoodOddIndex k s) := by
  classical
  unfold GoodOddIndex
  infer_instance

abbrev OddExteriorQuotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s

def goodOddBandEquiv (k t : ℕ) (hs : t+2≤k+1) :
    GoodOddIndex k (t+2) ≃
      BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) 1 where
  toFun I := ⟨fun _ => I.val.val,fun _ => I.val.property,
    (by
      intro j i
      have hi := I.property i
      constructor
      · exact hi.1
      · change (I.val.val i).val≤2*(k+1-(t+2)+i.val)
        omega),monotone_const⟩
  invFun C := ⟨⟨C.val 0,C.property.1 0⟩,by
    intro i
    have hi := C.property.2.1 0 i
    constructor
    · exact hi.1
    · have hi2 := hi.2
      change (C.val 0 i).val≤2*(k+1-(t+2)+i.val) at hi2
      change (C.val 0 i).val+2*(t+2)≤2*k+2+2*i.val
      omega⟩
  left_inv I := rfl
  right_inv C := by
    apply Subtype.ext
    funext j i
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]

private theorem odd_pairCoefficientForms (k : ℕ) :
    pairCoefficientForms (oddPluckerForms (K := K) k 0) (oddPluckerForms k 1)=
      oddPluckerForms k := by
  funext i
  fin_cases i <;> rfl

def oddExteriorLinearClass (k t : ℕ) :
    (⋀[K]^(t+2) (Fin (2*k+1) → K)) →ₗ[K]
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) :=
  (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal (t := t) (oddPluckerForms k))).toLinearMap.comp
    (exteriorPluckerCoordinates (t+2) (2*k+1))

theorem oddExteriorLinearClass_ker (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).ker=exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) (t+2) := by
  apply Submodule.ext
  intro x
  change Ideal.Quotient.mk
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (exteriorPluckerCoordinates (K := K) (t+2) (2*k+1) x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,← odd_pairCoefficientForms (K := K) k,
    exteriorCoordinates_mem_pairIdeal_iff,coefficientPairRelations_eq_exterior,
    oddPluckerForms_first,oddPluckerForms_second]

theorem oddExteriorLinearClass_range (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).range=oddPluckerDegree k t 1 := by
  rw [oddExteriorLinearClass,LinearMap.range_comp,exteriorPluckerCoordinates_range]
  rfl

def oddExteriorLinearPieceEquiv (k t : ℕ) :
    OddExteriorQuotientDegree (K := K) k (t+2) ≃ₗ[K]
      oddPluckerDegree (K := K) k t 1 :=
  (Submodule.quotEquivOfEq _ _ (oddExteriorLinearClass_ker k t).symm).trans
    ((oddExteriorLinearClass k t).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (oddExteriorLinearClass_range k t)))

theorem oddExteriorLinearPieceEquiv_mk (k t : ℕ)
    (x : ⋀[K]^(t+2) (Fin (2*k+1) → K)) :
    (oddExteriorLinearPieceEquiv k t (Submodule.Quotient.mk x) :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (exteriorPluckerCoordinates (t+2) (2*k+1) x) := by
  simp only [oddExteriorLinearPieceEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearEquiv.coe_ofEq_apply,
    LinearMap.quotKerEquivRange_apply_mk]
  rfl

def oddExteriorMiddleBasis [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (GoodOddIndex k (t+2)) K (OddExteriorQuotientDegree (K := K) k (t+2)) :=
  ((oddPluckerDegreeBasis k t hs 1).map (oddExteriorLinearPieceEquiv k t).symm).reindex
    (goodOddBandEquiv k t hs).symm

@[simp] theorem oddExteriorMiddleBasis_apply [CharZero K] (k t : ℕ) (hs : t+2≤k+1)
    (I : GoodOddIndex k (t+2)) :
    oddExteriorMiddleBasis (K := K) k t hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis (t+2) (2*k+1) I.val) := by
  apply (oddExteriorLinearPieceEquiv k t).injective
  apply Subtype.ext
  simp only [oddExteriorMiddleBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    Module.Basis.map_apply,LinearEquiv.apply_symm_apply,oddPluckerDegreeBasis_apply,
    oddExteriorLinearPieceEquiv_mk,exteriorPluckerCoordinates_basis,
    goodOddBandEquiv,chainPluckerProduct,Fin.prod_univ_one]
  rfl

def goodOddLowEquiv (k s : ℕ) (hs : s<2) : GoodOddIndex k s ≃ PluckerIndex s (2*k+1) where
  toFun I := I.val
  invFun I := ⟨I,by
    intro i
    have hi := i.isLt
    have hI := (I.val i).isLt
    constructor <;> omega⟩
  left_inv I := rfl
  right_inv I := rfl

def oddExteriorLowBasis (k s : ℕ) (hs : s<2) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) :=
  ((exteriorPluckerBasis s (2*k+1)).reindex (goodOddLowEquiv k s hs).symm).map
    ((exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s).quotEquivOfEqBot (exteriorDegreeRelations_eq_bot _ _ hs)).symm

@[simp] theorem oddExteriorLowBasis_apply (k s : ℕ) (hs : s<2) (I : GoodOddIndex k s) :
    oddExteriorLowBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  simp only [oddExteriorLowBasis,Module.Basis.map_apply,Module.Basis.reindex_apply,
    Equiv.symm_symm,goodOddLowEquiv,Submodule.quotEquivOfEqBot_symm_apply]
  rfl

theorem goodOddIndex_isEmpty (k s : ℕ) (hs : k+1<s) : IsEmpty (GoodOddIndex k s) := by
  refine ⟨fun I => ?_⟩
  have hpos : 0<s := by omega
  have h := (I.property (⟨0,hpos⟩ : Fin s)).2
  change (I.val.val ⟨0,hpos⟩).val+2*s≤2*k+2+2*0 at h
  omega

def oddExteriorHighBasis [CharZero K] (k s : ℕ) (hs : k+1<s) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) := by
  letI := goodOddIndex_isEmpty k s hs
  letI := odd_exteriorQuotientDegree_subsingleton
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) hs
  exact Module.Basis.empty _

@[simp] theorem oddExteriorHighBasis_apply [CharZero K] (k s : ℕ) (hs : k+1<s) (I : GoodOddIndex k s) :
    oddExteriorHighBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  exact (goodOddIndex_isEmpty k s hs).false I |>.elim

/-- The basis covers every degree and every odd ambient dimension. -/
def oddExteriorBasis [CharZero K] (k : ℕ) : (s : ℕ) →
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s)
  | 0 => oddExteriorLowBasis k 0 (by decide)
  | 1 => oddExteriorLowBasis k 1 (by decide)
  | t+2 => if hs : t+2≤k+1 then oddExteriorMiddleBasis k t hs
      else oddExteriorHighBasis k (t+2) (Nat.lt_of_not_ge hs)

@[simp] theorem oddExteriorBasis_apply [CharZero K] (k s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasis (K := K) k s I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  cases s with
  | zero => exact oddExteriorLowBasis_apply k 0 (by decide) I
  | succ s =>
      cases s with
      | zero => exact oddExteriorLowBasis_apply k 1 (by decide) I
      | succ t =>
          dsimp only [oddExteriorBasis]
          split_ifs with hs
          · exact oddExteriorMiddleBasis_apply k t hs I
          · exact oddExteriorHighBasis_apply k (t+2) (Nat.lt_of_not_ge hs) I

/-- The complete exterior-basis clause of Theorem 1.3, faithfully stated
using the actual generated-ideal quotient and the original exterior words.
The separate degeneration and Koszul clauses are not part of this statement. -/
theorem paper_theorem_1_3_exterior_basis [CharZero K] (k s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  refine ⟨oddExteriorBasis k s,?_⟩
  intro I
  rw [oddExteriorBasis_apply,exteriorPluckerBasis_apply]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0213

section TAF_LiteralSource_0214
/- Original module: PaperVerification.AlternatingFormsOddTransport -/


/-!
# Naturality of the displayed odd pencil

The two matching quadrics commute with every linear map.  A chosen basis
therefore identifies their degree quotients with the standard-coordinate
quotient through the actual exterior algebra functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem exteriorPower_map_exteriorPair (l : M →ₗ[K] N) (u v : M) :
    exteriorPower.map 2 l (exteriorPair u v) = exteriorPair (l u) (l v) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, exteriorPair_coe, map_mul,
    ExteriorAlgebra.map_apply_ι]

theorem matchingQuadratic_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : M →ₗ[K] N) (u v : ι → M) :
    exteriorPower.map 2 l (matchingQuadratic u v) =
      matchingQuadratic (l ∘ u) (l ∘ v) := by
  simp only [matchingQuadratic, map_sum, exteriorPower_map_exteriorPair,
    Function.comp_apply]

theorem oddPathFirstQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathFirstQuadratic (K := K) z) =
      oddPathFirstQuadratic (K := K) (l ∘ z) := by
  rw [oddPathFirstQuadratic, matchingQuadratic_map]
  rfl

theorem oddPathSecondQuadratic_map {k : ℕ} (l : M →ₗ[K] N)
    (z : Fin (2*k+1) → M) :
    exteriorPower.map 2 l (oddPathSecondQuadratic (K := K) z) =
      oddPathSecondQuadratic (K := K) (l ∘ z) := by
  rw [oddPathSecondQuadratic, matchingQuadratic_map]
  rfl

def standardBasisEquiv {n : ℕ} (b : Module.Basis (Fin n) K M) :
    (Fin n → K) ≃ₗ[K] M :=
  (Pi.basisFun K (Fin n)).equiv b (Equiv.refl (Fin n))

@[simp] theorem standardBasisEquiv_basisFun {n : ℕ}
    (b : Module.Basis (Fin n) K M) (i : Fin n) :
    standardBasisEquiv b (Pi.basisFun K (Fin n) i) = b i := by
  simp only [standardBasisEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

theorem oddPathFirstQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathFirstQuadratic (K := K) b := by
  rw [oddPathFirstQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

theorem oddPathSecondQuadratic_standardBasisEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) :
    exteriorPower.map 2 (standardBasisEquiv b).toLinearMap
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) =
      oddPathSecondQuadratic (K := K) b := by
  rw [oddPathSecondQuadratic_map]
  congr 1
  funext i
  exact standardBasisEquiv_basisFun b i

def oddExteriorBasisChangeEquiv {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s ≃ₗ[K]
    ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s :=
  exteriorQuotientDegreePencilEquiv (standardBasisEquiv b) _ _ _ _
    (by rw [oddPathFirstQuadratic_standardBasisEquiv,
      oddPathSecondQuadratic_standardBasisEquiv]) s

@[simp] theorem oddExteriorBasisChangeEquiv_mk {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ)
    (x : ⋀[K]^s (Fin (2*k+1) → K)) :
    oddExteriorBasisChangeEquiv b s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (exteriorPower.map s (standardBasisEquiv b).toLinearMap x) := by
  rw [oddExteriorBasisChangeEquiv, exteriorQuotientDegreePencilEquiv_mk]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0214

section TAF_LiteralSource_0215
/- Original module: PaperVerification.AlternatingFormsOddAbstractBasis -/


/-!
# The good exterior basis in arbitrary coordinates

This endpoint removes the choice of the standard coordinate vector space.
It covers every module with a basis of the requested size, every odd
dimension, and every exterior degree, and displays the original basis words.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] {k : ℕ}

def oddExteriorBasisAt (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s) :=
  (oddExteriorBasis k s).map (oddExteriorBasisChangeEquiv b s)

@[simp] theorem oddExteriorBasisAt_apply
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasisAt b s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) := by
  rw [oddExteriorBasisAt, Module.Basis.map_apply, oddExteriorBasis_apply,
    oddExteriorBasisChangeEquiv_mk, exteriorPluckerBasis_apply,
    exteriorPower.map_apply_ιMulti]
  congr 1
  apply congrArg (exteriorPower.ιMulti K s)
  funext i
  exact standardBasisEquiv_basisFun b (I.val.val i)

/-- The exterior-basis clause of Theorem 1.3 with its full basis-dependent
vector-space interpretation, including all boundary and vanishing degrees. -/
theorem paper_theorem_1_3_exterior_basis_with_basis
    (b : Module.Basis (Fin (2*k+1)) K M) (s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K
      (ExteriorQuotientDegree (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) s),
      ∀ I, B I = Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => b (I.val.val i))) :=
  ⟨oddExteriorBasisAt b s, oddExteriorBasisAt_apply b s⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0215

section TAF_LiteralSource_0216
/- Original module: PaperVerification.AlternatingFormsOddOrbitInterleaving -/


/-!
# The odd orbit normal form is the literal interleaved path pencil

The orbit calculation groups the `a` and `b` coordinates in two blocks.
The exterior straightening theorem interleaves them.  This file gives
the explicit permutation, identifies both quadratic generators including
their signs, and transports the complete good-monomial basis to the
actual orbit normal form in every exterior degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

/-- `aᵢ` occupies the odd position `2i+1` and `bⱼ` the even position `2j`. -/
def oddOrbitInterleave (t : ℕ) : OddOrbitMode t ≃ Fin (2*(t+1)+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr j =>
        have he : (2*j.val)%2=0 := by omega
        simp only [he, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv j := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

def oddOrbitInterleavedBasis (t : ℕ) :
    Module.Basis (Fin (2*(t+1)+1)) K (OddOrbitMode t → K) :=
  (Pi.basisFun K (OddOrbitMode t)).reindex (oddOrbitInterleave t)

theorem oddOrbitInterleavedBasis_at (t : ℕ) (i : OddOrbitMode t) :
    oddOrbitInterleavedBasis (K := K) t (oddOrbitInterleave t i) =
      Pi.basisFun K (OddOrbitMode t) i := by
  simp only [oddOrbitInterleavedBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply]

theorem oddOrbitInterleavedBasis_middle (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathMiddle i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inl i) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inl i)

theorem oddOrbitInterleavedBasis_first (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathFirstLeft i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.castSucc) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.castSucc)

theorem oddOrbitInterleavedBasis_second (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathSecondRight i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.succ) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.succ)

theorem exteriorPair_swap {M : Type*} [AddCommGroup M] [Module K M] (u v : M) :
    exteriorPair (K := K) u v = -exteriorPair v u := by
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

/-- The first orbit generator is exactly the second path generator. -/
theorem oddOrbitFirstForm_eq_path (t : ℕ) :
    oddOrbitFirstForm (K := K) t =
      oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitFirstForm, orbitIncidenceForm, oddPathSecondQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_middle,
    oddOrbitInterleavedBasis_second, exteriorPair]

/-- The second orbit generator is minus the first path generator.  The
sign is retained explicitly before comparing the generated ideals. -/
theorem oddOrbitSecondForm_eq_path (t : ℕ) :
    oddOrbitSecondForm (K := K) t =
      -oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitSecondForm, orbitIncidenceForm, oddPathFirstQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_first,
    oddOrbitInterleavedBasis_middle, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact exteriorPair_swap _ _

theorem quadraticSpan_swap_neg {M : Type*} [AddCommGroup M] [Module K M]
    (f g : ⋀[K]^2 M) :
    Submodule.span K ({f,g} : Set (⋀[K]^2 M)) =
      Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have hn : -f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) :=
        Submodule.subset_span (by simp)
      change f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M))
      have hnn := (Submodule.span K ({g,-f} : Set (⋀[K]^2 M))).neg_mem hn
      rw [neg_neg] at hnn
      exact hnn
    · rw [hx]
      exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.subset_span (by simp)
    · rw [hx]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))

theorem oddOrbit_quadraticSpan (t : ℕ) :
    Submodule.span K
      ({oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t),
        oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)} :
          Set (⋀[K]^2 (OddOrbitMode t → K))) =
      Submodule.span K ({oddOrbitFirstForm (K := K) t,oddOrbitSecondForm (K := K) t} :
        Set (⋀[K]^2 (OddOrbitMode t → K))) := by
  rw [oddOrbitFirstForm_eq_path, oddOrbitSecondForm_eq_path]
  exact quadraticSpan_swap_neg _ _

def oddOrbitQuotientDegreeEquiv (t s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)) s ≃ₗ[K]
    ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s :=
  exteriorQuotientDegreeGeneratorsEquiv _ _ _ _ (oddOrbit_quadraticSpan t) s

section CharacteristicZero

variable [CharZero K]

/-- The full good-word basis for the actual block orbit normal form. -/
def oddOrbitQuotientDegreeBasis (t s : ℕ) :
    Module.Basis (GoodOddIndex (t+1) s) K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) :=
  (oddExteriorBasisAt (oddOrbitInterleavedBasis (K := K) t) s).map (oddOrbitQuotientDegreeEquiv t s)

theorem oddOrbitQuotientDegreeBasis_apply (t s : ℕ) (I : GoodOddIndex (t+1) s) :
    oddOrbitQuotientDegreeBasis (K := K) t s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i))) := by
  rw [oddOrbitQuotientDegreeBasis, Module.Basis.map_apply, oddExteriorBasisAt_apply]
  simpa only [oddOrbitQuotientDegreeEquiv] using
    exteriorQuotientDegreeGeneratorsEquiv_mk
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t)
      (oddOrbit_quadraticSpan (K := K) t) s
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i)))

theorem oddOrbitQuotientDegree_finrank (t s : ℕ) :
    Module.finrank K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) =
      Fintype.card (GoodOddIndex (t+1) s) :=
  Module.finrank_eq_card_basis (oddOrbitQuotientDegreeBasis t s)

end CharacteristicZero

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0216

section TAF_LiteralSource_0217
/- Original module: PaperVerification.AlternatingFormsGoodPathBounds -/


/-!
# The exact good-index inequalities and binary strip bounds

The original exterior positions are shifted by one because the binary path
starts with a fixed up-step.  A selected position contributes a down-step.
The prefix count therefore counts indices `I_j+1<q` in a prefix of length
`q`.  The two inequalities below are exactly nonnegative height and the
upper strip bound, without truncated subtraction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.GoodPaths

/-- Number of selected original letters in the first `q` binary steps,
including the initial fixed up-step in the prefix length. -/
def selectedBefore {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (I i).val+1<q).card

theorem selectedBefore_le {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedBefore I q≤s := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin s)

/-- A strictly increasing list meets every prefix in an initial segment. -/
theorem lt_selectedBefore_iff {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) (i : Fin s) :
    i.val<selectedBefore I q ↔ (I i).val+1<q := by
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  have hb : (I b).val≤(I a).val := hI.monotone hba
  omega

/-- Just before a selected down-step, exactly its predecessors have occurred. -/
theorem selectedBefore_at {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+1)=i.val := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+1)=Finset.Iio i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    change (I j).val+1<(I i).val+1 ↔ j < i
    exact Nat.add_lt_add_iff_right.trans hI.lt_iff_lt
  rw [hf,Fin.card_Iio]

/-- Just after a selected down-step, it too has occurred. -/
theorem selectedBefore_after {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (i : Fin s) :
    selectedBefore I ((I i).val+2)=i.val+1 := by
  unfold selectedBefore
  have hf : (Finset.univ.filter fun j => (I j).val+1<(I i).val+2)=Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    have he : (I j).val≤(I i).val ↔ j ≤ i := hI.le_iff_le
    omega
  rw [hf,Fin.card_Iic]

/-- The literal down-step indicator at a binary position. -/
def selectedAt {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) : ℕ :=
  if ∃ i,(I i).val+1=q then 1 else 0

theorem selectedAt_le_one {s n : ℕ} (I : Fin s → Fin n) (q : ℕ) :
    selectedAt I q≤1 := by
  unfold selectedAt
  split_ifs <;> omega

/-- A prefix grows by precisely the selected-position indicator. -/
theorem selectedBefore_succ {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I (q+1)=selectedBefore I q+selectedAt I q := by
  by_cases hq : ∃ i,(I i).val+1=q
  · obtain ⟨i,rfl⟩ := hq
    rw [show (I i).val+1+1=(I i).val+2 by omega,
      selectedBefore_after hI i,selectedBefore_at hI i]
    simp [selectedAt]
  · have hf : (Finset.univ.filter fun i => (I i).val+1<q+1)=
        (Finset.univ.filter fun i => (I i).val+1<q) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hi : (I i).val+1≠q := fun he => hq ⟨i,he⟩
      omega
    simp only [selectedBefore,hf,selectedAt,if_neg hq,Nat.add_zero]

@[simp] theorem selectedBefore_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I 0=0 := by simp [selectedBefore]

@[simp] theorem selectedAt_zero {s n : ℕ} (I : Fin s → Fin n) :
    selectedAt I 0=0 := by simp [selectedAt]

/-- The final fixed up-step adds no selected position. -/
theorem selectedBefore_all {s n : ℕ} (I : Fin s → Fin n) :
    selectedBefore I (n+1)=s := by
  have h : ∀ i,(I i).val+1<n+1 := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

theorem selectedBefore_eq_card_of_ge {s n : ℕ} (I : Fin s → Fin n) (q : ℕ)
    (hq : n+1≤q) : selectedBefore I q=s := by
  have h : ∀ i,(I i).val+1<q := fun i => by have := (I i).isLt; omega
  simp [selectedBefore,h]

/-- Exact equivalence between the printed good-index bounds and all binary
prefix heights in the strip.  It holds in every parameter range. -/
theorem good_bounds_iff_prefix_strip (k s : ℕ) (I : Fin s → Fin (2*k+1))
    (hI : StrictMono I) :
    (∀ i,2*i.val≤(I i).val ∧ (I i).val+2*s≤2*k+2+2*i.val) ↔
    (∀ q,q≤2*k+3 → 2*selectedBefore I q≤q ∧
      q+2*s≤2*k+3+2*selectedBefore I q) := by
  constructor
  · intro h q hq
    have hc := selectedBefore_le I q
    constructor
    · by_cases hz : selectedBefore I q=0
      · omega
      · let i : Fin s := ⟨selectedBefore I q-1,by omega⟩
        have hi : i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := (lt_selectedBefore_iff hI q i).mp hi
        have hb := (h i).1
        dsimp only [i] at hb hpos
        omega
    · by_cases he : selectedBefore I q=s
      · omega
      · let i : Fin s := ⟨selectedBefore I q,by omega⟩
        have hi : ¬ i.val<selectedBefore I q := by dsimp [i]; omega
        have hpos := mt (lt_selectedBefore_iff hI q i).mpr hi
        have hb := (h i).2
        dsimp only [i] at hb hpos
        omega
  · intro h i
    have hlt := (I i).isLt
    have hlo := (h ((I i).val+2) (by omega)).1
    have hhi := (h ((I i).val+1) (by omega)).2
    rw [selectedBefore_after hI i] at hlo
    rw [selectedBefore_at hI i] at hhi
    constructor <;> omega

/-- The actual finite selected set of an increasing exterior word. -/
def selectedSet {s n : ℕ} (I : Fin s → Fin n) : Finset (Fin n) :=
  Finset.univ.image I

theorem selectedSet_card {s n : ℕ} {I : Fin s → Fin n} (hI : StrictMono I) :
    (selectedSet I).card=s := by
  rw [selectedSet,Finset.card_image_of_injective _ hI.injective,Finset.card_univ,
    Fintype.card_fin]

/-- Sorted lists and subsets of the same cardinality are genuinely equivalent. -/
def increasingSelectionEquiv (s n : ℕ) :
    {I : Fin s → Fin n // StrictMono I} ≃ {S : Finset (Fin n) // S.card=s} where
  toFun I := ⟨selectedSet I.val,selectedSet_card I.property⟩
  invFun S := ⟨S.val.orderEmbOfFin S.property,(S.val.orderEmbOfFin S.property).strictMono⟩
  left_inv I := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (selectedSet_card I.property)
      (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) I.property).symm
  right_inv S := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ S.val S.property

/-- Prefix counts agree with the literal selected set, so the preceding
strip characterization is a statement about the actual binary word. -/
theorem selectedBefore_eq_filter_card {s n : ℕ} {I : Fin s → Fin n}
    (hI : StrictMono I) (q : ℕ) :
    selectedBefore I q=((selectedSet I).filter fun x => x.val+1<q).card := by
  rw [selectedSet,Finset.filter_image]
  exact (Finset.card_image_of_injective _ hI.injective).symm

end PaperVerification.AlternatingForms.GoodPaths
end
end
end TAF_LiteralSource_0217

section TAF_LiteralSource_0218
/- Original module: PaperVerification.AlternatingFormsOddWalkCount -/


/-!
# The good odd exterior words count the paper's actual strip walks

An original exterior position `i` becomes downward step `i+1`.  Both
endpoints of a strip walk are upward steps, so every good downward set
of length `2*k+3` comes from exactly one increasing exterior word.
The proof constructs this equivalence using sorted finite sets.  It
therefore identifies the full good-word basis with the actual graph
walk count, including the degrees above the vanishing cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

open BooleanWalks

/-- The initial fixed up-step shifts every original exterior position by one. -/
def oddDownstepShift (k : ℕ) : Fin (2*k+1) ↪ Fin (2*k+3) where
  toFun i := ⟨i.val+1, by have := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have := congrArg Fin.val h
    change i.val+1=j.val+1 at this
    omega

def oddIndexDownset {k s : ℕ} (I : Fin s → Fin (2*k+1)) : Finset (Fin (2*k+3)) :=
  (GoodPaths.selectedSet I).map (oddDownstepShift k)

theorem oddIndexDownset_card {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) : (oddIndexDownset I).card=s := by
  rw [oddIndexDownset, Finset.card_map, GoodPaths.selectedSet_card hI]

theorem oddIndexDownset_prefix {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) (q : ℕ) :
    prefixCount (oddIndexDownset I) q = GoodPaths.selectedBefore I q := by
  rw [prefixCount, oddIndexDownset, Finset.filter_map, Finset.card_map]
  change ((GoodPaths.selectedSet I).filter (fun x => x.val+1<q)).card =
    GoodPaths.selectedBefore I q
  exact (GoodPaths.selectedBefore_eq_filter_card hI q).symm

def goodOddIndexToGoodSubset {k s : ℕ} (I : GoodOddIndex k s) :
    GoodSubset (2*k+3) s :=
  ⟨⟨oddIndexDownset I.val.val, oddIndexDownset_card I.val.property⟩, by
    intro q hq
    change 2*prefixCount (oddIndexDownset I.val.val) q≤q ∧
      q+2*s≤2*k+3+2*prefixCount (oddIndexDownset I.val.val) q
    rw [oddIndexDownset_prefix I.val.property]
    exact (GoodPaths.good_bounds_iff_prefix_strip k s I.val.val I.val.property).mp
      I.property q hq⟩

theorem goodOddIndexToGoodSubset_injective (k s : ℕ) :
    Function.Injective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro I J h
  have hs : oddIndexDownset I.val.val = oddIndexDownset J.val.val :=
    congrArg (fun S : GoodSubset (2*k+3) s => S.val.val) h
  have hi : GoodPaths.selectedSet I.val.val = GoodPaths.selectedSet J.val.val :=
    Finset.map_injective (oddDownstepShift k) hs
  apply Subtype.ext
  exact (GoodPaths.increasingSelectionEquiv s (2*k+1)).injective (Subtype.ext hi)

/-- A good downward set contains neither of the two endpoint steps. -/
theorem goodSubset_odd_interior {k s : ℕ} (S : GoodSubset (2*k+3) s)
    (j : Fin (2*k+3)) (hj : j∈S.val.val) :
    0<j.val ∧ j.val<2*k+2 := by
  have hfirst : (0 : Fin (2*k+3)) ∉ S.val.val := by
    intro hzero
    have hc := prefixCount_succ S.val.val 0
    have hd : selectedAt S.val.val 0 = 1 := by
      simpa only [Fin.val_zero, if_pos hzero] using
        selectedAt_position S.val.val (0 : Fin (2*k+3))
    have hc' : prefixCount S.val.val 1 = 1 := by
      simpa only [prefixCount_zero, hd, Nat.zero_add] using hc
    have hb : 2 * prefixCount S.val.val 1 ≤ 1 := (S.property 1 (by omega)).1
    rw [hc'] at hb
    norm_num at hb
  have hlast : (⟨2*k+2, by omega⟩ : Fin (2*k+3)) ∉ S.val.val := by
    intro hlast
    have hc := prefixCount_succ S.val.val (2*k+2)
    have hd := selectedAt_position S.val.val (⟨2*k+2, by omega⟩ : Fin (2*k+3))
    simp only [Fin.val_mk, if_pos hlast] at hd
    have ha := prefixCount_all S.val.val (2*k+3) le_rfl
    rw [S.val.property] at ha
    change prefixCount S.val.val (2*k+3) =
      prefixCount S.val.val (2*k+2) + selectedAt S.val.val (2*k+2) at hc
    rw [hd, ha] at hc
    have hb := (S.property (2*k+2) (by omega)).2
    omega
  have hj0 : j.val≠0 := by
    intro hz
    have he : j = (0 : Fin (2*k+3)) := Fin.ext hz
    exact hfirst (he ▸ hj)
  have hjlast : j.val≠2*k+2 := by
    intro hz
    have he : j = (⟨2*k+2, by omega⟩ : Fin (2*k+3)) := Fin.ext hz
    exact hlast (he ▸ hj)
  have hjlt := j.isLt
  omega

/-- Sort the downward steps and remove the initial fixed up-step. -/
def goodSubsetToOddIndex {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    Fin s → Fin (2*k+1) := fun i =>
  ⟨(S.val.val.orderEmbOfFin S.val.property i).val-1, by
    have h := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    omega⟩

theorem goodSubsetToOddIndex_strictMono {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    StrictMono (goodSubsetToOddIndex S) := by
  intro i j hij
  have hord := (S.val.val.orderEmbOfFin S.val.property).strictMono hij
  have hi := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property i)
  have hj := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property j)
  change (S.val.val.orderEmbOfFin S.val.property i).val <
    (S.val.val.orderEmbOfFin S.val.property j).val at hord
  change (S.val.val.orderEmbOfFin S.val.property i).val-1 <
    (S.val.val.orderEmbOfFin S.val.property j).val-1
  omega

theorem oddIndexDownset_goodSubsetToOddIndex {k s : ℕ}
    (S : GoodSubset (2*k+3) s) : oddIndexDownset (goodSubsetToOddIndex S)=S.val.val := by
  unfold oddIndexDownset GoodPaths.selectedSet
  rw [Finset.map_eq_image, Finset.image_image]
  have hf : (fun i => oddDownstepShift k (goodSubsetToOddIndex S i)) =
      S.val.val.orderEmbOfFin S.val.property := by
    funext i
    apply Fin.ext
    have hi := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    change (S.val.val.orderEmbOfFin S.val.property i).val-1+1 =
      (S.val.val.orderEmbOfFin S.val.property i).val
    omega
  simp only [Function.comp_def]
  rw [hf]
  exact Finset.image_orderEmbOfFin_univ S.val.val S.val.property

theorem goodSubsetToOddIndex_good {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    ∀ i, 2*i.val≤(goodSubsetToOddIndex S i).val ∧
      (goodSubsetToOddIndex S i).val+2*s≤2*k+2+2*i.val := by
  apply (GoodPaths.good_bounds_iff_prefix_strip k s (goodSubsetToOddIndex S)
    (goodSubsetToOddIndex_strictMono S)).mpr
  intro q hq
  rw [← oddIndexDownset_prefix (goodSubsetToOddIndex_strictMono S),
    oddIndexDownset_goodSubsetToOddIndex]
  exact S.property q hq

theorem goodOddIndexToGoodSubset_surjective (k s : ℕ) :
    Function.Surjective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro S
  refine ⟨⟨⟨goodSubsetToOddIndex S, goodSubsetToOddIndex_strictMono S⟩,
    goodSubsetToOddIndex_good S⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact oddIndexDownset_goodSubsetToOddIndex S

/-- Every good exterior word is precisely one bounded binary strip walk. -/
def goodOddIndexGoodSubsetEquiv (k s : ℕ) : GoodOddIndex k s ≃ GoodSubset (2*k+3) s :=
  Equiv.ofBijective goodOddIndexToGoodSubset
    ⟨goodOddIndexToGoodSubset_injective k s, goodOddIndexToGoodSubset_surjective k s⟩

theorem card_goodOddIndex_eq_paperWalkCount_of_le (k s : ℕ) (hs : s≤k+1) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  calc
    Fintype.card (GoodOddIndex k s) = Fintype.card (GoodSubset (2*k+3) s) :=
      Fintype.card_congr (goodOddIndexGoodSubsetEquiv k s)
    _ = StripWalks.walkCount (2*k+3-2*s) (2*k+3) :=
      card_goodSubset_eq_walkCount (2*k+3) s (by omega)
    _ = StripWalks.paperWalkCount (2*k+1) s := by
      unfold StripWalks.paperWalkCount
      congr 1 <;> omega

/-- A width-zero strip has no positive-length walk. -/
theorem stripWalkCount_zero_width (N : ℕ) (hN : 0<N) :
    StripWalks.walkCount 0 N=0 := by
  letI : Subsingleton (Fin (0+1)) := Fin.subsingleton_iff_le_one.mpr (by decide)
  letI : IsEmpty {p : (SimpleGraph.pathGraph (0+1)).Walk 0 (Fin.last 0) // p.length=N} :=
    ⟨fun p => by
      have hz := p.val.nil_of_subsingleton.length_eq_zero
      have hn := p.property
      omega⟩
  exact Fintype.card_of_isEmpty

theorem paperWalkCount_odd_above_cutoff (k s : ℕ) (hs : k+1<s) :
    StripWalks.paperWalkCount (2*k+1) s=0 := by
  unfold StripWalks.paperWalkCount
  rw [show 2*k+1+2-2*s=0 by omega]
  exact stripWalkCount_zero_width _ (by omega)

/-- The count equality is valid in every natural exterior degree. -/
theorem card_goodOddIndex_eq_paperWalkCount (k s : ℕ) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  by_cases hs : s≤k+1
  · exact card_goodOddIndex_eq_paperWalkCount_of_le k s hs
  · have hs' : k+1<s := by omega
    letI := goodOddIndex_isEmpty k s hs'
    rw [Fintype.card_of_isEmpty, paperWalkCount_odd_above_cutoff k s hs']

/-- The odd path pencil has exactly the paper's Hilbert function in all degrees. -/
theorem oddExteriorQuotientDegree_finrank_eq_paperWalkCount
    {K : Type*} [Field K] [CharZero K] (k s : ℕ) :
    Module.finrank K (OddExteriorQuotientDegree (K := K) k s) =
      StripWalks.paperWalkCount (2*k+1) s := by
  rw [Module.finrank_eq_card_basis (oddExteriorBasis (K := K) k s),
    card_goodOddIndex_eq_paperWalkCount]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0218

section TAF_LiteralSource_0219
/- Original module: PaperVerification.AlternatingFormsOddActualGeneric -/


/-!
# The actual odd generic quotient has the paper's complete walk series

This combines the explicit dominant orbit of the literal odd pencil, the
actual good exterior basis after its proved coordinate permutation, and
the bijection with the paper's bounded walks.  The single coefficient
polynomial controls every exterior degree simultaneously.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

theorem odd_actual_generic_hilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 → ∀ s : ℕ,
        Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s := by
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  obtain ⟨Q, hbase, hQ⟩ := oddOrbit_actual_hilbert_certificate (K := K) t
  refine ⟨Q, ?_, ?_⟩
  · intro hz
    exact hbase (by rw [hz, map_zero])
  · intro y hy s
    rw [hQ y hy s, oddOrbitQuotientDegree_finrank,
      card_goodOddIndex_eq_paperWalkCount]

theorem odd_actual_generic_paperHilbert (t : ℕ) :
    ∃ Q : MvPolynomial (OddOrbitSlot t ⊕ OddOrbitSlot t) K, Q ≠ 0 ∧
      ∀ y : (OddOrbitSlot t ⊕ OddOrbitSlot t) → K, eval y Q ≠ 0 →
        (∀ s : ℕ, Module.finrank K (ExteriorQuotientDegree
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
          (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) =
          StripWalks.paperWalkCount (2*(t+1)+1) s) ∧
        (∀ s : ℕ, t+2 < s →
          Module.finrank K (ExteriorQuotientDegree
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).1
            (orbitFormsFromCoordinates (oddOrbitExteriorBasis t) y).2 s) = 0) := by
  obtain ⟨Q, hQ, h⟩ := odd_actual_generic_hilbert (K := K) t
  refine ⟨Q, hQ, ?_⟩
  intro y hy
  refine ⟨h y hy, ?_⟩
  intro s hs
  rw [h y hy s, paperWalkCount_odd_above_cutoff (t+1) s (by omega)]

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0219

section TAF_LiteralSource_0220
/- Original module: PaperVerification.MatrixPowerSeriesResolvent -/


/-!
# Formal generating series of an actual finite transfer matrix

The coefficient of degree N is the actual matrix power T^N.  The resolvent
identity is proved coefficient by coefficient, with no convergence or
invertibility assumption on T.  A row certificate then determines a selected
entry of the inverse. This new source awaits compilation and audit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace PaperVerification.MatrixPowerSeries

variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- Every entry is the formal series of the corresponding entries of T^N. -/
def seriesMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  Matrix.of fun i j ↦ PowerSeries.mk fun N ↦ (T^N) i j

@[simp] theorem coeff_seriesMatrix (T : Matrix I I R) (N : ℕ) (i j : I) :
    PowerSeries.coeff N (seriesMatrix T i j)=(T^N) i j :=
  by simp only [seriesMatrix,Matrix.of_apply,PowerSeries.coeff_mk]

/-- The actual matrix I-zT over the formal power-series ring. -/
def resolventMatrix (T : Matrix I I R) : Matrix I I (PowerSeries R) :=
  1-(PowerSeries.X : PowerSeries R) • T.map (PowerSeries.C (R := R))

theorem series_equation (T : Matrix I I R) (i j : I) :
    seriesMatrix T i j-PowerSeries.X*
        (∑ k,PowerSeries.C (T i k)*seriesMatrix T k j)=
      PowerSeries.C ((1 : Matrix I I R) i j) := by
  apply PowerSeries.ext
  intro N
  cases N with
  | zero => simp [seriesMatrix]
  | succ N =>
      simp [coeff_seriesMatrix,PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul,pow_succ',Matrix.mul_apply]

/-- The coefficient-defined series is a right inverse of the actual resolvent. -/
theorem resolvent_mul_series (T : Matrix I I R) :
    resolventMatrix T*seriesMatrix T=1 := by
  rw [resolventMatrix,sub_mul,one_mul,Matrix.smul_mul]
  apply Matrix.ext
  intro i j
  change seriesMatrix T i j-PowerSeries.X*
      ((T.map (PowerSeries.C (R := R))*seriesMatrix T) i j)=
        (1 : Matrix I I (PowerSeries R)) i j
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [series_equation]
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

/-- A row certificate computes an inverse entry by associativity of the
actual finite matrix product. It is not a determinant or inverse assumption. -/
theorem row_certificate_entry (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first : I)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D) (last : I) :
    D*seriesMatrix T first last=row last := by
  have h := congrFun (Matrix.vecMul_vecMul row (resolventMatrix T) (seriesMatrix T)) last
  rw [hrow,resolvent_mul_series,Matrix.single_vecMul,Matrix.vecMul_one] at h
  exact h

/-- A unit-constant row certificate gives the entire formal inverse entry. -/
theorem series_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1) :
    seriesMatrix T first last=PowerSeries.X^height*PowerSeries.invOfUnit D 1 := by
  have hentry := row_certificate_entry T row D first hrow last
  rw [hlast] at hentry
  calc
    seriesMatrix T first last = 1*seriesMatrix T first last := (one_mul _).symm
    _ = (PowerSeries.invOfUnit D 1*D)*seriesMatrix T first last := by
      rw [PowerSeries.invOfUnit_mul D 1 hD]
    _ = PowerSeries.invOfUnit D 1*(D*seriesMatrix T first last) := mul_assoc _ _ _
    _ = PowerSeries.invOfUnit D 1*PowerSeries.X^height := by rw [hentry]
    _ = PowerSeries.X^height*PowerSeries.invOfUnit D 1 := mul_comm _ _

/-- All coefficients, including the unbounded length parameter, follow from
the formal row certificate. -/
theorem power_entry_of_row_certificate (T : Matrix I I R) (row : I → PowerSeries R)
    (D : PowerSeries R) (first last : I) (height : ℕ)
    (hrow : row ᵥ* resolventMatrix T=Pi.single first D)
    (hlast : row last=PowerSeries.X^height) (hD : PowerSeries.constantCoeff D=1)
    (s : ℕ) :
    (T^(s+height)) first last=PowerSeries.coeff s (PowerSeries.invOfUnit D 1) := by
  have h := congrArg (PowerSeries.coeff (s+height))
    (series_entry_of_row_certificate T row D first last height hrow hlast hD)
  rwa [coeff_seriesMatrix,PowerSeries.coeff_X_pow_mul] at h

end PaperVerification.MatrixPowerSeries
end
end
end TAF_LiteralSource_0220

section TAF_LiteralSource_0221
/- Original module: PaperVerification.PowerSeriesInverseDeterminant -/


/-!
# The exact Hessenberg determinant for a reciprocal coefficient

The finite coefficient matrix of multiplication by a unit-constant power
series is lower triangular with determinant one.  Its first inverse column
is the coefficient vector of the reciprocal.  The adjugate formula gives
the Hessenberg determinant, including the zero-size case and every sign.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical

namespace PaperVerification.PowerSeriesInverseDeterminant

variable {R : Type*} [CommRing R]

def coefficientTriangular (φ : PowerSeries R) (s : ℕ) :
    Matrix (Fin (s+1)) (Fin (s+1)) R :=
  fun i j => if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) φ else 0

theorem coefficientTriangular_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    (coefficientTriangular φ s).det = 1 := by
  have hl : (coefficientTriangular φ s).IsLowerTriangular := by
    intro i j hij
    change (if j.val ≤ i.val then _ else (0 : R)) = 0
    exact if_neg (by exact Nat.not_le_of_gt hij)
  rw [Matrix.det_of_isLowerTriangular _ hl]
  simp only [coefficientTriangular, le_refl, if_true, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ, Finset.prod_const_one]

theorem coefficientTriangular_mulVec (φ ψ : PowerSeries R) (s : ℕ) (i : Fin (s+1)) :
    (coefficientTriangular φ s *ᵥ (fun j => PowerSeries.coeff j.val ψ)) i =
      PowerSeries.coeff i.val (ψ*φ) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [coefficientTriangular, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a ψ * PowerSeries.coeff b φ) i.val]
  apply Finset.sum_bij (fun j hj => j.val)
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h)
  · intro j hj l hl h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, by have hi := i.isLt; omega⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ hj'⟩
  · intro j hj
    exact mul_comm _ _

theorem coefficientTriangular_inverse_column (φ : PowerSeries R)
    (hφ : φ.constantCoeff = 1) (s : ℕ) :
    coefficientTriangular φ s *ᵥ
      (fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)) = Pi.single 0 1 := by
  funext i
  rw [coefficientTriangular_mulVec, PowerSeries.invOfUnit_mul φ 1 hφ, PowerSeries.coeff_one]
  by_cases hi : i = 0
  · subst i
    simp
  · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi, hiv, Pi.single_apply, Ne.symm hi]

/-- The literal cofactor matrix, with the row and column signs distributed
so that alternating reciprocal coefficients become unsigned entries. -/
def inverseCoefficientMatrix (φ : PowerSeries R) (s : ℕ) : Matrix (Fin s) (Fin s) R :=
  fun i j => (-1 : R)^i.val * ((-1 : R)^(j.val+1) *
    (if i.val ≤ j.val+1 then PowerSeries.coeff (j.val+1-i.val) φ else 0))

theorem sign_products (s : ℕ) :
    (∏ i : Fin s, (-1 : R)^i.val) * (∏ i : Fin s, (-1 : R)^(i.val+1)) = (-1 : R)^s := by
  rw [← Finset.prod_mul_distrib]
  have hi (i : Fin s) : (-1 : R)^i.val * (-1 : R)^(i.val+1) = -1 := by
    rw [← pow_add, show i.val+(i.val+1)=2*i.val+1 by omega, pow_add, pow_mul]
    simp
  simp_rw [hi]
  simp

theorem inverseCoefficientMatrix_det (φ : PowerSeries R) (s : ℕ) :
    (inverseCoefficientMatrix φ s).det = (-1 : R)^s *
      ((coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc).det := by
  let B := (coefficientTriangular φ s).submatrix Fin.succ Fin.castSucc
  have he : inverseCoefficientMatrix φ s =
      Matrix.of (fun i j : Fin s => (-1 : R)^i.val *
        (Matrix.of (fun l r : Fin s => (-1 : R)^(r.val+1) * Bᵀ l r)) i j) := by
    ext i j
    rfl
  rw [he, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc, sign_products,
    Matrix.det_transpose]

/-- The reciprocal coefficient equals a genuine finite determinant.  The
proof uses only actual multiplication coefficients and the adjugate identity. -/
theorem coeff_inverse_eq_det (φ : PowerSeries R) (hφ : φ.constantCoeff = 1) (s : ℕ) :
    PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = (inverseCoefficientMatrix φ s).det := by
  let T := coefficientTriangular φ s
  let v : Fin (s+1) → R := fun j => PowerSeries.coeff j.val (PowerSeries.invOfUnit φ 1)
  have hv : T *ᵥ v = Pi.single 0 1 := coefficientTriangular_inverse_column φ hφ s
  have hd : T.det = 1 := coefficientTriangular_det φ hφ s
  have he := congrArg (fun w : Fin (s+1) → R => T.adjugate *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hd, one_smul,
    Matrix.one_mulVec, Matrix.mulVec_single_one] at he
  have hc := congrFun he (Fin.last s)
  change PowerSeries.coeff s (PowerSeries.invOfUnit φ 1) = T.adjugate (Fin.last s) 0 at hc
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hc
  simp only [Fin.val_zero, Fin.val_last, Nat.zero_add, Fin.zero_succAbove,
    Fin.succAbove_last] at hc
  rw [inverseCoefficientMatrix_det]
  exact hc

end PaperVerification.PowerSeriesInverseDeterminant
end
end
end TAF_LiteralSource_0221


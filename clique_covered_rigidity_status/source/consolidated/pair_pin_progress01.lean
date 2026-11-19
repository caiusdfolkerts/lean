module
import verification.internal.checkpoint
import verification.internal.extract
public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

set_option Elab.async false

section BundlePart0
/- Source: Papers/RigidityZheng_Specification.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Specification.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Module visibility and import paths adapted; umbrella Mathlib imports
replaced by the definitions and tactics used in this file.
-/


@[expose] public section

/-!
# Body--pin incidence and partition capacity

This file defines finite loopless body--pin incidences, the capped bundle
capacity, and the partition condition.
-/

namespace RB31E2E

/-- The capped rank contribution of a bundle of body--pin occurrences. -/
def pinCapacity : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 6

/--
A finite loopless body--pin multigraph represented by a finite type of
pin occurrences and its two distinct body endpoints.  Using occurrences
instead of quotient-valued multiedges keeps every pin's provenance.
-/
structure BodyPinIncidence where
  Body : Type
  Pin : Type
  bodyFinite : Fintype Body
  pinFinite : Fintype Pin
  bodyDecidableEq : DecidableEq Body
  pinDecidableEq : DecidableEq Pin
  left : Pin → Body
  right : Pin → Body
  loopless : ∀ e, left e ≠ right e

attribute [instance] BodyPinIncidence.bodyFinite
attribute [instance] BodyPinIncidence.pinFinite
attribute [instance] BodyPinIncidence.bodyDecidableEq
attribute [instance] BodyPinIncidence.pinDecidableEq

/-- Multiplicity of pins whose unordered endpoints lie in `A` and `B`. -/
def BodyPinIncidence.crossingMultiplicity
    (H : BodyPinIncidence) (A B : Finset H.Body) : ℕ :=
  (Finset.univ.filter fun e =>
    (H.left e ∈ A ∧ H.right e ∈ B) ∨
    (H.left e ∈ B ∧ H.right e ∈ A)).card

/-- Capacity of one pair of disjoint body sets. -/
def BodyPinIncidence.crossingCapacity
    (H : BodyPinIncidence) (A B : Finset H.Body) : ℕ :=
  pinCapacity (H.crossingMultiplicity A B)

/--
Multiplicity of the pin bundle between two labelled blocks.  The
definition is symmetric in `i` and `j`; the pins themselves remain an
occurrence type, so no provenance is lost by aggregation.
-/
def BodyPinIncidence.bundleMultiplicity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) : ℕ :=
  (Finset.univ.filter fun e =>
    (π (H.left e) = i ∧ π (H.right e) = j) ∨
    (π (H.left e) = j ∧ π (H.right e) = i)).card

/-- Capacity of the pin bundle joining two labelled blocks. -/
def BodyPinIncidence.bundleCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) : ℕ :=
  pinCapacity (H.bundleMultiplicity π i j)

/--
Multiplicity indexed by an unordered pair of block labels.  Diagonal
pairs are allowed at this level and are discarded by
`partitionCapacity`.
-/
def BodyPinIncidence.unorderedBundleMultiplicity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (b : Sym2 (Fin t)) : ℕ :=
  (Finset.univ.filter fun e => s(π (H.left e), π (H.right e)) = b).card

/--
The capacity sum over unordered distinct block pairs.  This is the
literal left hand side of the body--pin partition conjecture.
-/
def BodyPinIncidence.partitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  ∑ b ∈ (⊤ : SimpleGraph (Fin t)).edgeFinset,
    pinCapacity (H.unorderedBundleMultiplicity π b)

/--
The capacity sum over ordered distinct block pairs.  Each unordered
pair occurs twice.  This convention avoids making an arbitrary order
part of a set partition.
-/
def BodyPinIncidence.orderedPartitionCapacity
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  ∑ i : Fin t, ∑ j ∈ Finset.univ.erase i, H.bundleCapacity π i j

/--
The body--pin partition condition, expressed through surjective block
labels.  Surjectivity says that all `t` labels are actual blocks.  For
an empty body type the sole zero-block partition is included and the
natural-number right hand side is zero.
-/
def BodyPinIncidence.PartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    6 * (t - 1) ≤ H.partitionCapacity π

/-- The exactly doubled, ordered-pair audit form of the same condition. -/
def BodyPinIncidence.OrderedPartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    12 * (t - 1) ≤ H.orderedPartitionCapacity π

theorem BodyPinIncidence.bundleMultiplicity_comm
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.bundleMultiplicity π i j = H.bundleMultiplicity π j i := by
  simp only [bundleMultiplicity, or_comm]

theorem BodyPinIncidence.bundleCapacity_comm
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.bundleCapacity π i j = H.bundleCapacity π j i := by
  simp only [bundleCapacity, H.bundleMultiplicity_comm π i j]

end RB31E2E


end
end BundlePart0

#checked_checkpoint ".lake/checkpoints/attempt_01/block_001/Consolidated/PairPinProgress01.olean" record ".lake/reports/audit/current/progress_attempt_01/checkpoint_001.json"


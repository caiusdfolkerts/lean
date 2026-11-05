module
public import consolidated.pair_pin_progress01
import all consolidated.pair_pin_progress01
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

section BundlePart1
/- Source: Papers/RigidityDefectValues.lean -/




@[expose] public section

namespace Papers.Rigidity

open RB31E2E
open scoped Classical

/-- Every finite partition capacity is within `D` of six degrees of freedom
per non-grounded block. Surjectivity includes exactly the used blocks. -/
def PartitionDefectAtMost (H : BodyPinIncidence) (D : ℕ) : Prop :=
  ∀ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π →
    6 * (t - 1) ≤ H.partitionCapacity π + D

namespace GenericPinIdeal
noncomputable section

/-- The nonnegative maximum of all genuine partition defects. Every
finite partition occurs, and zero is supplied by the one-block partition. -/
def partitionDefectMaximum (H : BodyPinIncidence) : ℕ :=
  Nat.findGreatest
    (fun d => ∃ (t : ℕ) (π : H.Body → Fin t),
      Function.Surjective π ∧ d = 6 * (t - 1) - H.partitionCapacity π)
    (6 * (Fintype.card H.Body - 1))

theorem partition_defect_le_maximum (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) (hπ : Function.Surjective π) :
    6 * (t - 1) - H.partitionCapacity π ≤ partitionDefectMaximum H := by
  have ht : t ≤ Fintype.card H.Body := by
    simpa using Fintype.card_le_of_surjective π hπ
  exact Nat.le_findGreatest (by omega) ⟨t, π, hπ, rfl⟩

theorem partitionDefectMaximum_is_bound (H : BodyPinIncidence) :
    PartitionDefectAtMost H (partitionDefectMaximum H) := by
  intro t π hπ
  have h := partition_defect_le_maximum H π hπ
  omega

theorem partitionDefectMaximum_attained (H : BodyPinIncidence) (root : H.Body) :
    ∃ (t : ℕ) (π : H.Body → Fin t), Function.Surjective π ∧
      partitionDefectMaximum H = 6 * (t - 1) - H.partitionCapacity π := by
  have hconst : Function.Surjective (fun _ : H.Body => (0 : Fin 1)) := by
    intro i
    exact ⟨root, Subsingleton.elim _ _⟩
  have hzero : 0 = 6 * (1 - 1) - H.partitionCapacity (fun _ : H.Body => (0 : Fin 1)) := by simp
  exact Nat.findGreatest_spec
    (P := fun d => ∃ (t : ℕ) (π : H.Body → Fin t),
      Function.Surjective π ∧ d = 6 * (t - 1) - H.partitionCapacity π)
    (Nat.zero_le _) ⟨1, _, hconst, hzero⟩


end
end GenericPinIdeal
end Papers.Rigidity

end
end BundlePart1

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_002/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_002.json"

section BundlePart2
/- Source: Papers/RigidityZheng_Combinatorics_BodyPinCapacity.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/BodyPinCapacity.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Body--pin bundle capacity

Elementary facts about the `0,3,5,6` capacity table and the agreement
between occurrence-level unordered bundles and their oriented form.
-/

namespace RB31E2E

@[simp] theorem pinCapacity_zero : pinCapacity 0 = 0 := rfl
@[simp] theorem pinCapacity_one : pinCapacity 1 = 3 := rfl
@[simp] theorem pinCapacity_two : pinCapacity 2 = 5 := rfl

theorem pinCapacity_of_three_le {m : ℕ} (hm : 3 ≤ m) : pinCapacity m = 6 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity] at hm ⊢

theorem pinCapacity_le_six (m : ℕ) : pinCapacity m ≤ 6 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]

theorem pinCapacity_le_two_mul_add_one (m : ℕ) :
    pinCapacity m ≤ 2 * m + 1 := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]
  all_goals omega

theorem pinCapacity_le_three_mul (m : ℕ) : pinCapacity m ≤ 3 * m := by
  rcases m with _ | _ | _ | m <;> simp [pinCapacity]
  all_goals omega

theorem pinCapacity_eq_two_mul_add_one_of_one_or_two
    {m : ℕ} (hm : m = 1 ∨ m = 2) :
    pinCapacity m = 2 * m + 1 := by
  rcases hm with rfl | rfl <;> decide

/--
If `s` nonempty fine block-pairs carry `M` pins and every such pair
carries one or two pins, then aggregation into one capped bundle cannot
exceed the unaggregated `2M+s` budget.
-/
theorem pinCapacity_le_unaggregated (M s : ℕ)
    (hLower : s ≤ M) (hUpper : M ≤ 2 * s) :
    pinCapacity M ≤ 2 * M + s := by
  rcases M with _ | _ | _ | M <;> simp [pinCapacity]
  all_goals omega

theorem BodyPinIncidence.unorderedBundleMultiplicity_mk
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t) (i j : Fin t) :
    H.unorderedBundleMultiplicity π s(i, j) = H.bundleMultiplicity π i j := by
  unfold unorderedBundleMultiplicity bundleMultiplicity
  congr 1

end RB31E2E


end
end BundlePart2

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_003/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_003.json"

section BundlePart3
/- Source: Papers/RigidityZheng_Combinatorics_BodyPinFinpartition.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/BodyPinFinpartition.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Body--pin capacities indexed by ordinary finite partitions

The specification uses surjective labels `Body → Fin t`.  This file
proves that the same condition can be stated intrinsically using
`Finpartition univ`.  The constructions also cover the empty body type:
then both the label type and the finpartition have zero blocks.
-/

namespace RB31E2E

namespace BodyPinIncidence

/-- Bundle multiplicity for an arbitrary finite label type. -/
def bundleMultiplicityOn (H : BodyPinIncidence) {I : Type*} [DecidableEq I]
    (label : H.Body → I) (b : Sym2 I) : ℕ :=
  (Finset.univ.filter fun e => s(label (H.left e), label (H.right e)) = b).card

/-- Unordered capacity for an arbitrary finite label type. -/
def capacityOn (H : BodyPinIncidence) {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : ℕ :=
  ∑ b ∈ (⊤ : SimpleGraph I).edgeFinset,
    pinCapacity (H.bundleMultiplicityOn label b)

theorem bundleMultiplicityOn_fin {t : ℕ} (H : BodyPinIncidence)
    (label : H.Body → Fin t) (b : Sym2 (Fin t)) :
    H.bundleMultiplicityOn label b = H.unorderedBundleMultiplicity label b := rfl

theorem capacityOn_fin {t : ℕ} (H : BodyPinIncidence) (label : H.Body → Fin t) :
    H.capacityOn label = H.partitionCapacity label := rfl

/-- An equivalence induces an equivalence on unordered pairs. -/
def sym2Equiv {I K : Type*} (e : I ≃ K) : Sym2 I ≃ Sym2 K where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := Sym2.ind (by simp)
  right_inv := Sym2.ind (by simp)

@[simp]
theorem sym2Equiv_apply {I K : Type*} (e : I ≃ K) (b : Sym2 I) :
    sym2Equiv e b = b.map e := rfl

theorem bundleMultiplicityOn_comp_equiv
    (H : BodyPinIncidence) {I K : Type*} [DecidableEq I] [DecidableEq K]
    (e : I ≃ K) (label : H.Body → I) (b : Sym2 I) :
    H.bundleMultiplicityOn (e ∘ label) (sym2Equiv e b) =
      H.bundleMultiplicityOn label b := by
  unfold bundleMultiplicityOn
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro pin _
  change Sym2.map e s(label (H.left pin), label (H.right pin)) = Sym2.map e b ↔ _
  exact (Sym2.map.injective e.injective).eq_iff

theorem capacityOn_comp_equiv
    (H : BodyPinIncidence) {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : I ≃ K) (label : H.Body → I) :
    H.capacityOn (e ∘ label) = H.capacityOn label := by
  unfold capacityOn
  symm
  apply Finset.sum_equiv (sym2Equiv e)
  · intro b
    simp only [sym2Equiv_apply, SimpleGraph.mem_edgeFinset]
    rw [SimpleGraph.edgeSet_top, SimpleGraph.edgeSet_top]
    exact not_congr (Sym2.isDiag_map e.injective).symm
  · intro b hb
    rw [bundleMultiplicityOn_comp_equiv]

/-- The block of an element as a member of the finite type of parts. -/
def finpartitionBlock {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) (a : A) : P.parts :=
  ⟨P.part a, P.part_mem.mpr (by simp)⟩

theorem finpartitionBlock_surjective {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) :
    Function.Surjective (finpartitionBlock P) := by
  intro X
  obtain ⟨a, ha, hpart⟩ := P.part_surjOn X.property
  exact ⟨a, Subtype.ext hpart⟩

/-- Multiplicity of an unordered pair of ordinary finpartition blocks. -/
def finpartitionBundleMultiplicity (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) (b : Sym2 P.parts) : ℕ :=
  H.bundleMultiplicityOn (finpartitionBlock P) b

/-- Total capped capacity over unordered distinct blocks of `P`. -/
def finpartitionCapacity (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) : ℕ :=
  H.capacityOn (finpartitionBlock P)

theorem finpartitionBlock_eq_iff_mem {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finpartition (Finset.univ : Finset A)) (a : A) (X : P.parts) :
    finpartitionBlock P a = X ↔ a ∈ X.1 := by
  rw [Subtype.ext_iff]
  exact P.part_eq_iff_mem X.property

/-- Intrinsic bundle multiplicity is the original crossing multiplicity of its two blocks. -/
theorem finpartitionBundleMultiplicity_mk (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) (A B : P.parts) :
    H.finpartitionBundleMultiplicity P s(A, B) = H.crossingMultiplicity A.1 B.1 := by
  unfold finpartitionBundleMultiplicity bundleMultiplicityOn crossingMultiplicity
  congr 1
  ext pin
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.eq_iff]
  simp only [finpartitionBlock_eq_iff_mem]

theorem finpartitionCapacity_eq_sum (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) :
    H.finpartitionCapacity P =
      ∑ b ∈ (⊤ : SimpleGraph P.parts).edgeFinset,
        pinCapacity (H.finpartitionBundleMultiplicity P b) := rfl

/-- Canonical consecutive labels for the blocks of an ordinary finpartition. -/
noncomputable def finpartitionLabel (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) : H.Body → Fin P.parts.card :=
  P.parts.equivFin ∘ finpartitionBlock P

theorem finpartitionLabel_surjective (H : BodyPinIncidence)
    (P : Finpartition (Finset.univ : Finset H.Body)) :
    Function.Surjective (H.finpartitionLabel P) :=
  P.parts.equivFin.surjective.comp (finpartitionBlock_surjective P)

/-- Intrinsic block capacity equals capacity after canonical finite relabelling. -/
theorem finpartitionCapacity_eq_partitionCapacity_label
    (H : BodyPinIncidence) (P : Finpartition (Finset.univ : Finset H.Body)) :
    H.finpartitionCapacity P = H.partitionCapacity (H.finpartitionLabel P) := by
  rw [← H.capacityOn_fin]
  exact (H.capacityOn_comp_equiv P.parts.equivFin (finpartitionBlock P)).symm

/-- The fibre of a finite block label. -/
def labelFiber (H : BodyPinIncidence) {t : ℕ} (label : H.Body → Fin t)
    (i : Fin t) : Finset H.Body :=
  Finset.univ.filter fun a => label a = i

@[simp]
theorem mem_labelFiber (H : BodyPinIncidence) {t : ℕ} (label : H.Body → Fin t)
    (i : Fin t) (a : H.Body) : a ∈ H.labelFiber label i ↔ label a = i := by
  simp [labelFiber]

theorem labelFiber_nonempty (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    (H.labelFiber label i).Nonempty := by
  obtain ⟨a, ha⟩ := hlabel i
  exact ⟨a, (H.mem_labelFiber label i a).mpr ha⟩

theorem labelFiber_injective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Injective (H.labelFiber label) := by
  intro i j hij
  obtain ⟨a, hai⟩ := H.labelFiber_nonempty label hlabel i
  have haj : a ∈ H.labelFiber label j := by rwa [← hij]
  exact (H.mem_labelFiber label i a).mp hai |>.symm.trans
    ((H.mem_labelFiber label j a).mp haj)

def labelFiberEmbedding (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Fin t ↪ Finset H.Body :=
  ⟨H.labelFiber label, H.labelFiber_injective label hlabel⟩

/-- The ordinary finpartition whose blocks are the nonempty label fibres. -/
def finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Finpartition (Finset.univ : Finset H.Body) :=
  Finpartition.ofExistsUnique
    (Finset.univ.map (H.labelFiberEmbedding label hlabel))
    (by
      intro X hX
      exact Finset.subset_univ X)
    (by
      intro a ha
      refine ⟨H.labelFiber label (label a), ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_map.mpr ⟨label a, Finset.mem_univ _, rfl⟩
      · exact (H.mem_labelFiber label (label a) a).mpr rfl
      · intro X hX
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hX.1
        have haX := hX.2
        have hai := (H.mem_labelFiber label i a).mp haX
        subst i
        rfl)
    (by
      intro hempty
      obtain ⟨i, hi, hifiber⟩ := Finset.mem_map.mp hempty
      have hne := H.labelFiber_nonempty label hlabel i
      have hifiber' : H.labelFiber label i = ∅ := by
        simpa [labelFiberEmbedding] using hifiber
      rw [hifiber'] at hne
      exact Finset.not_nonempty_empty hne)

@[simp]
theorem finpartitionOfSurjection_parts (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    (H.finpartitionOfSurjection label hlabel).parts =
      Finset.univ.map (H.labelFiberEmbedding label hlabel) := rfl

@[simp]
theorem card_parts_finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    (H.finpartitionOfSurjection label hlabel).parts.card = t := by
  rw [H.finpartitionOfSurjection_parts]
  simp

/-- The fibre with label `i`, regarded as a block of the fibre partition. -/
def labelBlock (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    (H.finpartitionOfSurjection label hlabel).parts :=
  ⟨H.labelFiber label i, by
    rw [H.finpartitionOfSurjection_parts]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem labelBlock_injective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Injective (H.labelBlock label hlabel) := by
  intro i j hij
  apply H.labelFiber_injective label hlabel
  exact congr_arg Subtype.val hij

theorem labelBlock_surjective (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Function.Surjective (H.labelBlock label hlabel) := by
  intro X
  have hX : X.1 ∈ Finset.univ.map (H.labelFiberEmbedding label hlabel) := by
    simpa only [H.finpartitionOfSurjection_parts] using X.property
  obtain ⟨i, hi, hiX⟩ := Finset.mem_map.mp hX
  refine ⟨i, Subtype.ext ?_⟩
  simpa [labelBlock, labelFiberEmbedding] using hiX

/-- Labels are equivalent to the blocks of their fibre partition. -/
noncomputable def labelEquivBlocks (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    Fin t ≃ (H.finpartitionOfSurjection label hlabel).parts :=
  Equiv.ofBijective (H.labelBlock label hlabel)
    ⟨H.labelBlock_injective label hlabel, H.labelBlock_surjective label hlabel⟩

@[simp]
theorem labelEquivBlocks_apply (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (i : Fin t) :
    H.labelEquivBlocks label hlabel i = H.labelBlock label hlabel i := rfl

theorem finpartitionBlock_eq_labelEquivBlocks (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) (a : H.Body) :
    finpartitionBlock (H.finpartitionOfSurjection label hlabel) a =
      H.labelEquivBlocks label hlabel (label a) := by
  rw [H.labelEquivBlocks_apply]
  apply Subtype.ext
  exact (H.finpartitionOfSurjection label hlabel).part_eq_of_mem
    (H.labelBlock label hlabel (label a)).property
    ((H.mem_labelFiber label (label a) a).mpr rfl)

/-- The fibre finpartition and its original surjective labelling have equal capacity. -/
theorem finpartitionCapacity_finpartitionOfSurjection (H : BodyPinIncidence) {t : ℕ}
    (label : H.Body → Fin t) (hlabel : Function.Surjective label) :
    H.finpartitionCapacity (H.finpartitionOfSurjection label hlabel) =
      H.partitionCapacity label := by
  let P := H.finpartitionOfSurjection label hlabel
  let e := H.labelEquivBlocks label hlabel
  have hblock : finpartitionBlock P = e ∘ label := by
    funext a
    exact H.finpartitionBlock_eq_labelEquivBlocks label hlabel a
  unfold finpartitionCapacity
  rw [hblock, H.capacityOn_comp_equiv, H.capacityOn_fin]

/-- The intrinsic partition condition over all ordinary finpartitions. -/
def FinpartitionCondition (H : BodyPinIncidence) : Prop :=
  ∀ P : Finpartition (Finset.univ : Finset H.Body),
    6 * (P.parts.card - 1) ≤ H.finpartitionCapacity P

/--
Surjective finite labels and ordinary finpartitions give exactly the same
body--pin partition condition.  No nonemptiness hypothesis is needed.
-/
theorem partitionCondition_iff_finpartitionCondition (H : BodyPinIncidence) :
    H.PartitionCondition ↔ H.FinpartitionCondition := by
  constructor
  · intro hlabelled P
    have h := hlabelled P.parts.card (H.finpartitionLabel P)
      (H.finpartitionLabel_surjective P)
    rw [← H.finpartitionCapacity_eq_partitionCapacity_label] at h
    exact h
  · intro hparts t label hlabel
    have h := hparts (H.finpartitionOfSurjection label hlabel)
    rw [H.card_parts_finpartitionOfSurjection,
      H.finpartitionCapacity_finpartitionOfSurjection] at h
    exact h

end BodyPinIncidence

end RB31E2E


end
end BundlePart3

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_004/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_004.json"

section BundlePart4
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_Basic.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/Basic.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/













@[expose] public section

/-!
# Simple `(2,2)`-sparse edge sets

This file uses finite sets of unordered, non-diagonal vertex pairs.  Thus
parallel occurrences and loops are absent by construction.  Multiplicities
belong to the body--pin incidence layer, not to the sparse support.
-/

namespace RB31E2E

/-- An unordered edge with two distinct endpoints. -/
abbrev SimpleEdge (V : Type*) := {e : Sym2 V // ¬e.IsDiag}

/-- An occurrence-free finite simple edge set. -/
abbrev SimpleEdgeSet (V : Type*) := Finset (SimpleEdge V)

namespace SimpleEdge

variable {V : Type*} [DecidableEq V]

/-- The two endpoints of a simple edge. -/
def vertices (e : SimpleEdge V) : Finset V :=
  e.1.toFinset

@[simp]
theorem card_vertices (e : SimpleEdge V) : e.vertices.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.1 e.2

end SimpleEdge

variable {V : Type*} [DecidableEq V]

/-- Edges of `F` whose two endpoints lie in `X`. -/
def edgesInside (F : SimpleEdgeSet V) (X : Finset V) : SimpleEdgeSet V :=
  F.filter fun e => e.vertices ⊆ X

@[simp]
theorem mem_edgesInside {F : SimpleEdgeSet V} {X : Finset V} {e : SimpleEdge V} :
    e ∈ edgesInside F X ↔ e ∈ F ∧ e.vertices ⊆ X := by
  simp [edgesInside]

theorem edgesInside_subset (F : SimpleEdgeSet V) (X : Finset V) :
    edgesInside F X ⊆ F := by
  intro e he
  exact (mem_edgesInside.mp he).1

theorem edgesInside_mono_edges {F G : SimpleEdgeSet V} (hFG : F ⊆ G)
    (X : Finset V) : edgesInside F X ⊆ edgesInside G X := by
  intro e he
  exact mem_edgesInside.mpr ⟨hFG (mem_edgesInside.mp he).1, (mem_edgesInside.mp he).2⟩

theorem edgesInside_mono_vertices (F : SimpleEdgeSet V) {X Y : Finset V}
    (hXY : X ⊆ Y) : edgesInside F X ⊆ edgesInside F Y := by
  intro e he
  exact mem_edgesInside.mpr
    ⟨(mem_edgesInside.mp he).1, (mem_edgesInside.mp he).2.trans hXY⟩

theorem edgesInside_insert (F : SimpleEdgeSet V) (e : SimpleEdge V) (X : Finset V) :
    edgesInside (insert e F) X =
      if e.vertices ⊆ X then insert e (edgesInside F X) else edgesInside F X := by
  simpa only [edgesInside] using
    (Finset.filter_insert (p := fun f : SimpleEdge V => f.vertices ⊆ X) e F)

/-- Every nonempty induced vertex set obeys the `(2,2)` count. -/
def Sparse22 (F : SimpleEdgeSet V) : Prop :=
  ∀ X : Finset V, X.Nonempty → (edgesInside F X).card ≤ 2 * (X.card - 1)

/-- A nonempty vertex set on which the `(2,2)` inequality is tight. -/
def Tight22 (F : SimpleEdgeSet V) (X : Finset V) : Prop :=
  X.Nonempty ∧ (edgesInside F X).card = 2 * (X.card - 1)

@[simp]
theorem sparse22_empty : Sparse22 (∅ : SimpleEdgeSet V) := by
  intro X hX
  simp [edgesInside]

theorem Sparse22.mono {F G : SimpleEdgeSet V} (hF : Sparse22 F) (hGF : G ⊆ F) :
    Sparse22 G := by
  intro X hX
  exact (Finset.card_le_card (edgesInside_mono_edges hGF X)).trans (hF X hX)

/--
If adjoining a new simple edge destroys `(2,2)`-sparsity, some nonempty
vertex set contains both endpoints and was already tight before the edge
was adjoined.
-/
theorem exists_tight22_of_not_sparse22_insert {F : SimpleEdgeSet V} {e : SimpleEdge V}
    (hF : Sparse22 F) (heF : e ∉ F) (hbad : ¬ Sparse22 (insert e F)) :
    ∃ X : Finset V, X.Nonempty ∧ e.vertices ⊆ X ∧ Tight22 F X := by
  rw [Sparse22] at hbad
  push Not at hbad
  obtain ⟨X, hX, hviol⟩ := hbad
  have heX : e.vertices ⊆ X := by
    by_contra heX
    have hsame : edgesInside (insert e F) X = edgesInside F X := by
      simp [edgesInside_insert, heX]
    rw [hsame] at hviol
    exact (Nat.not_lt_of_ge (hF X hX)) hviol
  have heInside : e ∉ edgesInside F X := by
    simpa only [mem_edgesInside, not_and_or] using Or.inl heF
  have hcard :
      (edgesInside (insert e F) X).card = (edgesInside F X).card + 1 := by
    simp [edgesInside_insert, heX, heInside]
  have htight : (edgesInside F X).card = 2 * (X.card - 1) := by
    have hle := hF X hX
    rw [hcard] at hviol
    omega
  exact ⟨X, hX, heX, hX, htight⟩

end RB31E2E


end
end BundlePart4

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_005/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_005.json"

section BundlePart5
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_Uncrossing.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/Uncrossing.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Tight-set uncrossing for `(2,2)`-sparsity

The intersection is required to be nonempty.  This includes the
single-vertex-intersection case; no stronger overlap assumption is needed.
For disjoint tight sets neither tightness of their union nor tightness of
their empty intersection follows in general.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

theorem edgesInside_inter (F : SimpleEdgeSet V) (A B : Finset V) :
    edgesInside F (A ∩ B) = edgesInside F A ∩ edgesInside F B := by
  ext e
  simp only [mem_edgesInside, Finset.mem_inter]
  constructor
  · rintro ⟨heF, heAB⟩
    exact ⟨⟨heF, heAB.trans Finset.inter_subset_left⟩,
      ⟨heF, heAB.trans Finset.inter_subset_right⟩⟩
  · rintro ⟨⟨heF, heA⟩, -, heB⟩
    exact ⟨heF, Finset.subset_inter heA heB⟩

theorem union_edgesInside_subset (F : SimpleEdgeSet V) (A B : Finset V) :
    edgesInside F A ∪ edgesInside F B ⊆ edgesInside F (A ∪ B) := by
  intro e he
  rcases Finset.mem_union.mp he with heA | heB
  · exact mem_edgesInside.mpr
      ⟨(mem_edgesInside.mp heA).1,
        (mem_edgesInside.mp heA).2.trans Finset.subset_union_left⟩
  · exact mem_edgesInside.mpr
      ⟨(mem_edgesInside.mp heB).1,
        (mem_edgesInside.mp heB).2.trans Finset.subset_union_right⟩

/-- Induced-edge count is supermodular on vertex sets. -/
theorem card_edgesInside_supermodular (F : SimpleEdgeSet V) (A B : Finset V) :
    (edgesInside F A).card + (edgesInside F B).card ≤
      (edgesInside F (A ∪ B)).card + (edgesInside F (A ∩ B)).card := by
  calc
    (edgesInside F A).card + (edgesInside F B).card =
        (edgesInside F A ∪ edgesInside F B).card +
          (edgesInside F A ∩ edgesInside F B).card :=
      (Finset.card_union_add_card_inter _ _).symm
    _ ≤ (edgesInside F (A ∪ B)).card +
          (edgesInside F A ∩ edgesInside F B).card :=
      Nat.add_le_add_right
        (Finset.card_le_card (union_edgesInside_subset F A B)) _
    _ = (edgesInside F (A ∪ B)).card +
          (edgesInside F (A ∩ B)).card := by
      rw [edgesInside_inter]

/--
Two tight sets with nonempty intersection uncross: both their union and
their intersection are tight.  A one-vertex intersection is allowed.
-/
theorem tight22_union_inter {F : SimpleEdgeSet V} {A B : Finset V}
    (hF : Sparse22 F) (hA : Tight22 F A) (hB : Tight22 F B)
    (hAB : (A ∩ B).Nonempty) :
    Tight22 F (A ∪ B) ∧ Tight22 F (A ∩ B) := by
  have hAunionB : (A ∪ B).Nonempty := hA.1.mono Finset.subset_union_left
  have hSuper := card_edgesInside_supermodular F A B
  have hUnionUpper := hF (A ∪ B) hAunionB
  have hInterUpper := hF (A ∩ B) hAB
  have hCardIdentity := Finset.card_union_add_card_inter A B
  have hApos : 0 < A.card := Finset.card_pos.mpr hA.1
  have hBpos : 0 < B.card := Finset.card_pos.mpr hB.1
  have hUnionPos : 0 < (A ∪ B).card := Finset.card_pos.mpr hAunionB
  have hInterPos : 0 < (A ∩ B).card := Finset.card_pos.mpr hAB
  have hBudgetIdentity :
      2 * (A.card - 1) + 2 * (B.card - 1) =
        2 * ((A ∪ B).card - 1) + 2 * ((A ∩ B).card - 1) := by
    omega
  have hBudgetLower :
      2 * ((A ∪ B).card - 1) + 2 * ((A ∩ B).card - 1) ≤
        (edgesInside F (A ∪ B)).card + (edgesInside F (A ∩ B)).card := by
    rw [← hBudgetIdentity, ← hA.2, ← hB.2]
    exact hSuper
  have hUnionTight :
      (edgesInside F (A ∪ B)).card = 2 * ((A ∪ B).card - 1) := by
    omega
  have hInterTight :
      (edgesInside F (A ∩ B)).card = 2 * ((A ∩ B).card - 1) := by
    omega
  exact ⟨⟨hAunionB, hUnionTight⟩, ⟨hAB, hInterTight⟩⟩

end RB31E2E


end
end BundlePart5

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_006/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_006.json"

section BundlePart6
/- Source: Papers/RigidityZheng_Combinatorics_Sparse22_OptimalPartition.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/Sparse22/OptimalPartition.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Optimal tight-block partitions for `(2,2)`-sparse sets

The construction is canonical after a maximum-cardinality sparse subset
`F` is fixed: the block of a vertex is the union of all `F`-tight sets
containing that vertex.  No choice of a maximal tight set is made.
-/

namespace RB31E2E

variable {V : Type*} [DecidableEq V]

/-- `F` is a maximum-cardinality `(2,2)`-sparse subset of `J`. -/
structure IsMaximumSparseSubedge (J F : SimpleEdgeSet V) : Prop where
  subset : F ⊆ J
  sparse : Sparse22 F
  card_max : ∀ {G : SimpleEdgeSet V}, G ⊆ J → Sparse22 G → G.card ≤ F.card

/-- All sparse subsets of a fixed finite simple edge set. -/
noncomputable def sparseSubsets (J : SimpleEdgeSet V) : Finset (SimpleEdgeSet V) := by
  classical
  exact J.powerset.filter Sparse22

theorem mem_sparseSubsets {J F : SimpleEdgeSet V} :
    F ∈ sparseSubsets J ↔ F ⊆ J ∧ Sparse22 F := by
  classical
  simp [sparseSubsets]

/-- Every finite simple edge set has a maximum-cardinality sparse subset. -/
theorem exists_isMaximumSparseSubedge (J : SimpleEdgeSet V) :
    ∃ F : SimpleEdgeSet V, IsMaximumSparseSubedge J F := by
  classical
  have hne : (sparseSubsets J).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [mem_sparseSubsets]
  obtain ⟨F, hFmem, hFmax⟩ :=
    Finset.exists_max_image (sparseSubsets J) Finset.card hne
  have hF := mem_sparseSubsets.mp hFmem
  refine ⟨F, hF.1, hF.2, ?_⟩
  intro G hGJ hGsparse
  exact hFmax G (mem_sparseSubsets.mpr ⟨hGJ, hGsparse⟩)

theorem IsMaximumSparseSubedge.not_sparse_insert
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    ¬ Sparse22 (insert e F) := by
  intro hinsSparse
  have hinsJ : insert e F ⊆ J := Finset.insert_subset heJ hF.subset
  have hcard := hF.card_max hinsJ hinsSparse
  rw [Finset.card_insert_of_notMem heF] at hcard
  omega

/-- Every edge omitted by a maximum sparse subset has an `F`-tight witness. -/
theorem IsMaximumSparseSubedge.missing_edge_tight
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    ∃ X : Finset V, X.Nonempty ∧ e.vertices ⊆ X ∧ Tight22 F X :=
  exists_tight22_of_not_sparse22_insert hF.sparse heF
    (hF.not_sparse_insert heJ heF)

theorem SimpleEdge.not_vertices_subset_singleton (e : SimpleEdge V) (v : V) :
    ¬ e.vertices ⊆ {v} := by
  intro hev
  have hcard := Finset.card_le_card hev
  rw [e.card_vertices] at hcard
  simp at hcard

/-- Every singleton vertex set is tight; looplessness is used here. -/
theorem tight22_singleton (F : SimpleEdgeSet V) (v : V) : Tight22 F {v} := by
  have hempty : edgesInside F {v} = ∅ := by
    ext e
    simp [e.not_vertices_subset_singleton v]
  constructor
  · simp
  · simp [hempty]

/-- A finite family of tight sets with a common vertex has tight union. -/
theorem tight22_biUnion_of_common_vertex {F : SimpleEdgeSet V} (hF : Sparse22 F)
    {A : Finset (Finset V)} (hA : A.Nonempty) {v : V}
    (hv : ∀ X ∈ A, v ∈ X) (ht : ∀ X ∈ A, Tight22 F X) :
    Tight22 F (A.biUnion id) := by
  revert hv ht
  induction hA using Finset.Nonempty.cons_induction with
  | singleton X =>
      intro hv ht
      simpa using ht X (by simp)
  | cons X A hXA hA ih =>
      intro hv ht
      have htX : Tight22 F X := ht X (by simp)
      have htA : Tight22 F (A.biUnion id) := by
        apply ih
        · intro Y hY
          exact hv Y (by simp [hY])
        · intro Y hY
          exact ht Y (by simp [hY])
      have hinter : (X ∩ A.biUnion id).Nonempty := by
        obtain ⟨Y, hYA⟩ := hA
        refine ⟨v, ?_⟩
        exact Finset.mem_inter.mpr
          ⟨hv X (by simp), Finset.mem_biUnion.mpr ⟨Y, hYA, hv Y (by simp [hYA])⟩⟩
      have hu := (tight22_union_inter hF htX htA hinter).1
      simpa using hu

variable [Fintype V]

/-- All tight vertex sets containing `v`. -/
noncomputable def tightFamily (F : SimpleEdgeSet V) (v : V) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter fun X => v ∈ X ∧ Tight22 F X

@[simp]
theorem mem_tightFamily {F : SimpleEdgeSet V} {v : V} {X : Finset V} :
    X ∈ tightFamily F v ↔ v ∈ X ∧ Tight22 F X := by
  classical
  simp [tightFamily]

theorem tightFamily_nonempty (F : SimpleEdgeSet V) (v : V) :
    (tightFamily F v).Nonempty := by
  classical
  refine ⟨{v}, ?_⟩
  simp [tight22_singleton]

/-- The union of every tight set containing `v`. -/
noncomputable def tightHull (F : SimpleEdgeSet V) (v : V) : Finset V :=
  (tightFamily F v).biUnion id

theorem tightHull_tight {F : SimpleEdgeSet V} (hF : Sparse22 F) (v : V) :
    Tight22 F (tightHull F v) := by
  apply tight22_biUnion_of_common_vertex hF (tightFamily_nonempty F v)
  · intro X hX
    exact (mem_tightFamily.mp hX).1
  · intro X hX
    exact (mem_tightFamily.mp hX).2

@[simp]
theorem mem_tightHull_iff {F : SimpleEdgeSet V} {v w : V} :
    w ∈ tightHull F v ↔
      ∃ X : Finset V, Tight22 F X ∧ v ∈ X ∧ w ∈ X := by
  simp only [tightHull, Finset.mem_biUnion, mem_tightFamily, id_eq]
  aesop

@[simp]
theorem mem_tightHull_self (F : SimpleEdgeSet V) (v : V) : v ∈ tightHull F v := by
  rw [mem_tightHull_iff]
  exact ⟨{v}, tight22_singleton F v, by simp⟩

theorem mem_tightHull_comm {F : SimpleEdgeSet V} {v w : V} :
    w ∈ tightHull F v ↔ v ∈ tightHull F w := by
  simp only [mem_tightHull_iff]
  constructor <;> rintro ⟨X, hX, hv, hw⟩ <;> exact ⟨X, hX, hw, hv⟩

theorem tight_subset_tightHull {F : SimpleEdgeSet V} {X : Finset V} {v : V}
    (hX : Tight22 F X) (hv : v ∈ X) : X ⊆ tightHull F v := by
  intro w hw
  rw [mem_tightHull_iff]
  exact ⟨X, hX, hv, hw⟩

theorem tightHull_eq_of_mem {F : SimpleEdgeSet V} (hF : Sparse22 F) {v w : V}
    (hw : w ∈ tightHull F v) : tightHull F w = tightHull F v := by
  apply Finset.Subset.antisymm
  · apply tight_subset_tightHull (tightHull_tight hF w)
    exact mem_tightHull_comm.mp hw
  · exact tight_subset_tightHull (tightHull_tight hF v) hw

/-- Vertices are equivalent when they lie in one common tight set. -/
noncomputable def tightSetoid (F : SimpleEdgeSet V) (hF : Sparse22 F) : Setoid V where
  r v w := w ∈ tightHull F v
  iseqv := {
    refl := mem_tightHull_self F
    symm := fun hvw => mem_tightHull_comm.mp hvw
    trans := fun hvw hwz => by
      rw [tightHull_eq_of_mem hF hvw] at hwz
      exact hwz }

/-- The canonical partition into maximal tight blocks. -/
noncomputable def tightPartition (F : SimpleEdgeSet V) (hF : Sparse22 F) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid (tightSetoid F hF)

theorem tightPartition_part_eq_tightHull {F : SimpleEdgeSet V} (hF : Sparse22 F) (v : V) :
    (tightPartition F hF).part v = tightHull F v := by
  classical
  ext w
  simp [tightPartition, tightSetoid, Finpartition.mem_part_ofSetoid_iff_rel]

/-- Every part of the canonical partition is tight. -/
theorem tight_of_mem_tightPartition {F : SimpleEdgeSet V} (hF : Sparse22 F)
    {X : Finset V} (hX : X ∈ (tightPartition F hF).parts) : Tight22 F X := by
  obtain ⟨v, hv⟩ := (tightPartition F hF).nonempty_of_mem_parts hX
  have hpart : (tightPartition F hF).part v = X :=
    (tightPartition F hF).part_eq_of_mem hX hv
  rw [← hpart, tightPartition_part_eq_tightHull]
  exact tightHull_tight hF v

/-- An edge is internal when all its endpoints lie in one partition block. -/
def InternalTo (P : Finpartition (Finset.univ : Finset V)) (e : SimpleEdge V) : Prop :=
  ∃ X ∈ P.parts, e.vertices ⊆ X

/-- Every edge omitted by a maximum sparse set is internal to its tight partition. -/
theorem IsMaximumSparseSubedge.internal_missing_edge
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F)
    {e : SimpleEdge V} (heJ : e ∈ J) (heF : e ∉ F) :
    InternalTo (tightPartition F hF.sparse) e := by
  obtain ⟨X, hXne, heX, hXtight⟩ := hF.missing_edge_tight heJ heF
  obtain ⟨v, hvX⟩ := hXne
  refine ⟨(tightPartition F hF.sparse).part v, ?_, ?_⟩
  · exact (tightPartition F hF.sparse).part_mem.mpr (by simp)
  · rw [tightPartition_part_eq_tightHull]
    exact heX.trans (tight_subset_tightHull hXtight hvX)

/-- Edges lying inside some block of `P`. -/
noncomputable def internalEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleEdgeSet V := by
  classical
  exact K.filter (InternalTo P)

/-- Edges crossing the blocks of `P`. -/
noncomputable def crossEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleEdgeSet V := by
  classical
  exact K.filter fun e => ¬ InternalTo P e

@[simp]
theorem mem_internalEdges {K : SimpleEdgeSet V}
    {P : Finpartition (Finset.univ : Finset V)} {e : SimpleEdge V} :
    e ∈ internalEdges K P ↔ e ∈ K ∧ InternalTo P e := by
  classical
  simp [internalEdges]

@[simp]
theorem mem_crossEdges {K : SimpleEdgeSet V}
    {P : Finpartition (Finset.univ : Finset V)} {e : SimpleEdge V} :
    e ∈ crossEdges K P ↔ e ∈ K ∧ ¬ InternalTo P e := by
  classical
  simp [crossEdges]

theorem card_internalEdges_add_card_crossEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (internalEdges K P).card + (crossEdges K P).card = K.card := by
  classical
  exact Finset.card_filter_add_card_filter_not (s := K) (InternalTo P)

theorem internalEdges_eq_biUnion (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    internalEdges K P = P.parts.biUnion (edgesInside K) := by
  classical
  ext e
  simp only [mem_internalEdges, InternalTo, Finset.mem_biUnion, mem_edgesInside]
  aesop

theorem pairwiseDisjoint_edgesInside (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (P.parts : Set (Finset V)).PairwiseDisjoint (edgesInside K) := by
  intro A hA B hB hAB
  rw [Function.onFun, Finset.disjoint_left]
  intro e heA heB
  have hverts : e.vertices.Nonempty := Finset.card_pos.mp (by simp)
  obtain ⟨v, hv⟩ := hverts
  exact (Finset.disjoint_left.mp (P.disjoint hA hB hAB))
    ((mem_edgesInside.mp heA).2 hv) ((mem_edgesInside.mp heB).2 hv)

theorem card_internalEdges (K : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (internalEdges K P).card = ∑ X ∈ P.parts, (edgesInside K X).card := by
  classical
  rw [internalEdges_eq_biUnion, Finset.card_biUnion (pairwiseDisjoint_edgesInside K P)]

theorem sum_two_card_sub_one_parts
    (P : Finpartition (Finset.univ : Finset V)) :
    (∑ X ∈ P.parts, 2 * (X.card - 1)) =
      2 * (Fintype.card V - P.parts.card) := by
  have hsub :
      (∑ X ∈ P.parts, (X.card - 1)) =
        (∑ X ∈ P.parts, X.card) - P.parts.card := by
    calc
      (∑ X ∈ P.parts, (X.card - 1)) =
          (∑ X ∈ P.parts, X.card) - (∑ _X ∈ P.parts, 1) := by
        apply Finset.sum_tsub_distrib
        intro X hX
        exact Finset.card_pos.mpr (P.nonempty_of_mem_parts hX)
      _ = (∑ X ∈ P.parts, X.card) - P.parts.card := by simp
  calc
    (∑ X ∈ P.parts, 2 * (X.card - 1)) =
        2 * (∑ X ∈ P.parts, (X.card - 1)) := by
      symm
      exact Finset.mul_sum P.parts (fun X => X.card - 1) 2
    _ = 2 * ((∑ X ∈ P.parts, X.card) - P.parts.card) := by rw [hsub]
    _ = 2 * (Fintype.card V - P.parts.card) := by
      rw [P.sum_card_parts]
      simp

/-- The partition expression associated with a simple support. -/
noncomputable def sparsePartitionTerm (J : SimpleEdgeSet V)
    (P : Finpartition (Finset.univ : Finset V)) : ℕ :=
  2 * (Fintype.card V - P.parts.card) + (crossEdges J P).card

theorem crossEdges_mono {K L : SimpleEdgeSet V} (hKL : K ⊆ L)
    (P : Finpartition (Finset.univ : Finset V)) : crossEdges K P ⊆ crossEdges L P := by
  intro e he
  exact mem_crossEdges.mpr ⟨hKL (mem_crossEdges.mp he).1, (mem_crossEdges.mp he).2⟩

theorem IsMaximumSparseSubedge.crossEdges_eq
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F) :
    crossEdges F (tightPartition F hF.sparse) =
      crossEdges J (tightPartition F hF.sparse) := by
  classical
  ext e
  simp only [mem_crossEdges]
  constructor
  · rintro ⟨heF, heCross⟩
    exact ⟨hF.subset heF, heCross⟩
  · rintro ⟨heJ, heCross⟩
    refine ⟨?_, heCross⟩
    by_contra heFmem
    exact heCross (hF.internal_missing_edge heJ heFmem)

theorem card_internalEdges_tightPartition {F : SimpleEdgeSet V} (hF : Sparse22 F) :
    (internalEdges F (tightPartition F hF)).card =
      2 * (Fintype.card V - (tightPartition F hF).parts.card) := by
  rw [card_internalEdges]
  calc
    (∑ X ∈ (tightPartition F hF).parts, (edgesInside F X).card) =
        ∑ X ∈ (tightPartition F hF).parts, 2 * (X.card - 1) := by
      apply Finset.sum_congr rfl
      intro X hX
      exact (tight_of_mem_tightPartition hF hX).2
    _ = 2 * (Fintype.card V - (tightPartition F hF).parts.card) :=
      sum_two_card_sub_one_parts (tightPartition F hF)

/--
The canonical tight partition realizes equality in the partition bound for
a maximum sparse subset.
-/
theorem IsMaximumSparseSubedge.card_eq_sparsePartitionTerm
    {J F : SimpleEdgeSet V} (hF : IsMaximumSparseSubedge J F) :
    F.card = sparsePartitionTerm J (tightPartition F hF.sparse) := by
  have hsplit :=
    card_internalEdges_add_card_crossEdges F (tightPartition F hF.sparse)
  rw [card_internalEdges_tightPartition hF.sparse, hF.crossEdges_eq] at hsplit
  exact hsplit.symm

/-- Every sparse subset is bounded by every partition term. -/
theorem Sparse22.card_le_sparsePartitionTerm
    {J F : SimpleEdgeSet V} (hF : Sparse22 F) (hFJ : F ⊆ J)
    (P : Finpartition (Finset.univ : Finset V)) :
    F.card ≤ sparsePartitionTerm J P := by
  have hInternal :
      (internalEdges F P).card ≤ 2 * (Fintype.card V - P.parts.card) := by
    rw [card_internalEdges]
    calc
      (∑ X ∈ P.parts, (edgesInside F X).card) ≤
          ∑ X ∈ P.parts, 2 * (X.card - 1) := by
        apply Finset.sum_le_sum
        intro X hX
        exact hF X (P.nonempty_of_mem_parts hX)
      _ = 2 * (Fintype.card V - P.parts.card) := sum_two_card_sub_one_parts P
  have hCross : (crossEdges F P).card ≤ (crossEdges J P).card :=
    Finset.card_le_card (crossEdges_mono hFJ P)
  have hsplit := card_internalEdges_add_card_crossEdges F P
  simp only [sparsePartitionTerm]
  omega

/--
If every partition term is at least `R`, then `J` has an `R`-edge
`(2,2)`-sparse subset.  This is the extraction statement needed by the
body--pin bridge and does not invoke a graphic-matroid-union API.
-/
theorem exists_sparse22_of_all_partition_terms (J : SimpleEdgeSet V) (R : ℕ)
    (hR : ∀ P : Finpartition (Finset.univ : Finset V), R ≤ sparsePartitionTerm J P) :
    ∃ F : SimpleEdgeSet V, F ⊆ J ∧ Sparse22 F ∧ F.card = R := by
  obtain ⟨M, hM⟩ := exists_isMaximumSparseSubedge J
  have hRM : R ≤ M.card := by
    rw [hM.card_eq_sparsePartitionTerm]
    exact hR (tightPartition M hM.sparse)
  obtain ⟨F, hFM, hFcard⟩ := Finset.exists_subset_card_eq hRM
  exact ⟨F, hFM.trans hM.subset, hM.sparse.mono hFM, hFcard⟩

end RB31E2E


end
end BundlePart6

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_007/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_007.json"

section BundlePart7
/- Source: Papers/RigidityZheng_Combinatorics_BodyPinSparseSkeleton.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Combinatorics/BodyPinSparseSkeleton.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# A sparse null skeleton from body--pin partition capacity

This file isolates the finite combinatorial bridge used by the body--pin
closure argument.  A fine surjective labelling gives a simple support whose
nonzero bundle multiplicities are assumed to be at most two.  The partition
condition then forces that support to contain a prescribed `(2,2)`-sparse
subgraph.

The key intermediate statement is a provenance-preserving aggregation
inequality: after any coarsening of the fine labels, capped capacity is at
most `2 M + s`, where `M` and `s` count the fine crossing occurrences and
their fine simple support.  Thus aggregation never creates an unaccounted
capacity contribution.
-/

namespace RB31E2E

private theorem pinCapacity_eq_two_mul_add_one_of_pos_le_two
    {m : ℕ} (hpos : 0 < m) (hle : m ≤ 2) :
    pinCapacity m = 2 * m + 1 := by
  interval_cases m <;> decide

private theorem pinCapacity_le_two_mul_add_support
    (M s : ℕ) (hLower : s ≤ M) (hUpper : M ≤ 2 * s) :
    pinCapacity M ≤ 2 * M + s := by
  rcases M with _ | _ | _ | M <;> simp [pinCapacity]
  all_goals omega

/-- Edges of the complete graph, regarded as unordered non-diagonal pairs. -/
def completeEdgeEquivSimpleEdge (I : Type*) [Fintype I] [DecidableEq I] :
    (⊤ : SimpleGraph I).edgeFinset ≃ SimpleEdge I where
  toFun b := ⟨b.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet] using b.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet] using e.2⟩
  left_inv b := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

@[simp]
theorem completeEdgeEquivSimpleEdge_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : (⊤ : SimpleGraph I).edgeFinset) :
    (completeEdgeEquivSimpleEdge I b).1 = b.1 := rfl

/-- Reindex a complete-graph edge sum by unordered non-diagonal pairs. -/
theorem sum_completeEdges_eq_sum_simpleEdges
    {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    (f : Sym2 I → M) :
    (∑ b ∈ (⊤ : SimpleGraph I).edgeFinset, f b) =
      ∑ e : SimpleEdge I, f e.1 := by
  rw [← Finset.sum_attach]
  exact Fintype.sum_equiv (completeEdgeEquivSimpleEdge I)
    (fun b => f b.1) (fun e => f e.1) (fun _ => rfl)

namespace BodyPinIncidence

/-- Multiplicity carried by one fine simple label pair. -/
def fineMultiplicityOn (H : BodyPinIncidence) {I : Type*} [DecidableEq I]
    (label : H.Body → I) (e : SimpleEdge I) : ℕ :=
  H.bundleMultiplicityOn label e.1

/-- The simple support of all nonempty fine bundles. -/
noncomputable def fineSupportOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : SimpleEdgeSet I := by
  classical
  exact Finset.univ.filter fun e => 0 < H.fineMultiplicityOn label e

@[simp]
theorem mem_fineSupportOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) (e : SimpleEdge I) :
    e ∈ H.fineSupportOn label ↔ 0 < H.fineMultiplicityOn label e := by
  classical
  simp [fineSupportOn]

/-- Total multiplicity of the nonempty fine bundles. -/
noncomputable def fineMassOn (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) : ℕ :=
  ∑ e ∈ H.fineSupportOn label, H.fineMultiplicityOn label e

/-- Capacity may be summed over the type of simple edges. -/
theorem capacityOn_eq_sum_simpleEdges (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) :
    H.capacityOn label =
      ∑ e : SimpleEdge I, pinCapacity (H.fineMultiplicityOn label e) := by
  unfold capacityOn fineMultiplicityOn
  exact sum_completeEdges_eq_sum_simpleEdges
    (fun b => pinCapacity (H.bundleMultiplicityOn label b))

/-- Zero fine bundles can be removed from a multiplicity sum. -/
theorem fineMassOn_eq_sum_simpleEdges (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I) :
    H.fineMassOn label = ∑ e : SimpleEdge I, H.fineMultiplicityOn label e := by
  classical
  unfold fineMassOn fineSupportOn
  apply Finset.sum_subset (by simp)
  intro e heuniv henot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at henot
  exact Nat.eq_zero_of_not_pos henot

/-- On one- or two-pin support, the fine capacity is exactly `2 M + s`. -/
theorem capacityOn_eq_two_mul_fineMass_add_supportCard
    (H : BodyPinIncidence) {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.capacityOn label =
      2 * H.fineMassOn label + (H.fineSupportOn label).card := by
  classical
  rw [H.capacityOn_eq_sum_simpleEdges]
  calc
    (∑ e : SimpleEdge I, pinCapacity (H.fineMultiplicityOn label e)) =
        ∑ e ∈ H.fineSupportOn label,
          pinCapacity (H.fineMultiplicityOn label e) := by
      symm
      apply Finset.sum_subset (by simp)
      intro e heuniv henot
      have hm : ¬ 0 < H.fineMultiplicityOn label e := by
        simpa only [H.mem_fineSupportOn] using henot
      have hz : H.fineMultiplicityOn label e = 0 := Nat.eq_zero_of_not_pos hm
      simp [hz]
    _ = ∑ e ∈ H.fineSupportOn label,
          (2 * H.fineMultiplicityOn label e + 1) := by
      apply Finset.sum_congr rfl
      intro e he
      have hpos := (H.mem_fineSupportOn label e).mp he
      exact pinCapacity_eq_two_mul_add_one_of_pos_le_two hpos (hsmall e he)
    _ = 2 * H.fineMassOn label + (H.fineSupportOn label).card := by
      simp only [fineMassOn, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      simp

/-- Fine support edges which remain non-diagonal after a relabelling. -/
noncomputable def crossingFineSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) : SimpleEdgeSet I := by
  classical
  exact (H.fineSupportOn label).filter fun e => ¬(e.1.map ρ).IsDiag

@[simp]
theorem mem_crossingFineSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (e : SimpleEdge I) :
    e ∈ H.crossingFineSupportOn label ρ ↔
      e ∈ H.fineSupportOn label ∧ ¬(e.1.map ρ).IsDiag := by
  classical
  simp [crossingFineSupportOn]

/-- Total fine multiplicity which survives a relabelling as a crossing bundle. -/
noncomputable def crossingFineMassOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) : ℕ :=
  ∑ e ∈ H.crossingFineSupportOn label ρ,
    H.fineMultiplicityOn label e

/-- Fine support lying above one coarse unordered pair. -/
noncomputable def fibreSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) : SimpleEdgeSet I := by
  classical
  exact (H.fineSupportOn label).filter fun e => e.1.map ρ = b

@[simp]
theorem mem_fibreSupportOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) (e : SimpleEdge I) :
    e ∈ H.fibreSupportOn label ρ b ↔
      e ∈ H.fineSupportOn label ∧ e.1.map ρ = b := by
  classical
  simp [fibreSupportOn]

/-- Fine multiplicity lying above one coarse unordered pair. -/
noncomputable def fibreMassOn (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) : ℕ :=
  ∑ e ∈ H.fibreSupportOn label ρ b, H.fineMultiplicityOn label e

private theorem sum_filter_simpleEdges_eq_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) :
    (∑ e : SimpleEdge I with e.1.map ρ = b,
        H.fineMultiplicityOn label e) = H.fibreMassOn label ρ b := by
  classical
  unfold fibreMassOn
  symm
  apply Finset.sum_subset
  · intro e he
    have he' := (H.mem_fibreSupportOn label ρ b e).mp he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact he'.2
  · intro e heBig heSmall
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heBig
    have hnotSupport : e ∉ H.fineSupportOn label := by
      intro heSupport
      exact heSmall ((H.mem_fibreSupportOn label ρ b e).mpr ⟨heSupport, heBig⟩)
    have hnotPos : ¬ 0 < H.fineMultiplicityOn label e := by
      simpa only [H.mem_fineSupportOn] using hnotSupport
    exact Nat.eq_zero_of_not_pos hnotPos

/-- Coarse bundle multiplicity is the sum of the fine multiplicities above it. -/
theorem bundleMultiplicityOn_comp_eq_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K)
    (b : Sym2 K) (hb : b ∈ (⊤ : SimpleGraph K).edgeFinset) :
    H.bundleMultiplicityOn (ρ ∘ label) b = H.fibreMassOn label ρ b := by
  classical
  let T : Finset (Sym2 I) :=
    (⊤ : SimpleGraph I).edgeFinset.filter fun a => a.map ρ = b
  let pair : H.Pin → Sym2 I := fun p => s(label (H.left p), label (H.right p))
  have hraw := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset H.Pin) T pair
  have hbNotDiag : ¬ b.IsDiag := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet] using hb
  have hfilter :
      (Finset.univ.filter fun p : H.Pin => pair p ∈ T) =
        Finset.univ.filter fun p : H.Pin => (pair p).map ρ = b := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
    constructor
    · exact fun h => h.2
    · intro hp
      refine ⟨?_, hp⟩
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet]
        using fun hdiag => hbNotDiag (hp ▸ hdiag.map)
  have hraw' :
      (∑ a ∈ (⊤ : SimpleGraph I).edgeFinset with a.map ρ = b,
          H.bundleMultiplicityOn label a) =
        H.bundleMultiplicityOn (ρ ∘ label) b := by
    change (∑ a ∈ T,
        (Finset.univ.filter fun p : H.Pin => pair p = a).card) = _
    calc
      (∑ a ∈ T, (Finset.univ.filter fun p : H.Pin => pair p = a).card) =
          (Finset.univ.filter fun p : H.Pin => pair p ∈ T).card := hraw
      _ = (Finset.univ.filter fun p : H.Pin => (pair p).map ρ = b).card :=
        congrArg Finset.card hfilter
      _ = H.bundleMultiplicityOn (ρ ∘ label) b := by
        unfold bundleMultiplicityOn pair
        congr 1
  rw [← hraw']
  calc
    (∑ a ∈ (⊤ : SimpleGraph I).edgeFinset with a.map ρ = b,
        H.bundleMultiplicityOn label a) =
        ∑ e : SimpleEdge I with e.1.map ρ = b,
          H.fineMultiplicityOn label e := by
      rw [Finset.sum_filter, Finset.sum_filter]
      exact sum_completeEdges_eq_sum_simpleEdges
        (fun a => if a.map ρ = b then H.bundleMultiplicityOn label a else 0)
    _ = H.fibreMassOn label ρ b :=
      H.sum_filter_simpleEdges_eq_fibreMassOn label ρ b

theorem card_fibreSupportOn_le_fibreMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K) :
    (H.fibreSupportOn label ρ b).card ≤ H.fibreMassOn label ρ b := by
  classical
  unfold fibreMassOn
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  exact (H.mem_fineSupportOn label e).mp
    ((H.mem_fibreSupportOn label ρ b e).mp he).1

theorem fibreMassOn_le_two_mul_card
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) (b : Sym2 K)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.fibreMassOn label ρ b ≤ 2 * (H.fibreSupportOn label ρ b).card := by
  classical
  unfold fibreMassOn
  calc
    (∑ e ∈ H.fibreSupportOn label ρ b, H.fineMultiplicityOn label e) ≤
        ∑ _e ∈ H.fibreSupportOn label ρ b, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact hsmall e ((H.mem_fibreSupportOn label ρ b e).mp he).1
    _ = 2 * (H.fibreSupportOn label ρ b).card := by simp [Nat.mul_comm]

theorem sum_fibreMassOn_eq_crossingFineMassOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) :
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset, H.fibreMassOn label ρ b) =
      H.crossingFineMassOn label ρ := by
  classical
  unfold fibreMassOn fibreSupportOn crossingFineMassOn crossingFineSupportOn
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet] using
    (Finset.sum_fiberwise_eq_sum_filter
      (H.fineSupportOn label) (⊤ : SimpleGraph K).edgeFinset
      (fun e : SimpleEdge I => e.1.map ρ)
      (fun e => H.fineMultiplicityOn label e))

theorem sum_card_fibreSupportOn_eq_card_crossingFineSupportOn
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K) :
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
        (H.fibreSupportOn label ρ b).card) =
      (H.crossingFineSupportOn label ρ).card := by
  classical
  unfold fibreSupportOn crossingFineSupportOn
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top,
      Set.mem_compl_iff, Sym2.mem_diagSet] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (H.fineSupportOn label) (⊤ : SimpleGraph K).edgeFinset
      (fun e : SimpleEdge I => e.1.map ρ))

/--
The provenance-preserving aggregation inequality.  A coarse capped bundle
is paid for by the masses and support bits of the fine pairs which map to it.
-/
theorem capacityOn_comp_le_two_mul_crossingFineMass_add_card
    (H : BodyPinIncidence)
    {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K]
    (label : H.Body → I) (ρ : I → K)
    (hsmall : ∀ e ∈ H.fineSupportOn label,
      H.fineMultiplicityOn label e ≤ 2) :
    H.capacityOn (ρ ∘ label) ≤
      2 * H.crossingFineMassOn label ρ +
        (H.crossingFineSupportOn label ρ).card := by
  classical
  unfold capacityOn
  calc
    (∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
        pinCapacity (H.bundleMultiplicityOn (ρ ∘ label) b)) ≤
        ∑ b ∈ (⊤ : SimpleGraph K).edgeFinset,
          (2 * H.fibreMassOn label ρ b +
            (H.fibreSupportOn label ρ b).card) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [H.bundleMultiplicityOn_comp_eq_fibreMassOn label ρ b hb]
      exact pinCapacity_le_two_mul_add_support
        (H.fibreMassOn label ρ b) (H.fibreSupportOn label ρ b).card
        (H.card_fibreSupportOn_le_fibreMassOn label ρ b)
        (H.fibreMassOn_le_two_mul_card label ρ b hsmall)
    _ = 2 * H.crossingFineMassOn label ρ +
        (H.crossingFineSupportOn label ρ).card := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [H.sum_fibreMassOn_eq_crossingFineMassOn label ρ]
      rw [H.sum_card_fibreSupportOn_eq_card_crossingFineSupportOn label ρ]

theorem internalTo_iff_map_finpartitionBlock_isDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Finpartition (Finset.univ : Finset I)) (e : SimpleEdge I) :
    InternalTo P e ↔ (e.1.map (finpartitionBlock P)).IsDiag := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ a c =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      constructor
      · rintro ⟨X, hX, hac⟩
        have ha : a ∈ X := hac (by simp [SimpleEdge.vertices])
        have hc : c ∈ X := hac (by simp [SimpleEdge.vertices])
        apply Subtype.ext
        exact ((P.part_eq_iff_mem hX).2 ha).trans
          ((P.part_eq_iff_mem hX).2 hc).symm
      · intro hblock
        let X : P.parts := ⟨P.part a, P.part_mem.mpr (by simp)⟩
        refine ⟨X.1, X.2, ?_⟩
        intro v hv
        simp only [SimpleEdge.vertices, Sym2.toFinset_mk_eq,
          Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact P.mem_part (by simp)
        · have hpart : P.part v = P.part a := by
            exact congr_arg Subtype.val hblock.symm
          change v ∈ P.part a
          rw [← hpart]
          exact P.mem_part (by simp)

theorem crossingFineSupportOn_finpartitionBlock
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    H.crossingFineSupportOn label (finpartitionBlock P) =
      crossEdges (H.fineSupportOn label) P := by
  classical
  ext e
  rw [H.mem_crossingFineSupportOn, mem_crossEdges]
  rw [internalTo_iff_map_finpartitionBlock_isDiag]

theorem crossingFineMassOn_finpartitionBlock
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    H.crossingFineMassOn label (finpartitionBlock P) =
      ∑ e ∈ crossEdges (H.fineSupportOn label) P,
        H.fineMultiplicityOn label e := by
  unfold crossingFineMassOn
  rw [H.crossingFineSupportOn_finpartitionBlock label P]

theorem sum_internalEdges_add_sum_crossEdges
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : SimpleEdgeSet I)
    (P : Finpartition (Finset.univ : Finset I)) (w : SimpleEdge I → ℕ) :
    (∑ e ∈ internalEdges J P, w e) +
        (∑ e ∈ crossEdges J P, w e) = ∑ e ∈ J, w e := by
  classical
  unfold internalEdges crossEdges
  exact Finset.sum_filter_add_sum_filter_not J (InternalTo P) w

theorem card_internalEdges_le_sum_fineMultiplicity
    (H : BodyPinIncidence)
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : H.Body → I)
    (P : Finpartition (Finset.univ : Finset I)) :
    (internalEdges (H.fineSupportOn label) P).card ≤
      ∑ e ∈ internalEdges (H.fineSupportOn label) P,
        H.fineMultiplicityOn label e := by
  classical
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  exact (H.mem_fineSupportOn label e).mp (mem_internalEdges.mp he).1

/-- The deficit which must be paid by a sparse null skeleton. -/
noncomputable def sparseSkeletonTarget (H : BodyPinIncidence)
    {t : ℕ} (π : H.Body → Fin t) : ℕ :=
  6 * (t - 1) - 2 * H.fineMassOn π

/--
The body--pin partition condition extracts a simple `(2,2)`-sparse null
skeleton whenever every nonempty fine bundle contains at most two pins.

The explicit hypothesis `2 ≤ t` is the weakest case needed by the
nontrivial equality-cellule argument.  The zero- and one-label cases have
target zero and are intentionally left out of this interface.
-/
theorem exists_sparse_nullSkeleton
    (H : BodyPinIncidence) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (ht : 2 ≤ t)
    (hpartition : H.PartitionCondition)
    (hsmall : ∀ e ∈ H.fineSupportOn π,
      H.fineMultiplicityOn π e ≤ 2) :
    ∃ F : SimpleEdgeSet (Fin t),
      F ⊆ H.fineSupportOn π ∧ Sparse22 F ∧
        F.card = H.sparseSkeletonTarget π := by
  classical
  let J : SimpleEdgeSet (Fin t) := H.fineSupportOn π
  let M : ℕ := H.fineMassOn π
  let R : ℕ := H.sparseSkeletonTarget π
  have hfine : 6 * (t - 1) ≤ 2 * M + J.card := by
    have h := hpartition t π hπ
    rw [← H.capacityOn_fin] at h
    rw [H.capacityOn_eq_two_mul_fineMass_add_supportCard π hsmall] at h
    exact h
  have hterms :
      ∀ P : Finpartition (Finset.univ : Finset (Fin t)),
        R ≤ sparsePartitionTerm J P := by
    intro P
    let q : ℕ := P.parts.card
    let C : SimpleEdgeSet (Fin t) := crossEdges J P
    let A : SimpleEdgeSet (Fin t) := internalEdges J P
    let MC : ℕ := ∑ e ∈ C, H.fineMultiplicityOn π e
    let MA : ℕ := ∑ e ∈ A, H.fineMultiplicityOn π e
    have hqle : q ≤ t := by
      simpa [q] using P.card_parts_le_card
    have hqpos : 0 < q := by
      let v : Fin t := ⟨0, by omega⟩
      have hv : P.part v ∈ P.parts := P.part_mem.mpr (by simp)
      exact Finset.card_pos.mpr ⟨P.part v, hv⟩
    have hcardSplit : A.card + C.card = J.card := by
      exact card_internalEdges_add_card_crossEdges J P
    have hmassSplit : MA + MC = M := by
      exact sum_internalEdges_add_sum_crossEdges J P
        (fun e => H.fineMultiplicityOn π e)
    have hAcardMass : A.card ≤ MA := by
      exact H.card_internalEdges_le_sum_fineMultiplicity π P
    have hcoarseSurj :
        Function.Surjective (finpartitionBlock P ∘ π) :=
      (finpartitionBlock_surjective P).comp hπ
    have hcoarseLower :
        6 * (q - 1) ≤ H.capacityOn (finpartitionBlock P ∘ π) := by
      let e : P.parts ≃ Fin q := P.parts.equivFin
      have hsurj : Function.Surjective (e ∘ finpartitionBlock P ∘ π) :=
        e.surjective.comp hcoarseSurj
      have h := hpartition q (e ∘ finpartitionBlock P ∘ π) hsurj
      rw [← H.capacityOn_fin] at h
      have heq := H.capacityOn_comp_equiv e (finpartitionBlock P ∘ π)
      simpa only [Function.comp_assoc, heq] using h
    have hcoarseUpper :
        H.capacityOn (finpartitionBlock P ∘ π) ≤ 2 * MC + C.card := by
      have h := H.capacityOn_comp_le_two_mul_crossingFineMass_add_card
        π (finpartitionBlock P) hsmall
      rw [H.crossingFineMassOn_finpartitionBlock π P,
        H.crossingFineSupportOn_finpartitionBlock π P] at h
      exact h
    have hcoarse : 6 * (q - 1) ≤ 2 * MC + C.card :=
      hcoarseLower.trans hcoarseUpper
    have htarget : R = 6 * (t - 1) - 2 * M := rfl
    rw [sparsePartitionTerm]
    simp only [Fintype.card_fin]
    change R ≤ 2 * (t - q) + C.card
    rw [htarget]
    by_cases hsmallInternal : A.card ≤ 2 * (t - q)
    · omega
    · have hlargeInternal : 2 * (t - q) ≤ MA := by omega
      omega
  have hextract := exists_sparse22_of_all_partition_terms J R hterms
  simpa [J, R] using hextract

end BodyPinIncidence

end RB31E2E


end
end BundlePart7

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_008/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_008.json"

section BundlePart8
/- Source: Papers/RigidityDefectSkeleton.lean -/




@[expose] public section

/-!
# Sparse null skeletons for a nonzero body-pin defect

This is the quantitative extension of Zheng's zero-defect sparse skeleton
argument needed in Theorem 5.1. The hypothesis is a literal upper bound on
every partition defect, and the conclusion constructs an actual simple
`(2,2)`-sparse edge subset of the required cardinality.
-/

namespace Papers.Rigidity

open RB31E2E
open RB31E2E.BodyPinIncidence
open scoped BigOperators

/-- The sparse support subset supplying the quantitative Pfaffian codimension.
No generic geometry or dimension inequality is assumed in this combinatorial step. -/
theorem exists_sparse_nullSkeleton_of_defect_bound
    (H : BodyPinIncidence) (D : ℕ) {t : ℕ} (π : H.Body → Fin t)
    (hπ : Function.Surjective π) (ht : 2 ≤ t)
    (hpartition : PartitionDefectAtMost H D)
    (hsmall : ∀ e ∈ H.fineSupportOn π, H.fineMultiplicityOn π e ≤ 2) :
    ∃ F : SimpleEdgeSet (Fin t),
      F ⊆ H.fineSupportOn π ∧ Sparse22 F ∧
        F.card = 6 * (t - 1) - 2 * H.fineMassOn π - D := by
  classical
  let J : SimpleEdgeSet (Fin t) := H.fineSupportOn π
  let M : ℕ := H.fineMassOn π
  let R : ℕ := 6 * (t - 1) - 2 * M - D
  have hfine : 6 * (t - 1) ≤ 2 * M + J.card + D := by
    have h := hpartition t π hπ
    rw [← H.capacityOn_fin] at h
    rw [H.capacityOn_eq_two_mul_fineMass_add_supportCard π hsmall] at h
    exact h
  have hterms :
      ∀ P : Finpartition (Finset.univ : Finset (Fin t)),
        R ≤ sparsePartitionTerm J P := by
    intro P
    let q : ℕ := P.parts.card
    let C : SimpleEdgeSet (Fin t) := crossEdges J P
    let A : SimpleEdgeSet (Fin t) := internalEdges J P
    let MC : ℕ := ∑ e ∈ C, H.fineMultiplicityOn π e
    let MA : ℕ := ∑ e ∈ A, H.fineMultiplicityOn π e
    have hqle : q ≤ t := by
      simpa [q] using P.card_parts_le_card
    have hqpos : 0 < q := by
      let v : Fin t := ⟨0, by omega⟩
      have hv : P.part v ∈ P.parts := P.part_mem.mpr (by simp)
      exact Finset.card_pos.mpr ⟨P.part v, hv⟩
    have hcardSplit : A.card + C.card = J.card :=
      card_internalEdges_add_card_crossEdges J P
    have hmassSplit : MA + MC = M :=
      BodyPinIncidence.sum_internalEdges_add_sum_crossEdges J P
        (fun e => H.fineMultiplicityOn π e)
    have hAcardMass : A.card ≤ MA :=
      H.card_internalEdges_le_sum_fineMultiplicity π P
    have hcoarseSurj : Function.Surjective (finpartitionBlock P ∘ π) :=
      (finpartitionBlock_surjective P).comp hπ
    have hcoarseLower :
        6 * (q - 1) ≤ H.capacityOn (finpartitionBlock P ∘ π) + D := by
      let e : P.parts ≃ Fin q := P.parts.equivFin
      have hsurj : Function.Surjective (e ∘ finpartitionBlock P ∘ π) :=
        e.surjective.comp hcoarseSurj
      have h := hpartition q (e ∘ finpartitionBlock P ∘ π) hsurj
      rw [← H.capacityOn_fin] at h
      have heq := H.capacityOn_comp_equiv e (finpartitionBlock P ∘ π)
      simpa only [Function.comp_assoc, heq] using h
    have hcoarseUpper : H.capacityOn (finpartitionBlock P ∘ π) ≤
        2 * MC + C.card := by
      have h := H.capacityOn_comp_le_two_mul_crossingFineMass_add_card
        π (finpartitionBlock P) hsmall
      rw [H.crossingFineMassOn_finpartitionBlock π P,
        H.crossingFineSupportOn_finpartitionBlock π P] at h
      exact h
    have hcoarse : 6 * (q - 1) ≤ 2 * MC + C.card + D := by omega
    have htarget : R = 6 * (t - 1) - 2 * M - D := rfl
    rw [sparsePartitionTerm]
    simp only [Fintype.card_fin]
    change R ≤ 2 * (t - q) + C.card
    rw [htarget]
    by_cases hsmallInternal : A.card ≤ 2 * (t - q)
    · omega
    · have hlargeInternal : 2 * (t - q) ≤ MA := by omega
      omega
  exact exists_sparse22_of_all_partition_terms J R hterms

end Papers.Rigidity

end
end BundlePart8

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_009/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_009.json"

section BundlePart9
/- Source: Papers/RigidityZheng_Algebra_ComplexRealSpecialization.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/ComplexRealSpecialization.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Complex-to-real specialization for polynomial certificates

A nonzero polynomial over the reals has a real nonvanishing point.  Therefore
a polynomial certificate with coefficients in a ring that embeds into the
reals cannot exist only over the complexes.  The variable type need not be
finite: every multivariate polynomial has finite support, and
`MvPolynomial.funext` already packages that reduction.
-/

namespace RB31E2E

namespace ComplexRealSpecialization

open MvPolynomial

/-- A nonzero real multivariate polynomial is nonzero at some real point.
This is stronger than the finite-variable version: `σ` is arbitrary. -/
theorem exists_real_eval_ne_zero {σ : Type*}
    (P : MvPolynomial σ ℝ) (hP : P ≠ 0) :
    ∃ x : σ → ℝ, eval x P ≠ 0 := by
  by_contra hnone
  apply hP
  apply MvPolynomial.funext
  intro x
  have hx : eval x P = 0 := by
    by_contra hx
    exact hnone ⟨x, hx⟩
  simpa using hx

/-- Generic coefficient bridge.  The complex coefficient map need not be
injective: one nonzero complex evaluation already proves that the source
polynomial is nonzero.  Only the coefficient map into `ℝ` must be injective. -/
theorem map_real_ne_zero_and_exists_eval_of_complex_eval
    {R σ : Type*} [CommSemiring R]
    (toComplex : R →+* ℂ) (toReal : R →+* ℝ)
    (htoReal : Function.Injective toReal)
    (P : MvPolynomial σ R)
    (hComplex : ∃ z : σ → ℂ, eval z (map toComplex P) ≠ 0) :
    map toReal P ≠ 0 ∧ ∃ x : σ → ℝ, eval x (map toReal P) ≠ 0 := by
  obtain ⟨z, hz⟩ := hComplex
  have hP : P ≠ 0 := by
    intro hzero
    subst P
    apply hz
    simp
  have hReal : map toReal P ≠ 0 := by
    simpa using (MvPolynomial.map_injective toReal htoReal).ne hP
  exact ⟨hReal, exists_real_eval_ne_zero (map toReal P) hReal⟩

/-- Integer-coefficient specialization bridge. -/
theorem int_real_nonvanishing_of_complex_nonvanishing
    {σ : Type*} (P : MvPolynomial σ ℤ)
    (hComplex : ∃ z : σ → ℂ,
      eval z (map (Int.castRingHom ℂ) P) ≠ 0) :
    map (Int.castRingHom ℝ) P ≠ 0 ∧
      ∃ x : σ → ℝ, eval x (map (Int.castRingHom ℝ) P) ≠ 0 :=
  map_real_ne_zero_and_exists_eval_of_complex_eval
    (Int.castRingHom ℂ) (Int.castRingHom ℝ) Int.cast_injective P hComplex

/-- Rational-coefficient specialization bridge. -/
theorem rat_real_nonvanishing_of_complex_nonvanishing
    {σ : Type*} (P : MvPolynomial σ ℚ)
    (hComplex : ∃ z : σ → ℂ,
      eval z (map (Rat.castHom ℂ) P) ≠ 0) :
    map (Rat.castHom ℝ) P ≠ 0 ∧
      ∃ x : σ → ℝ, eval x (map (Rat.castHom ℝ) P) ≠ 0 :=
  map_real_ne_zero_and_exists_eval_of_complex_eval
    (Rat.castHom ℂ) (Rat.castHom ℝ) Rat.cast_injective P hComplex

/-! ## Finite matrices -/

/-- Entrywise specialization of a polynomial matrix. -/
noncomputable def specializeMatrix
    {R S σ m n : Type*} [CommSemiring R] [CommSemiring S]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix m n (MvPolynomial σ R)) : Matrix m n S :=
  A.map (MvPolynomial.eval₂Hom coeff x)

@[simp]
theorem specializeMatrix_apply
    {R S σ m n : Type*} [CommSemiring R] [CommSemiring S]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix m n (MvPolynomial σ R)) (i : m) (j : n) :
    specializeMatrix coeff x A i j = eval₂ coeff x (A i j) :=
  rfl

/-- Determinants commute with entrywise polynomial specialization. -/
theorem det_specializeMatrix
    {R S σ n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n]
    (coeff : R →+* S) (x : σ → S)
    (A : Matrix n n (MvPolynomial σ R)) :
    (specializeMatrix coeff x A).det = eval₂ coeff x A.det := by
  simpa [specializeMatrix] using
    (RingHom.map_det (MvPolynomial.eval₂Hom coeff x) A).symm

/-- A square matrix over a field with nonzero determinant acts injectively on
column vectors. -/
theorem mulVec_injective_of_det_ne_zero
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hdet : A.det ≠ 0) :
    Function.Injective A.mulVec := by
  intro v w hvw
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  rw [Matrix.mulVec_sub, hvw, sub_self]

/-- An injective finite matrix over a field has a nonzero full-column minor.
This is the elementary row-basis extraction needed before applying a
determinant polynomial certificate. -/
theorem exists_fullColumnMinor_of_mulVec_injective
    {K m n : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n K) (hA : Function.Injective A.mulVec) :
    ∃ rows : n → m, (A.submatrix rows id).det ≠ 0 := by
  classical
  have hLin : Function.Injective A.mulVecLin := by
    intro v w hvw
    apply hA
    simpa only [Matrix.mulVecLin_apply] using hvw
  have hRank : A.rank = Fintype.card n := by
    have hNullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [LinearMap.ker_eq_bot.mpr hLin, finrank_bot, add_zero,
      Module.finrank_fintype_fun_eq_card] at hNullity
    exact hNullity
  have hFinrankRows :
      Module.finrank K (Submodule.span K (Set.range A.row)) = Fintype.card n := by
    rw [← Matrix.rank_eq_finrank_span_row A]
    exact hRank
  have hSpanRows : Submodule.span K (Set.range A.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq <| by
      rw [hFinrankRows, Module.finrank_fintype_fun_eq_card]
  have hSelect :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  rw [hFinrankRows] at hSelect
  obtain ⟨f, hfMem, _, hfIndependent⟩ := hSelect
  have hfRows : ∀ i, ∃ r : m, A.row r = f i := fun i ↦ hfMem i
  choose selected hSelected using hfRows
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  let rows : n → m := fun i ↦ selected (e i)
  have hRowsIndependent :
      LinearIndependent K (A.submatrix rows id).row := by
    have hRowEq : (A.submatrix rows id).row = f ∘ e := by
      funext i j
      change A (selected (e i)) j = f (e i) j
      exact congrFun (hSelected (e i)) j
    rw [hRowEq]
    exact hfIndependent.comp e e.injective
  have hUnitMatrix : IsUnit (A.submatrix rows id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hRowsIndependent
  have hUnitDet : IsUnit (A.submatrix rows id).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hUnitMatrix
  exact ⟨rows, isUnit_iff_ne_zero.mp hUnitDet⟩

/-- For a square integer-coefficient polynomial matrix, injectivity at one
complex specialization implies injectivity at some real specialization.
No degree bound on the entries is needed. -/
theorem exists_real_specialization_injective_of_complex_square
    {σ n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (MvPolynomial σ ℤ))
    (hComplex : ∃ z : σ → ℂ,
      Function.Injective (specializeMatrix (Int.castRingHom ℂ) z A).mulVec) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  obtain ⟨z, hz⟩ := hComplex
  have hdetComplex : (specializeMatrix (Int.castRingHom ℂ) z A).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hvzero⟩ :=
      (Matrix.exists_mulVec_eq_zero_iff (M :=
        specializeMatrix (Int.castRingHom ℂ) z A)).mpr hdet
    apply hv
    apply hz
    simpa using hvzero
  have hPolynomialComplex : ∃ z : σ → ℂ,
      eval z (map (Int.castRingHom ℂ) A.det) ≠ 0 := by
    refine ⟨z, ?_⟩
    rw [eval_map, ← det_specializeMatrix]
    exact hdetComplex
  obtain ⟨_, x, hx⟩ :=
    int_real_nonvanishing_of_complex_nonvanishing A.det hPolynomialComplex
  refine ⟨x, mulVec_injective_of_det_ne_zero _ ?_⟩
  rw [det_specializeMatrix]
  simpa only [eval_map] using hx

/-- Rectangular full-column-rank bridge from a certified nonzero complex
full-column minor.  The row selector `rows` need not be assumed injective: a
nonzero determinant already forces the selected rows to be distinct enough.
The conclusion is injectivity of the entire real-specialized matrix. -/
theorem exists_real_specialization_injective_of_complex_minor
    {σ m n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix m n (MvPolynomial σ ℤ)) (rows : n → m)
    (hComplex : ∃ z : σ → ℂ,
      (specializeMatrix (Int.castRingHom ℂ) z
        (A.submatrix rows id)).det ≠ 0) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  have hMinorComplex : ∃ z : σ → ℂ,
      Function.Injective
        (specializeMatrix (Int.castRingHom ℂ) z
          (A.submatrix rows id)).mulVec := by
    obtain ⟨z, hz⟩ := hComplex
    exact ⟨z, mulVec_injective_of_det_ne_zero _ hz⟩
  obtain ⟨x, hMinorReal⟩ :=
    exists_real_specialization_injective_of_complex_square
      (A.submatrix rows id) hMinorComplex
  refine ⟨x, ?_⟩
  intro v w hvw
  apply hMinorReal
  funext i
  simpa [specializeMatrix, Matrix.mulVec] using congrFun hvw (rows i)

/-- Full rectangular form.  An injective complex specialization supplies a
nonzero full-column minor; the same minor polynomial is nonzero at some real
point, where it certifies injectivity of the whole matrix.  Again the entries
may have arbitrary degree, so this includes the requested linear-entry case. -/
theorem exists_real_specialization_injective_of_complex
    {σ m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (MvPolynomial σ ℤ))
    (hComplex : ∃ z : σ → ℂ,
      Function.Injective (specializeMatrix (Int.castRingHom ℂ) z A).mulVec) :
    ∃ x : σ → ℝ,
      Function.Injective (specializeMatrix (Int.castRingHom ℝ) x A).mulVec := by
  obtain ⟨z, hz⟩ := hComplex
  obtain ⟨rows, hrows⟩ := exists_fullColumnMinor_of_mulVec_injective
    (specializeMatrix (Int.castRingHom ℂ) z A) hz
  apply exists_real_specialization_injective_of_complex_minor A rows
  refine ⟨z, ?_⟩
  simpa [specializeMatrix, Matrix.submatrix_map] using hrows

end ComplexRealSpecialization

end RB31E2E


end
end BundlePart9

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_010/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_010.json"

section BundlePart10
/- Source: Papers/RigidityPolynomialRank.lean -/




@[expose] public section

/-!
# Generic rational-function rank is the attained maximum real rank

Both inequalities are proved by nonzero minors of the actual polynomial
matrix. Thus the use of rational function fields in the incidence proof is
identified with maximum rank over real Euclidean pin placements.
-/

namespace Papers.Rigidity.PolynomialRank

noncomputable section

open MvPolynomial
open RB31E2E.ComplexRealSpecialization

/-- A finite matrix has a square minor of order exactly its rank with
nonzero determinant. The selected rows and columns are actual labels. -/
theorem exists_rank_minor
    {k m n : Type*} [Field k] [Fintype m] [Fintype n]
    (A : Matrix m n k) :
    ∃ (rows : Fin A.rank → m) (cols : Fin A.rank → n),
      (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hSelect := Submodule.exists_fun_fin_finrank_span_eq k (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols] at hSelect
  obtain ⟨f, hfMem, _, hfIndependent⟩ := hSelect
  choose cols hcols using hfMem
  let B : Matrix m (Fin A.rank) k := A.submatrix id cols
  have hB : LinearIndependent k B.col := by
    have heq : B.col = f := by
      funext i j
      exact congrFun (hcols i) j
    rw [heq]
    exact hfIndependent
  obtain ⟨rows, hrows⟩ := exists_fullColumnMinor_of_mulVec_injective B
    (Matrix.mulVec_injective_iff.mpr hB)
  exact ⟨rows, cols, hrows⟩

variable {σ m n : Type*} [Fintype m] [Fintype n]

abbrev GenericField (σ : Type*) := FractionRing (MvPolynomial σ ℚ)

def genericMatrix (A : Matrix m n (MvPolynomial σ ℚ)) :
    Matrix m n (GenericField σ) :=
  A.map (algebraMap (MvPolynomial σ ℚ) (GenericField σ))

def realMatrix (A : Matrix m n (MvPolynomial σ ℚ)) (x : σ → ℝ) :
    Matrix m n ℝ :=
  A.map (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)

theorem generic_minor_det {r : ℕ} (A : Matrix m n (MvPolynomial σ ℚ))
    (rows : Fin r → m) (cols : Fin r → n) :
    ((genericMatrix A).submatrix rows cols).det =
      algebraMap (MvPolynomial σ ℚ) (GenericField σ) (A.submatrix rows cols).det := by
  exact (RingHom.map_det (algebraMap (MvPolynomial σ ℚ) (GenericField σ))
    (A.submatrix rows cols)).symm

theorem real_minor_det {r : ℕ} (A : Matrix m n (MvPolynomial σ ℚ))
    (x : σ → ℝ) (rows : Fin r → m) (cols : Fin r → n) :
    ((realMatrix A x).submatrix rows cols).det =
      MvPolynomial.eval₂ (Rat.castHom ℝ) x (A.submatrix rows cols).det := by
  exact (RingHom.map_det (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)
    (A.submatrix rows cols)).symm

/-- Specialization cannot increase the rank over the rational function
field, at any real coordinate tuple. -/
theorem realMatrix_rank_le_generic (A : Matrix m n (MvPolynomial σ ℚ)) (x : σ → ℝ) :
    (realMatrix A x).rank ≤ (genericMatrix A).rank := by
  classical
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (realMatrix A x)
  have hpoly : (A.submatrix rows cols).det ≠ 0 := by
    intro hz
    rw [real_minor_det, hz, MvPolynomial.eval₂_zero] at hdet
    exact hdet rfl
  have hgeneric : ((genericMatrix A).submatrix rows cols).det ≠ 0 := by
    rw [generic_minor_det]
    intro hz
    exact hpoly ((IsFractionRing.injective (MvPolynomial σ ℚ) (GenericField σ))
      (by simpa using hz))
  have hminor := Matrix.rank_of_det_ne_zero hgeneric
  have hle := Matrix.rank_submatrix_le (genericMatrix A) rows cols
  simpa only [hminor, Fintype.card_fin] using hle

/-- A nonzero generic maximal minor has a real nonvanishing specialization.
This proves attainment, not only an upper bound. -/
theorem exists_realMatrix_rank_eq_generic (A : Matrix m n (MvPolynomial σ ℚ)) :
    ∃ x : σ → ℝ, (realMatrix A x).rank = (genericMatrix A).rank := by
  classical
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (genericMatrix A)
  have hpoly : (A.submatrix rows cols).det ≠ 0 := by
    intro hz
    rw [generic_minor_det, hz, map_zero] at hdet
    exact hdet rfl
  have hrealPoly : MvPolynomial.map (Rat.castHom ℝ) (A.submatrix rows cols).det ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective (Rat.castHom ℝ) Rat.cast_injective).ne hpoly
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero _ hrealPoly
  have hminorDet : ((realMatrix A x).submatrix rows cols).det ≠ 0 := by
    rw [real_minor_det]
    simpa only [MvPolynomial.eval_map] using hx
  have hrank := Matrix.rank_of_det_ne_zero hminorDet
  have hle := Matrix.rank_submatrix_le (realMatrix A x) rows cols
  refine ⟨x, le_antisymm (realMatrix_rank_le_generic A x) ?_⟩
  simpa only [hrank, Fintype.card_fin] using hle

/-- Every specialization that is injective on the rational polynomial
ring has the generic rank. In particular, the paper's usual
algebraically independent coordinates are maximum-rank coordinates. -/
theorem realMatrix_rank_eq_generic_of_eval_injective
    (A : Matrix m n (MvPolynomial σ ℚ)) (x : σ → ℝ)
    (hx : Function.Injective (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)) :
    (realMatrix A x).rank = (genericMatrix A).rank := by
  classical
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor (genericMatrix A)
  have hpoly : (A.submatrix rows cols).det ≠ 0 := by
    intro hz
    rw [generic_minor_det, hz, map_zero] at hdet
    exact hdet rfl
  have hminorDet : ((realMatrix A x).submatrix rows cols).det ≠ 0 := by
    rw [real_minor_det]
    exact fun hz => hpoly (hx (by simpa using hz))
  have hrank := Matrix.rank_of_det_ne_zero hminorDet
  have hle := Matrix.rank_submatrix_le (realMatrix A x) rows cols
  apply le_antisymm (realMatrix_rank_le_generic A x)
  simpa only [hrank, Fintype.card_fin] using hle

end

end Papers.Rigidity.PolynomialRank

end
end BundlePart10

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_011/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_011.json"

section BundlePart11
/- Source: Papers/RigidityZheng_Linear_Vec3Twist.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/Vec3Twist.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Module visibility and import paths adapted; umbrella Mathlib imports
replaced by the definitions and tactics used in this file.
-/





@[expose] public section

/-!
# Three-dimensional twists and the Split--Klein form

This file contains only explicit linear algebra.  A twist is an angular
velocity together with a translational velocity.  Its value at a point
is the usual infinitesimal rigid-body velocity.  No rigidity theorem is
assumed here.
-/

namespace RB31E2E

/-- Coordinate vectors in dimension three. -/
abbrev Vec3 (k : Type*) := Fin 3 → k

namespace Vec3

/-- The bilinear coordinate dot product (not a Hermitian product). -/
def dot {k : Type*} [CommSemiring k] (x y : Vec3 k) : k :=
  ∑ i, x i * y i

/-- The coordinate cross product. -/
def cross {k : Type*} [CommRing k] (x y : Vec3 k) : Vec3 k :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

@[simp] theorem cross_self {k : Type*} [CommRing k] (x : Vec3 k) :
    cross x x = 0 := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_sub_left {k : Type*} [CommRing k] (x y p : Vec3 k) :
    cross (x - y) p = cross x p - cross y p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_add_left {k : Type*} [CommRing k] (x y p : Vec3 k) :
    cross (x + y) p = cross x p + cross y p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_left {k : Type*} [CommRing k] (a : k) (x p : Vec3 k) :
    cross (a • x) p = a • cross x p := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem dot_cross_self_left {k : Type*} [CommRing k] (x p : Vec3 k) :
    dot x (cross x p) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

end Vec3

/-- Angular and translational parts of an infinitesimal rigid motion. -/
abbrev Twist (k : Type*) := Vec3 k × Vec3 k

namespace Twist

/-- Velocity induced by a twist at the point `p`. -/
def eval {k : Type*} [CommRing k] (X : Twist k) (p : Vec3 k) : Vec3 k :=
  X.2 + Vec3.cross X.1 p

/-- The split Klein quadratic polynomial `ω · v`. -/
def splitKlein {k : Type*} [CommRing k] (X : Twist k) : k :=
  Vec3.dot X.1 X.2

@[simp] theorem splitKlein_neg {k : Type*} [CommRing k] (X : Twist k) :
    splitKlein (-X) = splitKlein X := by
  simp [splitKlein, Vec3.dot]

theorem splitKlein_sub_comm {k : Type*} [CommRing k] (X Y : Twist k) :
    splitKlein (X - Y) = splitKlein (Y - X) := by
  rw [show Y - X = -(X - Y) by abel, splitKlein_neg]

theorem splitKlein_smul {k : Type*} [CommRing k] (a : k) (X : Twist k) :
    splitKlein (a • X) = a ^ 2 * splitKlein X := by
  simp [splitKlein, Vec3.dot, Fin.sum_univ_succ]
  ring

/-- Two body twists assign the same velocity to the shared pin. -/
def CompatibleAt {k : Type*} [CommRing k]
    (X Y : Twist k) (p : Vec3 k) : Prop :=
  eval X p = eval Y p

theorem eval_sub {k : Type*} [CommRing k] (X Y : Twist k) (p : Vec3 k) :
    eval (X - Y) p = eval X p - eval Y p := by
  change (X.2 - Y.2) + Vec3.cross (X.1 - Y.1) p =
    (X.2 + Vec3.cross X.1 p) - (Y.2 + Vec3.cross Y.1 p)
  rw [Vec3.cross_sub_left]
  abel

theorem splitKlein_eq_zero_of_eval_eq_zero {k : Type*} [CommRing k]
    (X : Twist k) (p : Vec3 k) (h : eval X p = 0) :
    splitKlein X = 0 := by
  have hv : X.2 = -Vec3.cross X.1 p := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [eval] using h
  rw [splitKlein, hv]
  simp only [Vec3.dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  change -Vec3.dot X.1 (Vec3.cross X.1 p) = 0
  rw [Vec3.dot_cross_self_left]
  exact neg_zero

theorem splitKlein_sub_eq_zero_of_compatibleAt {k : Type*} [CommRing k]
    (X Y : Twist k) (p : Vec3 k) (h : CompatibleAt X Y p) :
    splitKlein (X - Y) = 0 := by
  apply splitKlein_eq_zero_of_eval_eq_zero (X - Y) p
  rw [eval_sub]
  exact sub_eq_zero.mpr h

end Twist

end RB31E2E


end
end BundlePart11

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_012/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_012.json"

section BundlePart12
/- Source: Papers/RigidityZheng_Linear_PinFibres.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/PinFibres.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Module visibility and import paths are adapted; the linear_combination
tactic is imported explicitly after removal of the upstream Mathlib umbrella.
-/



@[expose] public section

/-!
# Elementary pin fibres

The zero set of the velocity of a nonzero twist is an affine line parallel to
its angular part.  Everything here is coordinate algebra over an arbitrary
field; no genericity, characteristic, or algebraic-geometry hypothesis is
used.
-/

namespace RB31E2E

namespace Vec3

/-- The cross product is additive in its second argument. -/
theorem cross_sub_right {k : Type*} [CommRing k] (x p q : Vec3 k) :
    cross x (p - q) = cross x p - cross x q := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

/-- Over a field, the kernel of `p ↦ ω × p` is the line spanned by a
nonzero vector `ω`. -/
theorem cross_eq_zero_iff_eq_smul {k : Type*} [Field k]
    (ω d : Vec3 k) (hω : ω ≠ 0) :
    cross ω d = 0 ↔ ∃ c : k, d = c • ω := by
  constructor
  · intro hcross
    have hc0 : ω 1 * d 2 - ω 2 * d 1 = 0 := by
      simpa [cross] using congrFun hcross (0 : Fin 3)
    have hc1 : ω 2 * d 0 - ω 0 * d 2 = 0 := by
      simpa [cross] using congrFun hcross (1 : Fin 3)
    have hc2 : ω 0 * d 1 - ω 1 * d 0 = 0 := by
      simpa [cross] using congrFun hcross (2 : Fin 3)
    have hcoord : ∃ i : Fin 3, ω i ≠ 0 := by
      by_contra h
      apply hω
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    fin_cases i
    · change ω 0 ≠ 0 at hi
      refine ⟨d 0 / ω 0, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 0 / ω 0 * ω 0
        exact (div_mul_cancel₀ (d 0) hi).symm
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 0 / ω 0 * ω 1
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc2
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 0 / ω 0 * ω 2
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc1
    · change ω 1 ≠ 0 at hi
      refine ⟨d 1 / ω 1, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 1 / ω 1 * ω 0
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc2
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 1 / ω 1 * ω 1
        exact (div_mul_cancel₀ (d 1) hi).symm
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 1 / ω 1 * ω 2
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc0
    · change ω 2 ≠ 0 at hi
      refine ⟨d 2 / ω 2, ?_⟩
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 0 = d 2 / ω 2 * ω 0
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination hc1
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 1 = d 2 / ω 2 * ω 1
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hi).2
        linear_combination -hc0
      · simp only [Pi.smul_apply, smul_eq_mul]
        change d 2 = d 2 / ω 2 * ω 2
        exact (div_mul_cancel₀ (d 2) hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    fin_cases i <;> simp [cross] <;> ring

end Vec3

namespace Twist

/-- A pin solution puts its twist on the split--Klein quadric. -/
theorem splitKlein_eq_zero_of_pin_solution {k : Type*} [Field k]
    (X : Twist k) (p : Vec3 k) (hp : eval X p = 0) :
    splitKlein X = 0 :=
  splitKlein_eq_zero_of_eval_eq_zero X p hp

/-- A nonzero twist admitting a stationary pin has nonzero angular part. -/
theorem angular_ne_zero_of_ne_zero_of_eval_eq_zero {k : Type*} [Field k]
    (X : Twist k) (p : Vec3 k) (hX : X ≠ 0) (hp : eval X p = 0) :
    X.1 ≠ 0 := by
  intro hω
  have hcross : Vec3.cross X.1 p = 0 := by
    funext i
    fin_cases i <;> simp [Vec3.cross, hω]
  have hv : X.2 = 0 := by
    rw [eval, hcross, add_zero] at hp
    exact hp
  exact hX (Prod.ext hω hv)

/-- Two stationary pins of a twist differ in a direction killed by its
angular cross-product map. -/
theorem cross_pin_sub_eq_zero {k : Type*} [Field k]
    (X : Twist k) (p p' : Vec3 k)
    (hp : eval X p = 0) (hp' : eval X p' = 0) :
    Vec3.cross X.1 (p' - p) = 0 := by
  rw [Vec3.cross_sub_right]
  have hcross : Vec3.cross X.1 p' = Vec3.cross X.1 p := by
    apply add_left_cancel (a := X.2)
    exact hp'.trans hp.symm
  rw [hcross, sub_self]

/-- If the angular part is nonzero, any two stationary pins differ by a
scalar multiple of it. -/
theorem pin_sub_eq_smul_angular {k : Type*} [Field k]
    (X : Twist k) (p p' : Vec3 k) (hω : X.1 ≠ 0)
    (hp : eval X p = 0) (hp' : eval X p' = 0) :
    ∃ c : k, p' - p = c • X.1 :=
  (Vec3.cross_eq_zero_iff_eq_smul X.1 (p' - p) hω).mp
    (cross_pin_sub_eq_zero X p p' hp hp')

/-- Exact affine-collinearity statement for three stationary pins: both
differences from the first pin are scalar multiples of the angular part. -/
theorem three_pin_solutions_collinear {k : Type*} [Field k]
    (X : Twist k) (p₀ p₁ p₂ : Vec3 k) (hω : X.1 ≠ 0)
    (hp₀ : eval X p₀ = 0) (hp₁ : eval X p₁ = 0)
    (hp₂ : eval X p₂ = 0) :
    ∃ c₁ c₂ : k, p₁ - p₀ = c₁ • X.1 ∧ p₂ - p₀ = c₂ • X.1 := by
  obtain ⟨c₁, hc₁⟩ := pin_sub_eq_smul_angular X p₀ p₁ hω hp₀ hp₁
  obtain ⟨c₂, hc₂⟩ := pin_sub_eq_smul_angular X p₀ p₂ hω hp₀ hp₂
  exact ⟨c₁, c₂, hc₁, hc₂⟩

/-- A formulation needing only that the twist itself is nonzero: one pin
solution already forces the angular direction to be nonzero. -/
theorem three_pin_solutions_collinear_of_ne_zero {k : Type*} [Field k]
    (X : Twist k) (p₀ p₁ p₂ : Vec3 k) (hX : X ≠ 0)
    (hp₀ : eval X p₀ = 0) (hp₁ : eval X p₁ = 0)
    (hp₂ : eval X p₂ = 0) :
    ∃ c₁ c₂ : k, p₁ - p₀ = c₁ • X.1 ∧ p₂ - p₀ = c₂ • X.1 := by
  apply three_pin_solutions_collinear X p₀ p₁ p₂
    (angular_ne_zero_of_ne_zero_of_eval_eq_zero X p₀ hX hp₀)
    hp₀ hp₁ hp₂

end Twist

end RB31E2E


end
end BundlePart12

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_013/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_013.json"

section BundlePart13
/- Source: Papers/RigidityZheng_Linear_PinRank.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/PinRank.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Module visibility and import paths are adapted; finite-dimensional
rank-nullity is imported explicitly after removal of the upstream Mathlib umbrella.
-/




@[expose] public section

/-!
# Linear rank paid by one and two pins

This file proves the elementary `3,5,6` necessity bounds at the level
of one relative six-dimensional twist.
-/

namespace RB31E2E

namespace Twist

variable {k : Type*} [Field k]

/-- Evaluation at a pin is a linear map from twists to velocities. -/
def evalLinear (p : Vec3 k) : Twist k →ₗ[k] Vec3 k where
  toFun X := eval X p
  map_add' X Y := by
    change (X.2 + Y.2) + Vec3.cross (X.1 + Y.1) p =
      (X.2 + Vec3.cross X.1 p) + (Y.2 + Vec3.cross Y.1 p)
    rw [Vec3.cross_add_left]
    abel
  map_smul' a X := by
    change a • X.2 + Vec3.cross (a • X.1) p =
      a • (X.2 + Vec3.cross X.1 p)
    rw [Vec3.cross_smul_left, smul_add]

@[simp] theorem evalLinear_apply (p : Vec3 k) (X : Twist k) :
    evalLinear p X = eval X p := rfl

/-- Simultaneous evaluation at two pins. -/
def twoPinLinear (p q : Vec3 k) : Twist k →ₗ[k] (Vec3 k × Vec3 k) :=
  (evalLinear p).prod (evalLinear q)

@[simp] theorem twoPinLinear_apply (p q : Vec3 k) (X : Twist k) :
    twoPinLinear p q X = (eval X p, eval X q) := rfl

theorem finrank_vec3 : Module.finrank k (Vec3 k) = 3 := by
  simp [Vec3]

theorem finrank_twist : Module.finrank k (Twist k) = 6 := by
  simp [Twist, Vec3]

/-- One pin contributes at most three independent linear constraints. -/
theorem finrank_range_evalLinear_le_three (p : Vec3 k) :
    Module.finrank k (LinearMap.range (evalLinear p)) ≤ 3 := by
  calc
    Module.finrank k (LinearMap.range (evalLinear p)) ≤
        Module.finrank k (Vec3 k) := (LinearMap.range (evalLinear p)).finrank_le
    _ = 3 := finrank_vec3 (k := k)

def e₀ : Vec3 k := fun i ↦ if i = 0 then 1 else 0

private theorem e₀_ne_zero : (e₀ : Vec3 k) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  simp [e₀] at h0

/-- Two pin evaluations always have a nonzero relative rotation in their kernel. -/
theorem exists_ne_zero_mem_ker_twoPinLinear (p q : Vec3 k) :
    ∃ X : Twist k, X ≠ 0 ∧ X ∈ LinearMap.ker (twoPinLinear p q) := by
  by_cases hpq : p = q
  · subst q
    let X : Twist k := (e₀, -Vec3.cross e₀ p)
    refine ⟨X, ?_, ?_⟩
    · intro hX
      have hfst := congrArg Prod.fst hX
      exact e₀_ne_zero (by simpa [X] using hfst)
    · rw [LinearMap.mem_ker]
      apply Prod.ext <;> simp [X, eval]
  · let ω : Vec3 k := q - p
    let X : Twist k := (ω, -Vec3.cross ω p)
    have hω : ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
    refine ⟨X, ?_, ?_⟩
    · intro hX
      have hfst := congrArg Prod.fst hX
      exact hω (by simpa [X] using hfst)
    · rw [LinearMap.mem_ker]
      apply Prod.ext
      · simp [X, eval]
      · change -Vec3.cross ω p + Vec3.cross ω q = 0
        rw [show -Vec3.cross ω p + Vec3.cross ω q =
          Vec3.cross ω q - Vec3.cross ω p by abel]
        rw [← Vec3.cross_sub_right]
        change Vec3.cross (q - p) (q - p) = 0
        exact Vec3.cross_self (q - p)

/-- Two pins contribute at most five independent linear constraints. -/
theorem finrank_range_twoPinLinear_le_five (p q : Vec3 k) :
    Module.finrank k (LinearMap.range (twoPinLinear p q)) ≤ 5 := by
  obtain ⟨X, hX, hXker⟩ := exists_ne_zero_mem_ker_twoPinLinear p q
  have hker : LinearMap.ker (twoPinLinear p q) ≠ ⊥ := by
    intro hk
    have : X = 0 := by
      have : X ∈ (⊥ : Submodule k (Twist k)) := hk ▸ hXker
      simpa using this
    exact hX this
  have hkerRank : 1 ≤ Module.finrank k (LinearMap.ker (twoPinLinear p q)) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hrankNullity := (twoPinLinear p q).finrank_range_add_finrank_ker
  rw [finrank_twist (k := k)] at hrankNullity
  omega

/-- Any linear family of constraints on one relative twist has rank at most six. -/
theorem finrank_range_le_six {M : Type*} [AddCommGroup M] [Module k M]
    (L : Twist k →ₗ[k] M) :
    Module.finrank k (LinearMap.range L) ≤ 6 := by
  calc
    Module.finrank k (LinearMap.range L) ≤ Module.finrank k (Twist k) :=
      LinearMap.finrank_range_le L
    _ = 6 := finrank_twist (k := k)

/-- Evaluation at every occurrence in one pin bundle. -/
noncomputable def bundleLinear {I : Type*} (p : I → Vec3 k) :
    Twist k →ₗ[k] (I → Vec3 k) :=
  LinearMap.pi fun i ↦ evalLinear (p i)

@[simp] theorem bundleLinear_apply {I : Type*} (p : I → Vec3 k)
    (X : Twist k) (i : I) :
    bundleLinear p X i = eval X (p i) := by
  simp [bundleLinear]

theorem finrank_bundleTarget (m : ℕ) :
    Module.finrank k (Fin m → Vec3 k) = m * 3 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_vec3 (k := k)]

private theorem exists_ne_zero_mem_ker_bundleLinear_two
    (p : Fin 2 → Vec3 k) :
    ∃ X : Twist k, X ≠ 0 ∧ X ∈ LinearMap.ker (bundleLinear p) := by
  obtain ⟨X, hX, hXker⟩ :=
    exists_ne_zero_mem_ker_twoPinLinear (p 0) (p 1)
  refine ⟨X, hX, ?_⟩
  rw [LinearMap.mem_ker]
  have hpair : twoPinLinear (p 0) (p 1) X = 0 :=
    LinearMap.mem_ker.mp hXker
  funext i
  fin_cases i
  · have h0 := congrArg Prod.fst hpair
    simpa using h0
  · have h1 := congrArg Prod.snd hpair
    simpa using h1

/--
The complete linear version of the `0,3,5,6` table: a bundle of `m`
pins imposes rank at most `pinCapacity m` on one relative twist.
-/
theorem finrank_range_bundleLinear_le_pinCapacity
    (m : ℕ) (p : Fin m → Vec3 k) :
    Module.finrank k (LinearMap.range (bundleLinear p)) ≤ pinCapacity m := by
  rcases m with _ | _ | _ | m
  · have h := (LinearMap.range (bundleLinear p)).finrank_le
    rw [finrank_bundleTarget] at h
    change Module.finrank k (LinearMap.range (bundleLinear p)) ≤ 0
    exact h
  · have h := (LinearMap.range (bundleLinear p)).finrank_le
    rw [finrank_bundleTarget] at h
    change Module.finrank k (LinearMap.range (bundleLinear p)) ≤ 3
    exact h
  · obtain ⟨X, hX, hXker⟩ := exists_ne_zero_mem_ker_bundleLinear_two p
    have hker : LinearMap.ker (bundleLinear p) ≠ ⊥ := by
      intro hk
      have : X = 0 := by
        have : X ∈ (⊥ : Submodule k (Twist k)) := hk ▸ hXker
        simpa using this
      exact hX this
    have hkerRank : 1 ≤ Module.finrank k (LinearMap.ker (bundleLinear p)) :=
      Submodule.one_le_finrank_iff.mpr hker
    have hrankNullity := (bundleLinear p).finrank_range_add_finrank_ker
    rw [finrank_twist (k := k)] at hrankNullity
    simp only [pinCapacity]
    omega
  · simpa [pinCapacity] using
      (finrank_range_le_six (k := k) (bundleLinear p))

end Twist

end RB31E2E


end
end BundlePart13

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_014/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_014.json"

section BundlePart14
/- Source: Papers/RigidityZheng_Linear_TwistSystem.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Linear/TwistSystem.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Occurrence-level body twist systems

The endpoints are arbitrary functions on an occurrence type.  This
keeps parallel pins distinct and makes the semantics independent of a
chosen graph library representation.
-/

namespace RB31E2E

variable {k W E : Type*} [CommRing k]

/-- Every pin occurrence receives the same velocity from its two bodies. -/
def IsTwistMotion (src dst : E → W) (p : E → Vec3 k)
    (X : W → Twist k) : Prop :=
  ∀ e, Twist.eval (X (src e)) (p e) = Twist.eval (X (dst e)) (p e)

/-- A twist assignment is a single global Euclidean infinitesimal motion. -/
def IsDiagonalTwist (X : W → Twist k) : Prop :=
  ∃ Y : Twist k, X = fun _ ↦ Y

/-- At this pin placement the only body-twist motions are diagonal. -/
def TwistRigidAt (src dst : E → W) (p : E → Vec3 k) : Prop :=
  ∀ X : W → Twist k, IsTwistMotion src dst p X → IsDiagonalTwist X

/-- There exists a pin placement at which the twist system is rigid. -/
def HasRigidTwistRealization (src dst : E → W) : Prop :=
  ∃ p : E → Vec3 k, TwistRigidAt src dst p

theorem isTwistMotion_swap (src dst : E → W) (p : E → Vec3 k)
    (X : W → Twist k) :
    IsTwistMotion src dst p X ↔ IsTwistMotion dst src p X := by
  constructor <;> intro h e <;> exact (h e).symm

theorem twistRigidAt_swap (src dst : E → W) (p : E → Vec3 k) :
    TwistRigidAt src dst p ↔ TwistRigidAt dst src p := by
  constructor <;> intro h X hX
  · exact h X ((isTwistMotion_swap src dst p X).mpr hX)
  · exact h X ((isTwistMotion_swap src dst p X).mp hX)

theorem hasRigidTwistRealization_swap (src dst : E → W) :
    HasRigidTwistRealization (k := k) src dst ↔
      HasRigidTwistRealization (k := k) dst src := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (twistRigidAt_swap src dst p).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (twistRigidAt_swap src dst p).mpr hp⟩

theorem isTwistMotion_diagonal (src dst : E → W) (p : E → Vec3 k)
    (Y : Twist k) :
    IsTwistMotion src dst p (fun _ ↦ Y) := by
  intro e
  rfl

theorem IsDiagonalTwist.isTwistMotion {src dst : E → W} {p : E → Vec3 k}
    {X : W → Twist k} (hX : IsDiagonalTwist X) :
    IsTwistMotion src dst p X := by
  obtain ⟨Y, rfl⟩ := hX
  exact isTwistMotion_diagonal src dst p Y

theorem eval_sub_eq_zero_of_isTwistMotion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    (hX : IsTwistMotion src dst p X) (e : E) :
    Twist.eval (X (src e) - X (dst e)) (p e) = 0 := by
  rw [Twist.eval_sub]
  exact sub_eq_zero.mpr (hX e)

/-- Pin compatibility forces a Split--Klein null difference. -/
theorem splitKlein_sub_eq_zero_of_isTwistMotion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    (hX : IsTwistMotion src dst p X) (e : E) :
    Twist.splitKlein (X (src e) - X (dst e)) = 0 :=
  Twist.splitKlein_sub_eq_zero_of_compatibleAt _ _ _ (hX e)

end RB31E2E


end
end BundlePart14

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_015/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_015.json"

section BundlePart15
/- Source: Papers/RigidityZheng_Algebra_GroundedTwist.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/GroundedTwist.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Grounding the body-twist system

Fixing one body removes the six-dimensional diagonal subspace.  This
file proves that the resulting explicit linear operator is injective
exactly when the ungrounded pin system has only diagonal motions.
-/

namespace RB31E2E

variable {k W E : Type*} [Field k] [DecidableEq W]

/-- Bodies other than the selected grounded body. -/
abbrev OffRoot (root : W) := {w : W // w ≠ root}

/-- Extend an off-root assignment by zero at the grounded body. -/
def extendGrounded (root : W) (X : OffRoot root → Twist k) : W → Twist k :=
  fun w ↦ if h : w = root then 0 else X ⟨w, h⟩

@[simp] theorem extendGrounded_root (root : W) (X : OffRoot root → Twist k) :
    extendGrounded root X root = 0 := by
  simp [extendGrounded]

@[simp] theorem extendGrounded_offRoot (root : W) (X : OffRoot root → Twist k)
    (w : OffRoot root) :
    extendGrounded root X w.1 = X w := by
  simp [extendGrounded, w.2]

/-- Grounded extension as a linear map. -/
def extendGroundedLinear (root : W) :
    (OffRoot root → Twist k) →ₗ[k] (W → Twist k) where
  toFun := extendGrounded root
  map_add' X Y := by
    funext w
    by_cases h : w = root <;> simp [extendGrounded, h]
  map_smul' a X := by
    funext w
    by_cases h : w = root <;> simp [extendGrounded, h]

/-- Difference of two selected body twists. -/
def assignmentDifferenceLinear (u v : W) :
    (W → Twist k) →ₗ[k] Twist k where
  toFun X := X u - X v
  map_add' X Y := by simp; abel
  map_smul' a X := by simp [smul_sub]

/-- The explicit grounded pin-constraint operator. -/
noncomputable def groundedPinOperator (root : W) (src dst : E → W)
    (p : E → Vec3 k) :
    (OffRoot root → Twist k) →ₗ[k] (E → Vec3 k) :=
  LinearMap.pi fun e ↦
    (Twist.evalLinear (p e)).comp
      ((assignmentDifferenceLinear (src e) (dst e)).comp
        (extendGroundedLinear root))

@[simp] theorem groundedPinOperator_apply (root : W) (src dst : E → W)
    (p : E → Vec3 k) (X : OffRoot root → Twist k) (e : E) :
    groundedPinOperator root src dst p X e =
      Twist.eval
        (extendGrounded root X (src e) - extendGrounded root X (dst e)) (p e) := by
  simp [groundedPinOperator, assignmentDifferenceLinear, extendGroundedLinear]

theorem mem_ker_groundedPinOperator_iff (root : W) (src dst : E → W)
    (p : E → Vec3 k) (X : OffRoot root → Twist k) :
    X ∈ LinearMap.ker (groundedPinOperator root src dst p) ↔
      IsTwistMotion src dst p (extendGrounded root X) := by
  constructor
  · intro hX e
    have he := congrFun (LinearMap.mem_ker.mp hX) e
    simp only [groundedPinOperator_apply, Pi.zero_apply] at he
    rw [Twist.eval_sub] at he
    exact sub_eq_zero.mp he
  · intro hX
    rw [LinearMap.mem_ker]
    funext e
    simp only [groundedPinOperator_apply, Pi.zero_apply]
    rw [Twist.eval_sub]
    exact sub_eq_zero.mpr (hX e)

/-- Grounding converts diagonal-kernel rigidity into ordinary injectivity. -/
theorem groundedPinOperator_injective_iff_twistRigidAt
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Function.Injective (groundedPinOperator root src dst p) ↔
      TwistRigidAt src dst p := by
  constructor
  · intro hinj X hX
    let Y : Twist k := X root
    let Z : OffRoot root → Twist k := fun w ↦ X w.1 - Y
    have hExtend : extendGrounded root Z = fun w ↦ X w - Y := by
      funext w
      by_cases hw : w = root
      · subst w
        simp [Z, Y]
      · simp [extendGrounded, hw, Z]
    have hZmotion : IsTwistMotion src dst p (extendGrounded root Z) := by
      intro e
      rw [hExtend]
      simp only [Twist.eval_sub]
      exact congrArg (fun z ↦ z - Twist.eval Y (p e)) (hX e)
    have hZker : Z ∈ LinearMap.ker (groundedPinOperator root src dst p) :=
      (mem_ker_groundedPinOperator_iff root src dst p Z).mpr hZmotion
    have hZzero : Z = 0 := by
      apply hinj
      rw [LinearMap.mem_ker] at hZker
      simpa using hZker
    refine ⟨Y, ?_⟩
    funext w
    have hAt := congrFun hExtend w
    rw [hZzero] at hAt
    simp only [Pi.zero_apply, extendGrounded, dite_eq_ite, ite_self] at hAt
    exact sub_eq_zero.mp hAt.symm
  · intro hrig
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro Z hZ
      have hMotion :=
        (mem_ker_groundedPinOperator_iff root src dst p Z).mp hZ
      obtain ⟨Y, hdiag⟩ := hrig (extendGrounded root Z) hMotion
      have hY : Y = 0 := by
        have hroot := congrFun hdiag root
        simpa using hroot.symm
      have hZzero : Z = 0 := by
        funext w
        have hw := congrFun hdiag w.1
        rw [hY] at hw
        simpa using hw
      simp [hZzero]
    · exact bot_le

end RB31E2E


end
end BundlePart15

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_016/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_016.json"

section BundlePart16
/- Source: Papers/RigidityZheng_Algebra_GroundedTwistPolynomial.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/GroundedTwistPolynomial.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# The provenance polynomial matrix of the grounded twist operator

For a fixed grounded body, this file writes the actual pin operator as an
integer-coefficient polynomial matrix.  Its variables retain the pin
occurrence and spatial coordinate as provenance labels.  The comparison with
`groundedPinOperator` is an equality after explicit coordinate linear
equivalences, not merely an equality of ranks.
-/

namespace RB31E2E

namespace GroundedTwistPolynomial

noncomputable section

open MvPolynomial

/-- One variable for every coordinate of every pin occurrence. -/
abbrev PinVariable (E : Type*) := E × Fin 3

/-- Rows are pin occurrences together with output-velocity coordinates. -/
abbrev GroundedRow (E : Type*) := E × Fin 3

/-- `false` labels angular and `true` translational twist coordinates. -/
abbrev TwistCoordinate := Bool × Fin 3

/-- Columns are provenance-labelled coordinates of bodies other than root. -/
abbrev GroundedColumn {W : Type*} (root : W) := OffRoot root × TwistCoordinate

/-- Explicit coordinates on one six-dimensional twist. -/
def twistCoordinates {k : Type*} [Field k] :
    Twist k ≃ₗ[k] (TwistCoordinate → k) where
  toFun X
    | ⟨false, i⟩ => X.1 i
    | ⟨true, i⟩ => X.2 i
  invFun x :=
    ⟨fun i ↦ x ⟨false, i⟩, fun i ↦ x ⟨true, i⟩⟩
  left_inv X := by
    apply Prod.ext <;> funext i <;> rfl
  right_inv x := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl
  map_add' X Y := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl
  map_smul' a X := by
    funext c
    rcases c with ⟨b, i⟩
    cases b <;> rfl

@[simp] theorem twistCoordinates_angular {k : Type*} [Field k]
    (X : Twist k) (i : Fin 3) :
    twistCoordinates X ⟨false, i⟩ = X.1 i := rfl

@[simp] theorem twistCoordinates_translational {k : Type*} [Field k]
    (X : Twist k) (i : Fin 3) :
    twistCoordinates X ⟨true, i⟩ = X.2 i := rfl

/-- Coordinates on all off-root twists, with body labels retained. -/
def groundedTwistCoordinates {k W : Type*} [Field k] (root : W) :
    (OffRoot root → Twist k) ≃ₗ[k] (GroundedColumn root → k) :=
  (LinearEquiv.piCongrRight
      (fun _ : OffRoot root ↦ twistCoordinates (k := k))).trans
    (LinearEquiv.curry k k (OffRoot root) TwistCoordinate).symm

@[simp] theorem groundedTwistCoordinates_apply
    {k W : Type*} [Field k] (root : W)
    (X : OffRoot root → Twist k) (c : GroundedColumn root) :
    groundedTwistCoordinates root X c = twistCoordinates (X c.1) c.2 :=
  rfl

/-- Coordinates on all pin-velocity outputs. -/
def pinVelocityCoordinates {k E : Type*} [Field k] :
    (E → Vec3 k) ≃ₗ[k] (GroundedRow E → k) :=
  (LinearEquiv.curry k k E (Fin 3)).symm

@[simp] theorem pinVelocityCoordinates_apply
    {k E : Type*} [Field k] (Y : E → Vec3 k) (r : GroundedRow E) :
    pinVelocityCoordinates Y r = Y r.1 r.2 := rfl

/-- Recover pins from one assignment of the provenance variables. -/
def pinsOfAssignment {k E : Type*} (z : PinVariable E → k) : E → Vec3 k :=
  fun e i ↦ z ⟨e, i⟩

/-- Encode concrete pins as an assignment of all provenance variables. -/
def assignmentOfPins {k E : Type*} (p : E → Vec3 k) : PinVariable E → k :=
  fun ei ↦ p ei.1 ei.2

@[simp] theorem pinsOfAssignment_assignmentOfPins
    {k E : Type*} (p : E → Vec3 k) :
    pinsOfAssignment (assignmentOfPins p) = p := by
  rfl

@[simp] theorem assignmentOfPins_pinsOfAssignment
    {k E : Type*} (z : PinVariable E → k) :
    assignmentOfPins (pinsOfAssignment z) = z := by
  rfl

/-- A coordinate unit vector over any coefficient ring. -/
def coordinateUnit {R : Type*} [CommRing R] (i : Fin 3) : Vec3 R :=
  fun j ↦ if j = i then 1 else 0

/-- The angular/translational unit twist indexed by one column coordinate. -/
def twistCoordinateUnit {R : Type*} [CommRing R]
    (c : TwistCoordinate) : Twist R :=
  match c.1 with
  | false => ⟨coordinateUnit c.2, 0⟩
  | true => ⟨0, coordinateUnit c.2⟩

/-- The off-root coordinate basis vector indexed by a matrix column. -/
def groundedCoordinateUnit {R W : Type*} [CommRing R] [DecidableEq W]
    {root : W} (c : GroundedColumn root) : OffRoot root → Twist R :=
  fun w ↦ if w = c.1 then twistCoordinateUnit c.2 else 0

/-- Extend an off-root assignment by zero, over a general commutative ring. -/
def extendOffRoot {R W : Type*} [CommRing R] [DecidableEq W]
    (root : W) (X : OffRoot root → Twist R) : W → Twist R :=
  fun w ↦ if h : w = root then 0 else X ⟨w, h⟩

theorem extendOffRoot_eq_extendGrounded
    {k W : Type*} [Field k] [DecidableEq W]
    (root : W) (X : OffRoot root → Twist k) :
    extendOffRoot root X = extendGrounded root X := by
  rfl

/-- The universal provenance-labelled pin. -/
def universalPin {E : Type*} (e : E) :
    Vec3 (MvPolynomial (PinVariable E) ℤ) :=
  fun i ↦ X ⟨e, i⟩

/-- The same explicit coordinate matrix over any commutative coefficient
ring, for a concrete pin assignment. -/
def groundedPinMatrix {R W E : Type*} [CommRing R] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 R) :
    Matrix (GroundedRow E) (GroundedColumn root) R :=
  fun r c ↦
    Twist.eval
      (extendOffRoot root (groundedCoordinateUnit c) (src r.1) -
        extendOffRoot root (groundedCoordinateUnit c) (dst r.1))
      (p r.1) r.2

/-- The integer-coefficient, provenance-labelled polynomial matrix of the
grounded pin operator. -/
def groundedPinPolynomialMatrix {W E : Type*} [DecidableEq W]
    (root : W) (src dst : E → W) :
    Matrix (GroundedRow E) (GroundedColumn root)
      (MvPolynomial (PinVariable E) ℤ) :=
  groundedPinMatrix root src dst universalPin

private theorem totalDegree_extend_coordinateUnit_fst
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (w : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
        (groundedCoordinateUnit
          (R := MvPolynomial σ ℤ) c) w).1 i) = 0 := by
  rcases c with ⟨body, ⟨b, j⟩⟩
  cases b <;>
    simp [extendOffRoot, groundedCoordinateUnit, twistCoordinateUnit] <;>
    split_ifs
  all_goals
    by_cases hij : i = j <;>
      simp [coordinateUnit, hij]

private theorem totalDegree_extend_coordinateUnit_snd
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (w : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
        (groundedCoordinateUnit
          (R := MvPolynomial σ ℤ) c) w).2 i) = 0 := by
  rcases c with ⟨body, ⟨b, j⟩⟩
  cases b <;>
    simp [extendOffRoot, groundedCoordinateUnit, twistCoordinateUnit] <;>
    split_ifs
  all_goals
    by_cases hij : i = j <;>
      simp [coordinateUnit, hij]

private theorem totalDegree_groundedDifference_fst_le_zero
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (u v : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) u -
        extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) v).1 i) ≤ 0 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  rw [totalDegree_extend_coordinateUnit_fst,
    totalDegree_extend_coordinateUnit_fst]
  simp

private theorem totalDegree_groundedDifference_snd_le_zero
    {σ W : Type*} [DecidableEq W] (root : W)
    (c : GroundedColumn root) (u v : W) (i : Fin 3) :
    MvPolynomial.totalDegree
      ((extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) u -
        extendOffRoot root
          (groundedCoordinateUnit (R := MvPolynomial σ ℤ) c) v).2 i) ≤ 0 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  rw [totalDegree_extend_coordinateUnit_snd,
    totalDegree_extend_coordinateUnit_snd]
  simp

private theorem totalDegree_constant_mul_X_le_one
    {σ : Type*} (P : MvPolynomial σ ℤ) (v : σ)
    (hP : P.totalDegree ≤ 0) :
    (P * X v).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_X]
  omega

private theorem totalDegree_cross_universalPin_le_one
    {E : Type*} (omega : Vec3 (MvPolynomial (PinVariable E) ℤ))
    (e : E) (j : Fin 3)
    (homega : ∀ i, (omega i).totalDegree ≤ 0) :
    (Vec3.cross omega (universalPin e) j).totalDegree ≤ 1 := by
  fin_cases j <;>
    simp only [Vec3.cross, universalPin] <;>
    apply (MvPolynomial.totalDegree_sub _ _).trans <;>
    apply Nat.max_le.mpr <;>
    constructor <;>
    apply totalDegree_constant_mul_X_le_one <;>
    exact homega _

/-- Every entry of the provenance matrix has total degree at most one.  Thus
translation columns are constant and angular columns are linear in the pin
coordinates; no higher-degree coefficient is hidden in the construction. -/
theorem groundedPinPolynomialMatrix_totalDegree_le_one
    {W E : Type*} [DecidableEq W]
    (root : W) (src dst : E → W)
    (r : GroundedRow E) (c : GroundedColumn root) :
    MvPolynomial.totalDegree
      (groundedPinPolynomialMatrix root src dst r c) ≤ 1 := by
  rcases r with ⟨e, j⟩
  let D : Twist (MvPolynomial (PinVariable E) ℤ) :=
    extendOffRoot root (groundedCoordinateUnit c) (src e) -
      extendOffRoot root (groundedCoordinateUnit c) (dst e)
  have hω (i : Fin 3) : (D.1 i).totalDegree ≤ 0 := by
    exact totalDegree_groundedDifference_fst_le_zero
      root c (src e) (dst e) i
  have hv (i : Fin 3) : (D.2 i).totalDegree ≤ 0 := by
    exact totalDegree_groundedDifference_snd_le_zero
      root c (src e) (dst e) i
  change MvPolynomial.totalDegree
    (D.2 j + Vec3.cross D.1 (universalPin e) j) ≤ 1
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply Nat.max_le.mpr
  exact ⟨(hv j).trans (by omega),
    totalDegree_cross_universalPin_le_one D.1 e j hω⟩

/-! ## Equality with the actual grounded operator -/

/-- The coordinate basis on the off-root twist space. -/
def groundedTwistBasis {k W : Type*} [Field k] [Fintype W]
    [DecidableEq W] (root : W) :
    Module.Basis (GroundedColumn root) k (OffRoot root → Twist k) :=
  Module.Basis.ofEquivFun (groundedTwistCoordinates root)

/-- The coordinate basis on the pin-velocity output space. -/
def pinVelocityBasis {k E : Type*} [Field k] [Fintype E] :
    Module.Basis (GroundedRow E) k (E → Vec3 k) :=
  Module.Basis.ofEquivFun pinVelocityCoordinates

theorem groundedTwistBasis_apply_eq_coordinateUnit
    {k W : Type*} [Field k] [Fintype W] [DecidableEq W]
    (root : W) (c : GroundedColumn root) :
    groundedTwistBasis (k := k) root c = groundedCoordinateUnit c := by
  rw [groundedTwistBasis, Module.Basis.coe_ofEquivFun]
  apply (groundedTwistCoordinates (k := k) root).injective
  funext d
  rw [LinearEquiv.apply_symm_apply]
  rcases c with ⟨w, ⟨bc, i⟩⟩
  rcases d with ⟨v, ⟨bd, j⟩⟩
  cases bc <;> cases bd <;>
    by_cases hwv : v = w <;>
    by_cases hij : j = i <;>
    simp [groundedCoordinateUnit, twistCoordinateUnit, coordinateUnit,
      Pi.single_apply, Prod.ext_iff, hwv, hij]

/-- The usual coordinate matrix of the actual `groundedPinOperator`. -/
def groundedPinCoordinateMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Matrix (GroundedRow E) (GroundedColumn root) k :=
  LinearMap.toMatrix (groundedTwistBasis root) pinVelocityBasis
    (groundedPinOperator root src dst p)

/-- Entrywise equality between the explicit matrix and the coordinate matrix
of the genuine grounded operator. -/
theorem groundedPinMatrix_eq_coordinateMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    groundedPinMatrix root src dst p =
      groundedPinCoordinateMatrix root src dst p := by
  ext r c
  rw [groundedPinCoordinateMatrix, LinearMap.toMatrix_apply,
    groundedTwistBasis_apply_eq_coordinateUnit]
  change groundedPinMatrix root src dst p r c =
    pinVelocityCoordinates
      (groundedPinOperator root src dst p (groundedCoordinateUnit c)) r
  simp only [pinVelocityCoordinates_apply, groundedPinOperator_apply]
  rfl

/-- Matrix multiplication is literally the grounded operator after the two
displayed coordinate equivalences. -/
theorem groundedPinMatrix_mulVec_coordinates
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k)
    (Y : OffRoot root → Twist k) :
    (groundedPinMatrix root src dst p).mulVec
        (groundedTwistCoordinates root Y) =
      pinVelocityCoordinates (groundedPinOperator root src dst p Y) := by
  rw [groundedPinMatrix_eq_coordinateMatrix]
  have hground (X : OffRoot root → Twist k) :
      ((groundedTwistBasis root).repr X : GroundedColumn root → k) =
        groundedTwistCoordinates root X := by
    funext c
    exact Module.Basis.ofEquivFun_repr_apply _ _ _
  have hpin (X : E → Vec3 k) :
      (pinVelocityBasis.repr X : GroundedRow E → k) = pinVelocityCoordinates X := by
    funext r
    exact Module.Basis.ofEquivFun_repr_apply _ _ _
  simpa only [groundedPinCoordinateMatrix, hground, hpin]
    using (groundedPinOperator root src dst p).toMatrix_mulVec_repr
      (groundedTwistBasis root) pinVelocityBasis Y

/-- Injectivity of the explicit coordinate matrix is equivalent to
injectivity of the genuine grounded operator. -/
theorem groundedPinMatrix_mulVec_injective_iff
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (p : E → Vec3 k) :
    Function.Injective (groundedPinMatrix root src dst p).mulVec ↔
      Function.Injective (groundedPinOperator root src dst p) := by
  constructor
  · intro hMatrix Y Z hYZ
    apply (groundedTwistCoordinates (k := k) root).injective
    apply hMatrix
    rw [groundedPinMatrix_mulVec_coordinates,
      groundedPinMatrix_mulVec_coordinates, hYZ]
  · intro hOperator u v huv
    obtain ⟨Y, rfl⟩ := (groundedTwistCoordinates (k := k) root).surjective u
    obtain ⟨Z, rfl⟩ := (groundedTwistCoordinates (k := k) root).surjective v
    apply congrArg (groundedTwistCoordinates (k := k) root)
    apply hOperator
    apply (pinVelocityCoordinates (k := k) (E := E)).injective
    simpa only [groundedPinMatrix_mulVec_coordinates] using huv

/-! ## Polynomial specialization -/

/-- Apply a coefficient homomorphism coordinatewise to a three-vector. -/
def mapVec3 {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Vec3 R) : Vec3 S :=
  fun i ↦ f (v i)

/-- Apply a coefficient homomorphism coordinatewise to a twist. -/
def mapTwist {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Y : Twist R) : Twist S :=
  ⟨mapVec3 f Y.1, mapVec3 f Y.2⟩

@[simp] theorem mapTwist_zero
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    mapTwist f (0 : Twist R) = 0 := by
  apply Prod.ext <;> funext i <;> simp [mapTwist, mapVec3]

@[simp] theorem mapTwist_sub
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Y Z : Twist R) :
    mapTwist f (Y - Z) = mapTwist f Y - mapTwist f Z := by
  apply Prod.ext <;> funext i <;> simp [mapTwist, mapVec3]

/-- Rigid-body velocity evaluation commutes with coefficient maps. -/
theorem mapVec3_eval
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Y : Twist R) (p : Vec3 R) :
    mapVec3 f (Twist.eval Y p) =
      Twist.eval (mapTwist f Y) (mapVec3 f p) := by
  funext i
  fin_cases i <;>
    simp [mapVec3, mapTwist, Twist.eval, Vec3.cross]

@[simp] theorem mapTwist_twistCoordinateUnit
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (c : TwistCoordinate) :
    mapTwist f (twistCoordinateUnit c : Twist R) =
      (twistCoordinateUnit c : Twist S) := by
  rcases c with ⟨b, i⟩
  cases b <;>
    apply Prod.ext <;>
    funext j <;>
    simp [mapTwist, mapVec3, twistCoordinateUnit, coordinateUnit]

theorem mapTwist_groundedCoordinateUnit
    {R S W : Type*} [CommRing R] [CommRing S] [DecidableEq W]
    (f : R →+* S) {root : W} (c : GroundedColumn root) :
    (fun w ↦ mapTwist f (groundedCoordinateUnit (R := R) c w)) =
      groundedCoordinateUnit (R := S) c := by
  funext w
  by_cases hw : w = c.1 <;>
    simp [groundedCoordinateUnit, hw]

theorem mapTwist_extendOffRoot
    {R S W : Type*} [CommRing R] [CommRing S] [DecidableEq W]
    (f : R →+* S) (root : W) (Y : OffRoot root → Twist R) :
    (fun w ↦ mapTwist f (extendOffRoot root Y w)) =
      extendOffRoot root (fun u ↦ mapTwist f (Y u)) := by
  funext w
  by_cases hw : w = root <;>
    simp [extendOffRoot, hw]

theorem mapVec3_universalPin
    {k E : Type*} [Field k] (z : PinVariable E → k) (e : E) :
    mapVec3 (MvPolynomial.eval₂Hom (Int.castRingHom k) z) (universalPin e) =
      pinsOfAssignment z e := by
  funext i
  simp [mapVec3, universalPin, pinsOfAssignment]

/-- Specializing the provenance matrix gives the explicit matrix at the
corresponding pin placement, entry for entry.  This holds over every field,
and hence in particular over every characteristic-zero field, `ℝ`, and `ℂ`. -/
theorem specialize_groundedPinPolynomialMatrix
    {k W E : Type*} [Field k] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst) =
      groundedPinMatrix root src dst (pinsOfAssignment z) := by
  ext r c
  rcases r with ⟨e, j⟩
  change
    MvPolynomial.eval₂ (Int.castRingHom k) z
      (groundedPinMatrix root src dst universalPin (e, j) c) =
    groundedPinMatrix root src dst (pinsOfAssignment z) (e, j) c
  change
    (mapVec3 (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
      (Twist.eval
        (extendOffRoot root (groundedCoordinateUnit c) (src e) -
          extendOffRoot root (groundedCoordinateUnit c) (dst e))
        (universalPin e))) j = _
  rw [mapVec3_eval, mapTwist_sub]
  rw [show mapTwist (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
        (extendOffRoot root (groundedCoordinateUnit c) (src e)) =
      extendOffRoot root (groundedCoordinateUnit c) (src e) by
    have h := congrFun
      (mapTwist_extendOffRoot
        (MvPolynomial.eval₂Hom (Int.castRingHom k) z) root
        (groundedCoordinateUnit c)) (src e)
    simpa [mapTwist_groundedCoordinateUnit] using h]
  rw [show mapTwist (MvPolynomial.eval₂Hom (Int.castRingHom k) z)
        (extendOffRoot root (groundedCoordinateUnit c) (dst e)) =
      extendOffRoot root (groundedCoordinateUnit c) (dst e) by
    have h := congrFun
      (mapTwist_extendOffRoot
        (MvPolynomial.eval₂Hom (Int.castRingHom k) z) root
        (groundedCoordinateUnit c)) (dst e)
    simpa [mapTwist_groundedCoordinateUnit] using h]
  rw [mapVec3_universalPin]
  rfl

/-- Direct matrix/operator identity: after specialization, the provenance
matrix is exactly `LinearMap.toMatrix` of `groundedPinOperator` in the
displayed bases. -/
theorem specialize_groundedPinPolynomialMatrix_eq_operatorMatrix
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst) =
      groundedPinCoordinateMatrix root src dst (pinsOfAssignment z) := by
  rw [specialize_groundedPinPolynomialMatrix,
    groundedPinMatrix_eq_coordinateMatrix]

/-- The fully specialized polynomial matrix acts as the actual grounded pin
operator under the explicit coordinate equivalences. -/
theorem specializedPolynomialMatrix_mulVec_coordinates
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k)
    (Y : OffRoot root → Twist k) :
    (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst)).mulVec
        (groundedTwistCoordinates root Y) =
      pinVelocityCoordinates
        (groundedPinOperator root src dst (pinsOfAssignment z) Y) := by
  rw [specialize_groundedPinPolynomialMatrix]
  exact groundedPinMatrix_mulVec_coordinates root src dst
    (pinsOfAssignment z) Y

/-- The conjugacy as an equality of linear maps, rather than just a pointwise
statement about vectors. -/
theorem specializedPolynomialMatrix_operator_conjugacy
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
        (groundedPinPolynomialMatrix root src dst)).mulVecLin.comp
        (groundedTwistCoordinates root).toLinearMap =
      (pinVelocityCoordinates (k := k) (E := E)).toLinearMap.comp
        (groundedPinOperator root src dst (pinsOfAssignment z)) := by
  apply LinearMap.ext
  intro Y
  exact specializedPolynomialMatrix_mulVec_coordinates
    root src dst z Y

/-- Specialization is injective exactly when the genuine grounded operator at
the specialized pins is injective. -/
theorem specializedPolynomialMatrix_injective_iff_grounded
    {k W E : Type*} [Field k] [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W) (z : PinVariable E → k) :
    Function.Injective
        (ComplexRealSpecialization.specializeMatrix (Int.castRingHom k) z
          (groundedPinPolynomialMatrix root src dst)).mulVec ↔
      Function.Injective
        (groundedPinOperator root src dst (pinsOfAssignment z)) := by
  rw [specialize_groundedPinPolynomialMatrix]
  exact groundedPinMatrix_mulVec_injective_iff root src dst
    (pinsOfAssignment z)

/-! ## The complex-to-real rigidity transfer -/

/-- A complex pin placement with injective grounded operator gives a real pin
placement with injective grounded operator.  The fixed `root` is the explicit
witness that the body type is nonempty. -/
theorem exists_real_grounded_injective_of_exists_complex
    {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W)
    (hComplex : ∃ p : E → Vec3 ℂ,
      Function.Injective (groundedPinOperator root src dst p)) :
    ∃ p : E → Vec3 ℝ,
      Function.Injective (groundedPinOperator root src dst p) := by
  obtain ⟨pComplex, hpComplex⟩ := hComplex
  have hMatrixComplex : ∃ z : PinVariable E → ℂ,
      Function.Injective
        (ComplexRealSpecialization.specializeMatrix (Int.castRingHom ℂ) z
          (groundedPinPolynomialMatrix root src dst)).mulVec := by
    refine ⟨assignmentOfPins pComplex, ?_⟩
    apply (specializedPolynomialMatrix_injective_iff_grounded
      root src dst (assignmentOfPins pComplex)).mpr
    simpa using hpComplex
  obtain ⟨zReal, hzReal⟩ :=
    ComplexRealSpecialization.exists_real_specialization_injective_of_complex
      (groundedPinPolynomialMatrix root src dst) hMatrixComplex
  refine ⟨pinsOfAssignment zReal, ?_⟩
  exact (specializedPolynomialMatrix_injective_iff_grounded
    root src dst zReal).mp hzReal

/-- Genuine end-to-end transfer: existence of a complex rigid body-twist pin
placement implies existence of a real rigid body-twist pin placement. -/
theorem exists_real_twistRigidAt_of_exists_complex
    {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
    (root : W) (src dst : E → W)
    (hComplex : ∃ p : E → Vec3 ℂ, TwistRigidAt src dst p) :
    ∃ p : E → Vec3 ℝ, TwistRigidAt src dst p := by
  have hGroundedComplex : ∃ p : E → Vec3 ℂ,
      Function.Injective (groundedPinOperator root src dst p) := by
    obtain ⟨p, hp⟩ := hComplex
    exact ⟨p,
      (groundedPinOperator_injective_iff_twistRigidAt root src dst p).mpr hp⟩
  obtain ⟨pReal, hpReal⟩ :=
    exists_real_grounded_injective_of_exists_complex
      root src dst hGroundedComplex
  exact ⟨pReal,
    (groundedPinOperator_injective_iff_twistRigidAt
      root src dst pReal).mp hpReal⟩

end

end GroundedTwistPolynomial

end RB31E2E


end
end BundlePart16

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_017/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_017.json"

section BundlePart17
/- Source: Papers/RigidityGenericPinMatrix.lean -/




@[expose] public section

/-!
# The independent pin coefficient matrix and its real specializations

The field consists of rational functions in the original three coordinates
of every pin occurrence. Matrix specialization is proved entry by entry;
its generic rank is the attained maximum rank over real pin placements.
-/

namespace Papers.Rigidity.GenericPinIdeal

noncomputable section

open MvPolynomial
open RB31E2E
open RB31E2E.GroundedTwistPolynomial

abbrev PinField (E : Type*) := FractionRing (MvPolynomial (E × Fin 3) ℚ)

/-- One algebraically independent coordinate per pin occurrence and axis. -/
def genericPins {E : Type*} : E → RB31E2E.Vec3 (PinField E) :=
  fun e i => algebraMap (MvPolynomial (E × Fin 3) ℚ) (PinField E) (X (e, i))

/-- The actual coordinate matrix of the grounded compatibility operator. -/
def genericMotionMatrix {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) :
    Matrix (GroundedRow E) (GroundedColumn root) (PinField E) :=
  groundedPinMatrix root src dst genericPins

/-- The literal grounded matrix commutes with every ring homomorphism. -/
theorem map_groundedPinMatrix
    {R S V E : Type*} [CommRing R] [CommRing S] [DecidableEq V]
    (f : R →+* S) (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 R) :
    (groundedPinMatrix root src dst p).map f =
      groundedPinMatrix root src dst (fun e => mapVec3 f (p e)) := by
  ext a c
  rcases a with ⟨e, j⟩
  have hground (v : V) :
      mapTwist f (extendOffRoot root (groundedCoordinateUnit (R := R) c) v) =
        extendOffRoot root (groundedCoordinateUnit (R := S) c) v := by
    have h := congrFun (mapTwist_extendOffRoot f root (groundedCoordinateUnit c)) v
    simpa [mapTwist_groundedCoordinateUnit] using h
  have h := congrFun (mapVec3_eval f
    (extendOffRoot root (groundedCoordinateUnit (R := R) c) (src e) -
      extendOffRoot root (groundedCoordinateUnit (R := R) c) (dst e)) (p e)) j
  rw [mapTwist_sub, hground, hground] at h
  exact h

/-- The rational polynomial matrix keeps the same occurrence-level pins. -/
def rationalMotionMatrix {V E : Type*} [DecidableEq V]
    (root : V) (src dst : E → V) :
    Matrix (GroundedRow E) (GroundedColumn root) (MvPolynomial (E × Fin 3) ℚ) :=
  groundedPinMatrix root src dst (fun e i => X (e, i))

theorem genericMatrix_rationalMotionMatrix
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V) :
    PolynomialRank.genericMatrix (rationalMotionMatrix root src dst) =
      genericMotionMatrix root src dst := by
  rw [PolynomialRank.genericMatrix, rationalMotionMatrix, map_groundedPinMatrix]
  rfl

theorem realMatrix_rationalMotionMatrix
    {V E : Type*} [DecidableEq V] (root : V) (src dst : E → V)
    (z : E × Fin 3 → ℝ) :
    PolynomialRank.realMatrix (rationalMotionMatrix root src dst) z =
      groundedPinMatrix root src dst (pinsOfAssignment z) := by
  rw [PolynomialRank.realMatrix, rationalMotionMatrix, map_groundedPinMatrix]
  congr 1
  funext e i
  simp [mapVec3, pinsOfAssignment]

theorem real_groundedPinMatrix_rank_le_generic
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 ℝ) :
    (groundedPinMatrix root src dst p).rank ≤ (genericMotionMatrix root src dst).rank := by
  have h := PolynomialRank.realMatrix_rank_le_generic
    (rationalMotionMatrix root src dst) (assignmentOfPins p)
  simpa only [realMatrix_rationalMotionMatrix, genericMatrix_rationalMotionMatrix,
    pinsOfAssignment_assignmentOfPins] using h

/-- A real placement attains the full rational-function rank. -/
theorem exists_real_groundedPinMatrix_rank_eq_generic
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (root : V) (src dst : E → V) :
    ∃ p : E → RB31E2E.Vec3 ℝ,
      (groundedPinMatrix root src dst p).rank = (genericMotionMatrix root src dst).rank := by
  obtain ⟨z, hz⟩ := PolynomialRank.exists_realMatrix_rank_eq_generic
    (rationalMotionMatrix root src dst)
  exact ⟨pinsOfAssignment z, by
    simpa only [realMatrix_rationalMotionMatrix, genericMatrix_rationalMotionMatrix] using hz⟩

/-- The coordinate matrix has exactly the rank of the actual grounded
linear operator over any field. -/
theorem groundedPinMatrix_rank_eq_operator_rank
    {k V E : Type*} [Field k] [Fintype V] [Fintype E] [DecidableEq V]
    (root : V) (src dst : E → V) (p : E → RB31E2E.Vec3 k) :
    (groundedPinMatrix root src dst p).rank =
      Module.finrank k (groundedPinOperator root src dst p).range := by
  rw [groundedPinMatrix_eq_coordinateMatrix, groundedPinCoordinateMatrix,
    Matrix.rank_eq_finrank_range_toLin _ pinVelocityBasis (groundedTwistBasis root),
    Matrix.toLin_toMatrix]

theorem genericMotionMatrix_rank_eq_operator_rank
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (root : V) (src dst : E → V) :
    (genericMotionMatrix root src dst).rank =
      Module.finrank (PinField E) (groundedPinOperator root src dst genericPins).range :=
  groundedPinMatrix_rank_eq_operator_rank root src dst genericPins

/-- Rank-nullity has exactly six coordinates per non-root body. -/
theorem genericMotion_rank_add_nullity
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (root : V) (src dst : E → V) :
    (genericMotionMatrix root src dst).rank +
      Module.finrank (PinField E) (groundedPinOperator root src dst genericPins).ker =
      6 * (Fintype.card V - 1) := by
  rw [genericMotionMatrix_rank_eq_operator_rank,
    LinearMap.finrank_range_add_finrank_ker]
  have hcard : Fintype.card (OffRoot root) = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun v : V => v = root)]
    simp
  simp [Module.finrank_pi_fintype, hcard, RB31E2E.Twist.finrank_twist, Nat.mul_comm]

end

end Papers.Rigidity.GenericPinIdeal

end
end BundlePart17

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_018/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_018.json"

section BundlePart18
/- Source: Papers/RigidityZheng_NullCellule_Definitions.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/Definitions.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Distinct Split--Klein null-difference configurations

This is the point-set semantics of the null cellule used in the
algebraic-geometric layer.  It is intentionally independent of any
dimension claim.
-/

namespace RB31E2E

variable {k V : Type*} [CommRing k] [DecidableEq V]

/-- The Split--Klein null-difference equation attached to an unordered edge. -/
def IsNullOnEdge (X : V → Twist k) (e : SimpleEdge V) : Prop :=
  Sym2.lift ⟨fun u v ↦ Twist.splitKlein (X u - X v) = 0, by
    intro u v
    apply propext
    change Twist.splitKlein (X u - X v) = 0 ↔
      Twist.splitKlein (X v - X u) = 0
    rw [Twist.splitKlein_sub_comm]⟩ e.1

/-- All equations attached to the selected simple edge set hold. -/
def IsNullDifferenceConfiguration (F : SimpleEdgeSet V) (X : V → Twist k) : Prop :=
  ∀ e ∈ F, IsNullOnEdge X e

/-- The open condition that all labelled twists are pairwise distinct. -/
def IsDistinctConfiguration (X : V → Twist k) : Prop :=
  Function.Injective X

/-- Membership in the distinct null-difference cellule. -/
def InNullCellule (F : SimpleEdgeSet V) (X : V → Twist k) : Prop :=
  IsDistinctConfiguration X ∧ IsNullDifferenceConfiguration F X

omit [DecidableEq V] in
@[simp] theorem isNullOnEdge_mk (X : V → Twist k) (u v : V) (huv : u ≠ v) :
    IsNullOnEdge X ⟨s(u, v), fun h ↦ huv (Sym2.mk_isDiag_iff.mp h)⟩ ↔
      Twist.splitKlein (X u - X v) = 0 := by
  rfl

omit [DecidableEq V] in
/-- Common translation of every twist leaves all edge differences unchanged. -/
theorem isNullDifferenceConfiguration_add_common
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : IsNullDifferenceConfiguration F X) (A : Twist k) :
    IsNullDifferenceConfiguration F (fun v ↦ X v + A) := by
  rintro ⟨z, hz⟩ he
  have hNull := hX ⟨z, hz⟩ he
  unfold IsNullOnEdge at hNull ⊢
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.lift_mk] at hNull ⊢
      rw [show (X u + A) - (X v + A) = X u - X v by abel]
      exact hNull

omit [DecidableEq V] in
/-- Common scaling preserves the null equations, including at scale zero. -/
theorem isNullDifferenceConfiguration_smul
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : IsNullDifferenceConfiguration F X) (a : k) :
    IsNullDifferenceConfiguration F (fun v ↦ a • X v) := by
  rintro ⟨z, hz⟩ he
  have hNull := hX ⟨z, hz⟩ he
  unfold IsNullOnEdge at hNull ⊢
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.lift_mk] at hNull ⊢
      rw [← smul_sub, Twist.splitKlein_smul, hNull, mul_zero]

omit [DecidableEq V] in
theorem isDistinctConfiguration_add_common
    {X : V → Twist k} (hX : IsDistinctConfiguration X) (A : Twist k) :
    IsDistinctConfiguration (fun v ↦ X v + A) := by
  intro u v huv
  apply hX
  exact add_right_cancel huv

omit [DecidableEq V] in
theorem isDistinctConfiguration_smul
    {K : Type*} [Field K] {X : V → Twist K}
    (hX : IsDistinctConfiguration X) {a : K} (ha : a ≠ 0) :
    IsDistinctConfiguration (fun v ↦ a • X v) := by
  intro u v huv
  apply hX
  have h := congrArg (fun Z : Twist K ↦ a⁻¹ • Z) huv
  simpa [smul_smul, ha] using h

omit [DecidableEq V] in
theorem inNullCellule_add_common
    {F : SimpleEdgeSet V} {X : V → Twist k}
    (hX : InNullCellule F X) (A : Twist k) :
    InNullCellule F (fun v ↦ X v + A) :=
  ⟨isDistinctConfiguration_add_common hX.1 A,
    isNullDifferenceConfiguration_add_common hX.2 A⟩

omit [DecidableEq V] in
theorem inNullCellule_smul
    {K : Type*} [Field K] {F : SimpleEdgeSet V} {X : V → Twist K}
    (hX : InNullCellule F X) {a : K} (ha : a ≠ 0) :
    InNullCellule F (fun v ↦ a • X v) :=
  ⟨isDistinctConfiguration_smul hX.1 ha,
    isNullDifferenceConfiguration_smul hX.2 a⟩

end RB31E2E


end
end BundlePart18

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_019/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_019.json"

section BundlePart19
/- Source: Papers/RigidityZheng_NullCellule_PolynomialModel.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/PolynomialModel.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Polynomial model of Split--Klein null cellules

The six coordinates at every vertex are retained as provenance-labelled
variables.  Evaluating the universal twist at a concrete twist assignment is
definitionally the original assignment, and each unordered edge polynomial
evaluates to the corresponding Split--Klein null-difference equation.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- Six provenance-labelled coordinates at each vertex.  `false` denotes an
angular coordinate and `true` a translational coordinate. -/
abbrev TwistVariable (V : Type*) := V × (Bool × Fin 3)

/-- The universal angular coordinate at vertex `v`. -/
def angularCoordinate {k V : Type*} [CommRing k] (v : V) (i : Fin 3) :
    MvPolynomial (TwistVariable V) k :=
  X ⟨v, false, i⟩

/-- The universal translational coordinate at vertex `v`. -/
def translationalCoordinate {k V : Type*} [CommRing k] (v : V) (i : Fin 3) :
    MvPolynomial (TwistVariable V) k :=
  X ⟨v, true, i⟩

/-- The universal six-coordinate twist attached to a vertex. -/
def universalTwist {k V : Type*} [CommRing k] (v : V) :
    Twist (MvPolynomial (TwistVariable V) k) :=
  ⟨angularCoordinate v, translationalCoordinate v⟩

/-- Turn a concrete vertex-labelled twist configuration into an assignment of
all provenance-labelled polynomial variables. -/
def assignmentOfTwists {k V : Type*} [CommRing k]
    (Y : V → Twist k) : TwistVariable V → k
  | ⟨v, false, i⟩ => (Y v).1 i
  | ⟨v, true, i⟩ => (Y v).2 i

/-- Evaluate the six coordinate polynomials of a polynomial-valued twist. -/
def evalPolynomialTwist {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (T : Twist (MvPolynomial (TwistVariable V) k)) : Twist k :=
  ⟨fun i ↦ eval a (T.1 i), fun i ↦ eval a (T.2 i)⟩

@[simp]
theorem evalPolynomialTwist_universal {k V : Type*} [CommRing k]
    (Y : V → Twist k) (v : V) :
    evalPolynomialTwist (assignmentOfTwists Y) (universalTwist v) = Y v := by
  apply Prod.ext
  · funext i
    simp [evalPolynomialTwist, universalTwist, angularCoordinate,
      assignmentOfTwists]
  · funext i
    simp [evalPolynomialTwist, universalTwist, translationalCoordinate,
      assignmentOfTwists]

@[simp]
theorem evalPolynomialTwist_sub {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (S T : Twist (MvPolynomial (TwistVariable V) k)) :
    evalPolynomialTwist a (S - T) =
      evalPolynomialTwist a S - evalPolynomialTwist a T := by
  apply Prod.ext <;> funext i <;> simp [evalPolynomialTwist]

/-- Evaluation commutes with the Split--Klein quadratic form. -/
theorem eval_splitKlein {k V : Type*} [CommRing k]
    (a : TwistVariable V → k)
    (T : Twist (MvPolynomial (TwistVariable V) k)) :
    eval a (Twist.splitKlein T) =
      Twist.splitKlein (evalPolynomialTwist a T) := by
  simp [Twist.splitKlein, Vec3.dot, evalPolynomialTwist]

/-- The orientation-independent scalar null-difference value of an edge. -/
def nullDifferenceValue {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) : k :=
  Sym2.lift ⟨fun u v ↦ Twist.splitKlein (Y u - Y v), by
    intro u v
    exact Twist.splitKlein_sub_comm _ _⟩ e.1

/-- The orientation-independent Split--Klein quadratic attached to an edge. -/
def edgePolynomial {k V : Type*} [CommRing k]
    (e : SimpleEdge V) : MvPolynomial (TwistVariable V) k :=
  Sym2.lift ⟨fun u v ↦
    Twist.splitKlein (universalTwist u - universalTwist v), by
      intro u v
      exact Twist.splitKlein_sub_comm _ _⟩ e.1

/-- The coordinate dictionary: evaluating an edge polynomial is exactly the
point-set Split--Klein value of that edge. -/
theorem eval_edgePolynomial {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) =
      nullDifferenceValue Y e := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [edgePolynomial, nullDifferenceValue, Sym2.lift_mk]
      rw [eval_splitKlein, evalPolynomialTwist_sub,
        evalPolynomialTwist_universal, evalPolynomialTwist_universal]

@[simp]
theorem eval_edgePolynomial_mk {k V : Type*} [CommRing k]
    (Y : V → Twist k) (u v : V) (huv : u ≠ v) :
    eval (assignmentOfTwists Y)
        (edgePolynomial (k := k)
          ⟨s(u, v), fun h ↦ huv (Sym2.mk_isDiag_iff.mp h)⟩) =
      Twist.splitKlein (Y u - Y v) := by
  rw [eval_edgePolynomial]
  rfl

/-- The scalar edge value vanishes exactly when the existing point-set
predicate `IsNullOnEdge` holds. -/
theorem nullDifferenceValue_eq_zero_iff {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    nullDifferenceValue Y e = 0 ↔ IsNullOnEdge Y e := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v => rfl

/-- Evaluation of one edge generator vanishes exactly on its point-set edge
equation. -/
theorem eval_edgePolynomial_eq_zero_iff {k V : Type*} [CommRing k]
    (Y : V → Twist k) (e : SimpleEdge V) :
    eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) = 0 ↔
      IsNullOnEdge Y e := by
  rw [eval_edgePolynomial, nullDifferenceValue_eq_zero_iff]

/-- The ideal generated by the selected edge quadrics. -/
def edgeIdeal {k V : Type*} [CommRing k]
    (F : SimpleEdgeSet V) : Ideal (MvPolynomial (TwistVariable V) k) :=
  Ideal.span
    (edgePolynomial (k := k) '' (F : Set (SimpleEdge V)))

/-- An ideal vanishes at an assignment when it lies in the kernel of the
corresponding evaluation homomorphism. -/
def VanishesAt {k ι : Type*} [CommRing k]
    (a : ι → k) (I : Ideal (MvPolynomial ι k)) : Prop :=
  I ≤ RingHom.ker (MvPolynomial.eval a)

/-- The zero set of the generated edge ideal is exactly the existing
`IsNullDifferenceConfiguration` predicate. -/
theorem vanishesAt_edgeIdeal_iff {k V : Type*} [CommRing k] [DecidableEq V]
    (F : SimpleEdgeSet V) (Y : V → Twist k) :
    VanishesAt (assignmentOfTwists Y) (edgeIdeal (k := k) F) ↔
      IsNullDifferenceConfiguration F Y := by
  constructor
  · intro hIdeal e he
    apply (eval_edgePolynomial_eq_zero_iff Y e).mp
    have hGenerator : edgePolynomial (k := k) e ∈ edgeIdeal (k := k) F := by
      apply Ideal.subset_span
      exact ⟨e, he, rfl⟩
    simpa [VanishesAt] using hIdeal hGenerator
  · intro hNull
    rw [VanishesAt, edgeIdeal, Ideal.span_le]
    rintro P ⟨e, he, rfl⟩
    change eval (assignmentOfTwists Y) (edgePolynomial (k := k) e) = 0
    exact (eval_edgePolynomial_eq_zero_iff Y e).mpr (hNull e he)

/-! ## Standard homogeneity -/

theorem angularDifference_isHomogeneous_one
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (angularCoordinate (k := k) u i -
      angularCoordinate (k := k) v i).IsHomogeneous 1 := by
  simpa only [angularCoordinate] using
    (MvPolynomial.isHomogeneous_X k
      (⟨u, ⟨false, i⟩⟩ : TwistVariable V)).sub
      (MvPolynomial.isHomogeneous_X k
        (⟨v, ⟨false, i⟩⟩ : TwistVariable V))

theorem translationalDifference_isHomogeneous_one
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (translationalCoordinate (k := k) u i -
      translationalCoordinate (k := k) v i).IsHomogeneous 1 := by
  simpa only [translationalCoordinate] using
    (MvPolynomial.isHomogeneous_X k
      (⟨u, ⟨true, i⟩⟩ : TwistVariable V)).sub
      (MvPolynomial.isHomogeneous_X k
        (⟨v, ⟨true, i⟩⟩ : TwistVariable V))

theorem splitKleinDifferenceTerm_isHomogeneous_two
    {k V : Type*} [CommRing k] (u v : V) (i : Fin 3) :
    (((universalTwist (k := k) u - universalTwist (k := k) v).1 i) *
      ((universalTwist (k := k) u - universalTwist (k := k) v).2 i)).IsHomogeneous 2 := by
  simpa [universalTwist, angularCoordinate, translationalCoordinate] using
    (angularDifference_isHomogeneous_one (k := k) u v i).mul
      (translationalDifference_isHomogeneous_one (k := k) u v i)

/-- Every edge generator is standard-total-degree homogeneous of degree two. -/
theorem edgePolynomial_isHomogeneous_two
    {k V : Type*} [CommRing k] (e : SimpleEdge V) :
    (edgePolynomial (k := k) e).IsHomogeneous 2 := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ u v =>
      simp only [edgePolynomial, Sym2.lift_mk, Twist.splitKlein, Vec3.dot]
      simpa using MvPolynomial.IsHomogeneous.sum Finset.univ
        (fun i ↦
          ((universalTwist (k := k) u - universalTwist (k := k) v).1 i) *
            ((universalTwist (k := k) u - universalTwist (k := k) v).2 i))
        2 (fun i _ ↦
          splitKleinDifferenceTerm_isHomogeneous_two (k := k) u v i)

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart19

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_020/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_020.json"

section BundlePart20
/- Source: Papers/RigidityZheng_NullCellule_ReplacementIdentities.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/ReplacementIdentities.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Exact polynomial identities for the two replacement moves

The weighted-degeneration argument later needs more than a dimension slogan:
it needs the exact provenance of every weight-zero, weight-one, and weight-two
term.  This file records those identities over an arbitrary commutative ring.
No initial-ideal or dimension theorem is assumed here.
-/

namespace RB31E2E

namespace Twist

variable {k : Type*} [CommRing k]

/-- The cross term in the polarization of the Split--Klein quadratic form.
It is `2B(X,Y)` in the paper's characteristic-not-two convention. -/
def mixedPairing (X Y : Twist k) : k :=
  Vec3.dot X.1 Y.2 + Vec3.dot Y.1 X.2

theorem splitKlein_add_mixedPairing (X Y : Twist k) :
    splitKlein (X + Y) =
      splitKlein X + splitKlein Y + mixedPairing X Y := by
  simp [splitKlein, mixedPairing, Vec3.dot, Fin.sum_univ_succ]
  ring

theorem mixedPairing_comm (X Y : Twist k) :
    mixedPairing X Y = mixedPairing Y X := by
  simp [mixedPairing, add_comm]

/-- Exact edge-to-`K₃` identity: `b-a-c` is the mixed term. -/
theorem splitKlein_add_sub_self_sub_self (X Y : Twist k) :
    splitKlein (X + Y) - splitKlein X - splitKlein Y =
      mixedPairing X Y := by
  rw [splitKlein_add_mixedPairing]
  abel

/-- Exact external-edge expansion for vertex-to-`K₄`. -/
theorem splitKlein_translate_difference (Z D A : Twist k) :
    splitKlein ((Z + D) - A) =
      splitKlein (Z - A) + splitKlein D + mixedPairing (Z - A) D := by
  rw [show (Z + D) - A = (Z - A) + D by abel,
    splitKlein_add_mixedPairing]

/-- Common translation cancels from an internal clone edge. -/
theorem splitKlein_common_translate_difference (Z D₁ D₂ : Twist k) :
    splitKlein ((Z + D₁) - (Z + D₂)) = splitKlein (D₁ - D₂) := by
  congr 1
  abel

end Twist

namespace NullCellulePolynomial

noncomputable section

/-- Two provenance-labelled polynomial twists used as the local `y,d`
coordinates of the edge-to-`K₃` move. -/
def triangleY {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable (Fin 2)) k) :=
  universalTwist 0

def triangleD {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable (Fin 2)) k) :=
  universalTwist 1

def triangleA {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleY (k := k))

def triangleB {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleY (k := k) + triangleD (k := k))

def triangleC {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable (Fin 2)) k :=
  Twist.splitKlein (triangleD (k := k))

/-- Polynomial-level form of `b-a-c = 2B(y,d)`, retaining the `y/d`
variable provenance needed by the six local initial-fibre cases. -/
theorem triangle_polar_combination {k : Type*} [CommRing k] :
    triangleB (k := k) - triangleA (k := k) - triangleC (k := k) =
      Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) := by
  exact Twist.splitKlein_add_sub_self_sub_self _ _

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart20

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_021/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_021.json"

section BundlePart21
/- Source: Papers/RigidityZheng_NullCellule_WeightComponents.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/WeightComponents.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Provenance-preserving weight components

For the edge-to-`K₃` replacement, the old variable `y` has weight zero and
the displacement variable `d` has weight one.  This file proves inside
`MvPolynomial` that the three exact terms have weights `0`, `1`, and `2`.
Consequently the weight-zero initial component of the replaced equation is
literally the old edge equation.  This is the first formal descent statement;
it does not assume an initial-ideal or dimension theorem.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- The edge-to-triangle degeneration weight: the retained `y`-coordinates
have weight zero and the displacement `d`-coordinates have weight one. -/
def triangleWeight : TwistVariable (Fin 2) → ℕ :=
  fun x ↦ x.1.val

@[simp] theorem triangleWeight_zero (c : Bool × Fin 3) :
    triangleWeight (0, c) = 0 := rfl

@[simp] theorem triangleWeight_one (c : Bool × Fin 3) :
    triangleWeight (1, c) = 1 := rfl

theorem triangleY_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (i : Fin 3) :
    IsWeightedHomogeneous triangleWeight
      (X ((0 : Fin 2), b, i) : MvPolynomial (TwistVariable (Fin 2)) k) 0 := by
  simpa [triangleWeight] using
    (isWeightedHomogeneous_X k triangleWeight ((0 : Fin 2), b, i))

theorem triangleD_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (i : Fin 3) :
    IsWeightedHomogeneous triangleWeight
      (X ((1 : Fin 2), b, i) : MvPolynomial (TwistVariable (Fin 2)) k) 1 := by
  simpa [triangleWeight] using
    (isWeightedHomogeneous_X k triangleWeight ((1 : Fin 2), b, i))

theorem triangleA_isWeightedHomogeneous_zero
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight (triangleA (k := k)) 0 := by
  simp only [triangleA, Twist.splitKlein, Vec3.dot, triangleY,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 0
  intro i hi
  simpa using
    (triangleY_coordinate_isWeightedHomogeneous (k := k) false i).mul
      (triangleY_coordinate_isWeightedHomogeneous (k := k) true i)

theorem triangleC_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight (triangleC (k := k)) 2 := by
  simp only [triangleC, Twist.splitKlein, Vec3.dot, triangleD,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro i hi
  simpa using
    (triangleD_coordinate_isWeightedHomogeneous (k := k) false i).mul
      (triangleD_coordinate_isWeightedHomogeneous (k := k) true i)

theorem triangleMixed_isWeightedHomogeneous_one
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous triangleWeight
      (Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k))) 1 := by
  simp only [Twist.mixedPairing, Vec3.dot, triangleY, triangleD,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro i hi
    simpa using
      (triangleY_coordinate_isWeightedHomogeneous (k := k) false i).mul
        (triangleD_coordinate_isWeightedHomogeneous (k := k) true i)
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro i hi
    simpa using
      (triangleD_coordinate_isWeightedHomogeneous (k := k) false i).mul
        (triangleY_coordinate_isWeightedHomogeneous (k := k) true i)

/-- Exact three-layer provenance decomposition of the replacement equation. -/
theorem triangleB_eq_weight_layers {k : Type*} [CommRing k] :
    triangleB (k := k) =
      triangleA (k := k) +
        Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) +
          triangleC (k := k) := by
  rw [triangleB, triangleA, triangleC, triangleY, triangleD,
    Twist.splitKlein_add_mixedPairing]
  ac_rfl

/-- The weight-zero component descends exactly to the old edge equation. -/
theorem triangleB_weightedComponent_zero {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 0 (triangleB (k := k)) =
      triangleA (k := k) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_same]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_ne 0 (by decide)]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_ne 0 (by decide)]
  simp

/-- The weight-one component remembers precisely the mixed incidence term. -/
theorem triangleB_weightedComponent_one {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 1 (triangleB (k := k)) =
      Twist.mixedPairing (triangleY (k := k)) (triangleD (k := k)) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne 1 (by decide)]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_same]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_ne 1 (by decide)]
  simp

/-- The weight-two component is exactly the new displacement null equation. -/
theorem triangleB_weightedComponent_two {k : Type*} [CommRing k] :
    weightedHomogeneousComponent triangleWeight 2 (triangleB (k := k)) =
      triangleC (k := k) := by
  rw [triangleB_eq_weight_layers]
  simp only [map_add]
  rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne 2 (by decide)]
  rw [triangleMixed_isWeightedHomogeneous_one.weightedHomogeneousComponent_ne 2 (by decide)]
  rw [triangleC_isWeightedHomogeneous_two.weightedHomogeneousComponent_same]
  simp

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart21

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_022/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_022.json"

section BundlePart22
/- Source: Papers/RigidityZheng_NullCellule_VertexK4Weight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/VertexK4Weight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Provenance weights for the vertex-to-`K₄` replacement

The retained centre twist `Z` and an external twist `A` have weight zero,
whereas the three clone displacements `D i` have weight one.  This file
records the resulting `0/1/2` decomposition of every external clone-edge
equation.  It also proves that common translation cancels on an internal
clone edge and that the resulting equation is purely of weight two.

The vertex labels below are deliberately explicit: the three displacement
labels remain distinguishable throughout the polynomial calculation.  Thus
the statements retain the provenance needed by a later initial-ideal or
incidence-descent argument; no such geometric theorem is assumed here.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

/-- Provenance labels for one vertex-to-`K₄` replacement chart. -/
inductive VertexK4Label
  | center
  | external
  | displacement (i : Fin 3)
  deriving DecidableEq

/-- The retained central twist. -/
def vertexK4Z {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist VertexK4Label.center

/-- A provenance-labelled external twist. -/
def vertexK4A {k : Type*} [CommRing k] :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist VertexK4Label.external

/-- The displacement of clone `i` from the retained centre. -/
def vertexK4D {k : Type*} [CommRing k] (i : Fin 3) :
    Twist (MvPolynomial (TwistVariable VertexK4Label) k) :=
  universalTwist (VertexK4Label.displacement i)

/-- Centre and external coordinates have weight zero; every clone
displacement coordinate has weight one. -/
def vertexK4Weight : TwistVariable VertexK4Label → ℕ
  | ⟨VertexK4Label.center, _⟩ => 0
  | ⟨VertexK4Label.external, _⟩ => 0
  | ⟨VertexK4Label.displacement _, _⟩ => 1

@[simp] theorem vertexK4Weight_center (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.center, c) = 0 := rfl

@[simp] theorem vertexK4Weight_external (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.external, c) = 0 := rfl

@[simp] theorem vertexK4Weight_displacement (i : Fin 3)
    (c : Bool × Fin 3) :
    vertexK4Weight (VertexK4Label.displacement i, c) = 1 := rfl

theorem vertexK4Z_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.center, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.center, b, j))

theorem vertexK4A_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.external, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.external, b, j))

theorem vertexK4D_coordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (i : Fin 3) (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.displacement i, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 1 := by
  simpa [vertexK4Weight] using
    (isWeightedHomogeneous_X k vertexK4Weight
      (VertexK4Label.displacement i, b, j))

/-- The old external edge equation, before the centre is cloned. -/
def vertexK4OldExternal {k : Type*} [CommRing k] :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4Z (k := k) - vertexK4A (k := k))

/-- The equation on the external edge incident with clone `i`. -/
def vertexK4ExternalClone {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein
    ((vertexK4Z (k := k) + vertexK4D (k := k) i) - vertexK4A (k := k))

/-- The mixed centre/external--displacement term for clone `i`. -/
def vertexK4ExternalMixed {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.mixedPairing
    (vertexK4Z (k := k) - vertexK4A (k := k))
    (vertexK4D (k := k) i)

/-- The pure displacement-null term for clone `i`. -/
def vertexK4DisplacementNull {k : Type*} [CommRing k] (i : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4D (k := k) i)

/-- The internal clone-edge equation between clones `i` and `j`. -/
def vertexK4InternalClone {k : Type*} [CommRing k] (i j : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein
    ((vertexK4Z (k := k) + vertexK4D (k := k) i) -
      (vertexK4Z (k := k) + vertexK4D (k := k) j))

/-- The same internal edge written only in displacement coordinates. -/
def vertexK4InternalDisplacement {k : Type*} [CommRing k] (i j : Fin 3) :
    MvPolynomial (TwistVariable VertexK4Label) k :=
  Twist.splitKlein (vertexK4D (k := k) i - vertexK4D (k := k) j)

private theorem vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (b : Bool) (j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.center, b, j) -
        X (VertexK4Label.external, b, j) :
        MvPolynomial (TwistVariable VertexK4Label) k) 0 := by
  exact (weightedHomogeneousSubmodule k vertexK4Weight 0).sub_mem
    (vertexK4Z_coordinate_isWeightedHomogeneous (k := k) b j)
    (vertexK4A_coordinate_isWeightedHomogeneous (k := k) b j)

private theorem vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
    {k : Type*} [CommRing k] (i j : Fin 3) (b : Bool) (r : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (X (VertexK4Label.displacement i, b, r) -
        X (VertexK4Label.displacement j, b, r) :
        MvPolynomial (TwistVariable VertexK4Label) k) 1 := by
  exact (weightedHomogeneousSubmodule k vertexK4Weight 1).sub_mem
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i b r)
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) j b r)

theorem vertexK4OldExternal_isWeightedHomogeneous_zero
    {k : Type*} [CommRing k] :
    IsWeightedHomogeneous vertexK4Weight (vertexK4OldExternal (k := k)) 0 := by
  simp only [vertexK4OldExternal, Twist.splitKlein, Vec3.dot, vertexK4Z,
    vertexK4A, universalTwist]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 0
  intro j hj
  simpa [angularCoordinate, translationalCoordinate] using
    (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) false j).mul
      (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) true j)

theorem vertexK4DisplacementNull_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4DisplacementNull (k := k) i) 2 := by
  simp only [vertexK4DisplacementNull, Twist.splitKlein, Vec3.dot, vertexK4D,
    universalTwist, angularCoordinate, translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro j hj
  simpa [angularCoordinate, translationalCoordinate] using
    (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i false j).mul
      (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i true j)

theorem vertexK4ExternalMixed_isWeightedHomogeneous_one
    {k : Type*} [CommRing k] (i : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4ExternalMixed (k := k) i) 1 := by
  simp only [vertexK4ExternalMixed, Twist.mixedPairing, Vec3.dot, vertexK4Z,
    vertexK4A, vertexK4D, universalTwist, angularCoordinate,
    translationalCoordinate]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro j hj
    simpa [angularCoordinate, translationalCoordinate] using
      (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) false j).mul
        (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i true j)
  · apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 1
    intro j hj
    simpa [angularCoordinate, translationalCoordinate] using
      (vertexK4D_coordinate_isWeightedHomogeneous (k := k) i false j).mul
        (vertexK4BaseDifferenceCoordinate_isWeightedHomogeneous (k := k) true j)

/-- Exact `0/1/2` provenance decomposition of every external clone edge. -/
theorem vertexK4ExternalClone_eq_weight_layers
    {k : Type*} [CommRing k] (i : Fin 3) :
    vertexK4ExternalClone (k := k) i =
      vertexK4OldExternal (k := k) +
        vertexK4ExternalMixed (k := k) i +
          vertexK4DisplacementNull (k := k) i := by
  rw [vertexK4ExternalClone, vertexK4OldExternal, vertexK4ExternalMixed,
    vertexK4DisplacementNull, Twist.splitKlein_translate_difference]
  ac_rfl

/-- The weight-zero component is literally the original external edge. -/
theorem vertexK4ExternalClone_weightedComponent_zero
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 0
        (vertexK4ExternalClone (k := k) i) =
      vertexK4OldExternal (k := k) := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_same]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_ne
    0 (by decide)]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_ne
    0 (by decide)]
  simp

/-- The weight-one component is precisely the mixed incidence term. -/
theorem vertexK4ExternalClone_weightedComponent_one
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 1
        (vertexK4ExternalClone (k := k) i) =
      vertexK4ExternalMixed (k := k) i := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne
    1 (by decide)]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_same]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_ne
    1 (by decide)]
  simp

/-- The weight-two component is precisely the displacement null term. -/
theorem vertexK4ExternalClone_weightedComponent_two
    {k : Type*} [CommRing k] (i : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 2
        (vertexK4ExternalClone (k := k) i) =
      vertexK4DisplacementNull (k := k) i := by
  rw [vertexK4ExternalClone_eq_weight_layers]
  simp only [map_add]
  rw [vertexK4OldExternal_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne
    2 (by decide)]
  rw [(vertexK4ExternalMixed_isWeightedHomogeneous_one (k := k) i).weightedHomogeneousComponent_ne
    2 (by decide)]
  rw [(vertexK4DisplacementNull_isWeightedHomogeneous_two (k := k) i).weightedHomogeneousComponent_same]
  simp

/-- Common translation by `Z` cancels exactly on an internal clone edge. -/
theorem vertexK4InternalClone_eq_internalDisplacement
    {k : Type*} [CommRing k] (i j : Fin 3) :
    vertexK4InternalClone (k := k) i j =
      vertexK4InternalDisplacement (k := k) i j := by
  exact Twist.splitKlein_common_translate_difference _ _ _

/-- An internal clone edge is purely of provenance weight two. -/
theorem vertexK4InternalDisplacement_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4InternalDisplacement (k := k) i j) 2 := by
  simp only [vertexK4InternalDisplacement, Twist.splitKlein, Vec3.dot,
    vertexK4D, universalTwist]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ 2
  intro r hr
  simpa [angularCoordinate, translationalCoordinate] using
    (vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
      (k := k) i j false r).mul
      (vertexK4DisplacementDifferenceCoordinate_isWeightedHomogeneous
        (k := k) i j true r)

theorem vertexK4InternalClone_isWeightedHomogeneous_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    IsWeightedHomogeneous vertexK4Weight
      (vertexK4InternalClone (k := k) i j) 2 := by
  rw [vertexK4InternalClone_eq_internalDisplacement]
  exact vertexK4InternalDisplacement_isWeightedHomogeneous_two i j

/-- The internal clone edge has no weight-zero contribution. -/
theorem vertexK4InternalClone_weightedComponent_zero
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 0
        (vertexK4InternalClone (k := k) i j) = 0 := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_ne
    0 (by decide)

/-- The internal clone edge has no weight-one contribution. -/
theorem vertexK4InternalClone_weightedComponent_one
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 1
        (vertexK4InternalClone (k := k) i j) = 0 := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_ne
    1 (by decide)

/-- The entire internal clone-edge equation is its weight-two component. -/
theorem vertexK4InternalClone_weightedComponent_two
    {k : Type*} [CommRing k] (i j : Fin 3) :
    weightedHomogeneousComponent vertexK4Weight 2
        (vertexK4InternalClone (k := k) i j) =
      vertexK4InternalClone (k := k) i j := by
  exact (vertexK4InternalClone_isWeightedHomogeneous_two (k := k) i j).weightedHomogeneousComponent_same

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart22

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_023/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_023.json"

section BundlePart23
/- Source: Papers/RigidityZheng_NullCellule_WeightInitialIdeal.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/WeightInitialIdeal.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Minimum-weight initial ideals with provenance

This file packages the minimum nonzero weighted-homogeneous component of a
polynomial as a predicate and defines the corresponding weight-initial ideal.
The definition deliberately keeps the source polynomial: membership in the
initial ideal therefore carries an explicit ideal-theoretic provenance
receipt.

The general cancellation lemma below is the algebraic core of the
edge-to-`K₃` move.  If two ideal elements have identical components below a
given weight, subtracting them exposes the first surviving component, which
is then a generator of the weight-initial ideal.  The local triangle and
vertex-to-`K₄` consequences are proved over `ℚ`, so every claimed initial
form is accompanied by an unconditional nonvanishing proof.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

section InitialIdeal

variable {k σ : Type*} [CommRing k]

/-- `g` is the minimum nonzero `w`-weighted homogeneous component of `f`.
The witnessing degree is retained, while all strictly smaller natural-number
components are required to vanish. -/
def IsInitialComponent (w : σ → ℕ)
    (f g : MvPolynomial σ k) : Prop :=
  ∃ d : ℕ,
    weightedHomogeneousComponent w d f = g ∧
      g ≠ 0 ∧
        ∀ e < d, weightedHomogeneousComponent w e f = 0

/-- The minimum-weight initial ideal, generated by initial components of
actual elements of `I`. -/
def weightInitialIdeal (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  Ideal.span {g | ∃ f ∈ I, IsInitialComponent w f g}

/-- Every provenance-witnessed initial component is a generator of the
weight-initial ideal. -/
theorem initialComponent_mem_weightInitialIdeal
    (w : σ → ℕ) (I : Ideal (MvPolynomial σ k))
    {f g : MvPolynomial σ k} (hf : f ∈ I)
    (hfg : IsInitialComponent w f g) :
    g ∈ weightInitialIdeal w I := by
  apply Ideal.subset_span
  exact ⟨f, hf, hfg⟩

/-- A nonzero weighted-homogeneous ideal element is its own minimum-weight
initial form. -/
theorem isInitialComponent_self_of_isWeightedHomogeneous
    (w : σ → ℕ) {f : MvPolynomial σ k} {d : ℕ}
    (hf : IsWeightedHomogeneous w f d) (hf0 : f ≠ 0) :
    IsInitialComponent w f f := by
  refine ⟨d, hf.weightedHomogeneousComponent_same, hf0, ?_⟩
  intro e he
  exact hf.weightedHomogeneousComponent_ne e (Nat.ne_of_lt he)

/-- Consequently, a nonzero weighted-homogeneous member of `I` belongs to
the weight-initial ideal without changing its polynomial expression. -/
theorem isWeightedHomogeneous_mem_weightInitialIdeal
    (w : σ → ℕ) (I : Ideal (MvPolynomial σ k))
    {f : MvPolynomial σ k} {d : ℕ}
    (hfI : f ∈ I) (hf : IsWeightedHomogeneous w f d) (hf0 : f ≠ 0) :
    f ∈ weightInitialIdeal w I :=
  initialComponent_mem_weightInitialIdeal w I hfI
    (isInitialComponent_self_of_isWeightedHomogeneous w hf hf0)

/-- Weight zero has no lower component, so a nonzero zero-component is
automatically initial. -/
theorem isInitialComponent_of_component_zero
    (w : σ → ℕ) {f g : MvPolynomial σ k}
    (hfg : weightedHomogeneousComponent w 0 f = g) (hg0 : g ≠ 0) :
    IsInitialComponent w f g := by
  refine ⟨0, hfg, hg0, ?_⟩
  intro e he
  exact (Nat.not_lt_zero e he).elim

/-- Same-lower-layer cancellation: after subtracting two polynomials whose
components agree below `d`, the first specified surviving difference is an
initial component. -/
theorem isInitialComponent_sub_of_same_lower_components
    (w : σ → ℕ) {f g h : MvPolynomial σ k} {d : ℕ}
    (hd : weightedHomogeneousComponent w d f -
        weightedHomogeneousComponent w d g = h)
    (hh0 : h ≠ 0)
    (hlow : ∀ e < d,
      weightedHomogeneousComponent w e f =
        weightedHomogeneousComponent w e g) :
    IsInitialComponent w (f - g) h := by
  refine ⟨d, ?_, hh0, ?_⟩
  · simpa only [map_sub] using hd
  · intro e he
    simp only [map_sub, hlow e he, sub_self]

/-- Ideal-theoretic elimination receipt: cancelling equal low-weight layers
of two elements of `I` puts the newly exposed initial form in
`weightInitialIdeal w I`. -/
theorem cancelledInitialComponent_mem_weightInitialIdeal
    (w : σ → ℕ) (I : Ideal (MvPolynomial σ k))
    {f g h : MvPolynomial σ k} {d : ℕ}
    (hf : f ∈ I) (hg : g ∈ I)
    (hd : weightedHomogeneousComponent w d f -
        weightedHomogeneousComponent w d g = h)
    (hh0 : h ≠ 0)
    (hlow : ∀ e < d,
      weightedHomogeneousComponent w e f =
        weightedHomogeneousComponent w e g) :
    h ∈ weightInitialIdeal w I := by
  apply initialComponent_mem_weightInitialIdeal w I (I.sub_mem hf hg)
  exact isInitialComponent_sub_of_same_lower_components w hd hh0 hlow

/-- The zero ideal has zero weight-initial ideal.  This also checks that the
nonzero clause in `IsInitialComponent` rules out a spurious initial form of
the zero polynomial. -/
theorem weightInitialIdeal_bot (w : σ → ℕ) :
    weightInitialIdeal w (⊥ : Ideal (MvPolynomial σ k)) = ⊥ := by
  apply le_antisymm
  · rw [weightInitialIdeal, Ideal.span_le]
    rintro g ⟨f, hf, hfg⟩
    have hf0 : f = 0 := by simpa using hf
    subst f
    rcases hfg with ⟨d, hd, hg0, hlow⟩
    have hg : g = 0 := by simpa using hd.symm
    simp [hg]
  · exact bot_le

end InitialIdeal

/-! ## Explicit nonvanishing witnesses over `ℚ` -/

def rationalAxis : Vec3 ℚ := ![1, 0, 0]

def triangleAWitness : Fin 2 → Twist ℚ
  | 0 => (rationalAxis, rationalAxis)
  | 1 => 0

theorem triangleA_ne_zero : triangleA (k := ℚ) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (assignmentOfTwists triangleAWitness)) hzero
  have hone :
      MvPolynomial.eval (assignmentOfTwists triangleAWitness)
        (triangleA (k := ℚ)) = 1 := by
    rw [triangleA, eval_splitKlein]
    simp [triangleY, triangleAWitness, rationalAxis, Twist.splitKlein,
      Vec3.dot, Fin.sum_univ_succ]
  rw [hone] at heval
  simp at heval

def triangleCWitness : Fin 2 → Twist ℚ
  | 0 => 0
  | 1 => (rationalAxis, rationalAxis)

theorem triangleC_ne_zero : triangleC (k := ℚ) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (assignmentOfTwists triangleCWitness)) hzero
  have hone :
      MvPolynomial.eval (assignmentOfTwists triangleCWitness)
        (triangleC (k := ℚ)) = 1 := by
    rw [triangleC, eval_splitKlein]
    simp [triangleD, triangleCWitness, rationalAxis, Twist.splitKlein,
      Vec3.dot, Fin.sum_univ_succ]
  rw [hone] at heval
  simp at heval

def triangleMixedWitness : Fin 2 → Twist ℚ
  | 0 => (rationalAxis, 0)
  | 1 => (0, rationalAxis)

theorem triangleMixed_ne_zero :
    Twist.mixedPairing (triangleY (k := ℚ)) (triangleD (k := ℚ)) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (assignmentOfTwists triangleMixedWitness)) hzero
  have hone :
      MvPolynomial.eval (assignmentOfTwists triangleMixedWitness)
          (Twist.mixedPairing (triangleY (k := ℚ))
            (triangleD (k := ℚ))) = 1 := by
    simp [Twist.mixedPairing, triangleY, triangleD, universalTwist,
      angularCoordinate, translationalCoordinate, assignmentOfTwists,
      triangleMixedWitness, rationalAxis, Vec3.dot, Fin.sum_univ_succ]
  rw [hone] at heval
  simp at heval

/-! ## The complete edge-to-`K₃` minimum-weight table -/

/-- Provenance names for the three triangle equations
`a = q(y)`, `b = q(y+d)`, and `c = q(d)`. -/
inductive TriangleEquation
  | a
  | b
  | c
  deriving DecidableEq

/-- The polynomial carried by a named triangle equation. -/
def triangleEquationPolynomial : TriangleEquation →
    MvPolynomial (TwistVariable (Fin 2)) ℚ
  | .a => triangleA
  | .b => triangleB
  | .c => triangleC

/-- The ideal generated by a selected subset of the three local triangle
equations. -/
def triangleSelectionIdeal (S : Finset TriangleEquation) :
    Ideal (MvPolynomial (TwistVariable (Fin 2)) ℚ) :=
  Ideal.span {p | ∃ e ∈ S, triangleEquationPolynomial e = p}

theorem triangleEquation_mem_selectionIdeal
    {S : Finset TriangleEquation} {e : TriangleEquation} (he : e ∈ S) :
    triangleEquationPolynomial e ∈ triangleSelectionIdeal S := by
  apply Ideal.subset_span
  exact ⟨e, he, rfl⟩

theorem triangleA_mem_initial_of_a_selected
    {S : Finset TriangleEquation} (ha : TriangleEquation.a ∈ S) :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal S) := by
  apply isWeightedHomogeneous_mem_weightInitialIdeal triangleWeight
    (triangleSelectionIdeal S)
  · exact triangleEquation_mem_selectionIdeal ha
  · exact triangleA_isWeightedHomogeneous_zero
  · exact triangleA_ne_zero

theorem triangleA_mem_initial_of_b_selected
    {S : Finset TriangleEquation} (hb : TriangleEquation.b ∈ S) :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal S) := by
  apply initialComponent_mem_weightInitialIdeal triangleWeight
    (triangleSelectionIdeal S) (triangleEquation_mem_selectionIdeal hb)
  apply isInitialComponent_of_component_zero triangleWeight
  · exact triangleB_weightedComponent_zero
  · exact triangleA_ne_zero

theorem triangleC_mem_initial_of_c_selected
    {S : Finset TriangleEquation} (hc : TriangleEquation.c ∈ S) :
    triangleC (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal S) := by
  apply isWeightedHomogeneous_mem_weightInitialIdeal triangleWeight
    (triangleSelectionIdeal S)
  · exact triangleEquation_mem_selectionIdeal hc
  · exact triangleC_isWeightedHomogeneous_two
  · exact triangleC_ne_zero

/-- Selecting both `a` and `b` exposes the mixed weight-one receipt after
their common weight-zero layer is cancelled. -/
theorem triangleMixed_mem_initial_of_ab_selected
    {S : Finset TriangleEquation}
    (ha : TriangleEquation.a ∈ S) (hb : TriangleEquation.b ∈ S) :
    Twist.mixedPairing (triangleY (k := ℚ)) (triangleD (k := ℚ)) ∈
      weightInitialIdeal triangleWeight (triangleSelectionIdeal S) := by
  have hbI : triangleB (k := ℚ) ∈ triangleSelectionIdeal S := by
    simpa [triangleEquationPolynomial] using
      (triangleEquation_mem_selectionIdeal hb)
  have haI : triangleA (k := ℚ) ∈ triangleSelectionIdeal S := by
    simpa [triangleEquationPolynomial] using
      (triangleEquation_mem_selectionIdeal ha)
  apply cancelledInitialComponent_mem_weightInitialIdeal triangleWeight
    (triangleSelectionIdeal S) (d := 1) hbI haI
  · rw [triangleB_weightedComponent_one]
    rw [triangleA_isWeightedHomogeneous_zero.weightedHomogeneousComponent_ne
      1 (by decide)]
    simp
  · exact triangleMixed_ne_zero
  · intro e he
    have he0 : e = 0 := by omega
    subst e
    rw [triangleB_weightedComponent_zero]
    exact
      (triangleA_isWeightedHomogeneous_zero (k := ℚ)).weightedHomogeneousComponent_same.symm

/-- No selected local equation produces no initial equation. -/
theorem triangle_initial_table_none :
    weightInitialIdeal triangleWeight
      (triangleSelectionIdeal (∅ : Finset TriangleEquation)) = ⊥ := by
  rw [show triangleSelectionIdeal (∅ : Finset TriangleEquation) = ⊥ by
    simp [triangleSelectionIdeal]]
  exact weightInitialIdeal_bot triangleWeight

/-- The singleton `c` row contributes the pure displacement null equation. -/
theorem triangle_initial_table_c :
    triangleC (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal ({TriangleEquation.c} :
        Finset TriangleEquation)) := by
  exact triangleC_mem_initial_of_c_selected (by simp)

/-- The singleton `a` row retains the old equation. -/
theorem triangle_initial_table_a :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal ({TriangleEquation.a} :
        Finset TriangleEquation)) := by
  exact triangleA_mem_initial_of_a_selected (by simp)

/-- The symmetric singleton `b` row has the same old weight-zero equation. -/
theorem triangle_initial_table_b :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
      (triangleSelectionIdeal ({TriangleEquation.b} :
        Finset TriangleEquation)) := by
  exact triangleA_mem_initial_of_b_selected (by simp)

/-- For the pair `{a,b}`, both the old equation and the mixed
linear-in-`d` receipt occur in the initial ideal. -/
theorem triangle_initial_table_ab :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.a, TriangleEquation.b} :
            Finset TriangleEquation)) ∧
      Twist.mixedPairing (triangleY (k := ℚ)) (triangleD (k := ℚ)) ∈
        weightInitialIdeal triangleWeight
          (triangleSelectionIdeal
            ({TriangleEquation.a, TriangleEquation.b} :
              Finset TriangleEquation)) := by
  constructor
  · exact triangleA_mem_initial_of_a_selected (by simp)
  · exact triangleMixed_mem_initial_of_ab_selected (by simp) (by simp)

/-- The `{a,c}` representative of the “one `u`-edge plus `c`” row. -/
theorem triangle_initial_table_ac :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.a, TriangleEquation.c} :
            Finset TriangleEquation)) ∧
      triangleC (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.a, TriangleEquation.c} :
            Finset TriangleEquation)) := by
  constructor
  · exact triangleA_mem_initial_of_a_selected (by simp)
  · exact triangleC_mem_initial_of_c_selected (by simp)

/-- The symmetric `{b,c}` representative has the same old/local initial
equations. -/
theorem triangle_initial_table_bc :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.b, TriangleEquation.c} :
            Finset TriangleEquation)) ∧
      triangleC (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.b, TriangleEquation.c} :
            Finset TriangleEquation)) := by
  constructor
  · exact triangleA_mem_initial_of_b_selected (by simp)
  · exact triangleC_mem_initial_of_c_selected (by simp)

/-- The full `{a,b,c}` row contains the old equation, the pure displacement
null equation, and the mixed incidence receipt. -/
theorem triangle_initial_table_abc :
    triangleA (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.a, TriangleEquation.b, TriangleEquation.c} :
            Finset TriangleEquation)) ∧
      triangleC (k := ℚ) ∈ weightInitialIdeal triangleWeight
        (triangleSelectionIdeal
          ({TriangleEquation.a, TriangleEquation.b, TriangleEquation.c} :
            Finset TriangleEquation)) ∧
      Twist.mixedPairing (triangleY (k := ℚ)) (triangleD (k := ℚ)) ∈
        weightInitialIdeal triangleWeight
          (triangleSelectionIdeal
            ({TriangleEquation.a, TriangleEquation.b, TriangleEquation.c} :
              Finset TriangleEquation)) := by
  constructor
  · exact triangleA_mem_initial_of_a_selected (by simp)
  constructor
  · exact triangleC_mem_initial_of_c_selected (by simp)
  · exact triangleMixed_mem_initial_of_ab_selected (by simp) (by simp)

/-! ## Vertex-to-`K₄` initial-ideal receipts -/

def vertexK4OldWitness : VertexK4Label → Twist ℚ
  | .center => (rationalAxis, rationalAxis)
  | .external => 0
  | .displacement _ => 0

theorem vertexK4OldExternal_ne_zero :
    vertexK4OldExternal (k := ℚ) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (assignmentOfTwists vertexK4OldWitness)) hzero
  have hone :
      MvPolynomial.eval (assignmentOfTwists vertexK4OldWitness)
        (vertexK4OldExternal (k := ℚ)) = 1 := by
    rw [vertexK4OldExternal, eval_splitKlein, evalPolynomialTwist_sub]
    simp [vertexK4Z, vertexK4A, vertexK4OldWitness, rationalAxis,
      Twist.splitKlein, Vec3.dot, Fin.sum_univ_succ]
  rw [hone] at heval
  simp at heval

theorem vertexK4InternalClone_ne_zero {i j : Fin 3} (hij : i ≠ j) :
    vertexK4InternalClone (k := ℚ) i j ≠ 0 := by
  let Y : VertexK4Label → Twist ℚ := fun label ↦
    if label = VertexK4Label.displacement i then
      (rationalAxis, rationalAxis)
    else 0
  intro hzero
  have heval := congrArg (MvPolynomial.eval (assignmentOfTwists Y)) hzero
  have hone :
      MvPolynomial.eval (assignmentOfTwists Y)
        (vertexK4InternalClone (k := ℚ) i j) = 1 := by
    rw [vertexK4InternalClone_eq_internalDisplacement,
      vertexK4InternalDisplacement, eval_splitKlein,
      evalPolynomialTwist_sub]
    simp [vertexK4D, Y, Ne.symm hij, rationalAxis, Twist.splitKlein, Vec3.dot,
      Fin.sum_univ_succ]
  rw [hone] at heval
  simp at heval

/-- Any ideal containing an external clone-edge equation has the contracted
old external equation in its weight-initial ideal. -/
theorem vertexK4OldExternal_mem_initial_of_externalClone_mem
    (I : Ideal (MvPolynomial (TwistVariable VertexK4Label) ℚ))
    (i : Fin 3) (hi : vertexK4ExternalClone (k := ℚ) i ∈ I) :
    vertexK4OldExternal (k := ℚ) ∈
      weightInitialIdeal vertexK4Weight I := by
  apply initialComponent_mem_weightInitialIdeal vertexK4Weight I hi
  apply isInitialComponent_of_component_zero vertexK4Weight
  · exact vertexK4ExternalClone_weightedComponent_zero i
  · exact vertexK4OldExternal_ne_zero

/-- A genuine internal clone edge (`i ≠ j`) is purely of weight two and
therefore enters the initial ideal unchanged. -/
theorem vertexK4InternalClone_mem_initial_of_mem
    (I : Ideal (MvPolynomial (TwistVariable VertexK4Label) ℚ))
    {i j : Fin 3} (hij : i ≠ j)
    (hijI : vertexK4InternalClone (k := ℚ) i j ∈ I) :
    vertexK4InternalClone (k := ℚ) i j ∈
      weightInitialIdeal vertexK4Weight I := by
  apply isWeightedHomogeneous_mem_weightInitialIdeal vertexK4Weight I hijI
  · exact vertexK4InternalClone_isWeightedHomogeneous_two i j
  · exact vertexK4InternalClone_ne_zero hij

/-- Principal-ideal form of the external-edge contraction receipt. -/
theorem vertexK4_external_principal_initial (i : Fin 3) :
    vertexK4OldExternal (k := ℚ) ∈
      weightInitialIdeal vertexK4Weight
        (Ideal.span ({vertexK4ExternalClone (k := ℚ) i} :
          Set (MvPolynomial (TwistVariable VertexK4Label) ℚ))) := by
  apply vertexK4OldExternal_mem_initial_of_externalClone_mem (i := i)
  exact Ideal.subset_span (by simp)

/-- Principal-ideal form of the pure weight-two internal-edge receipt. -/
theorem vertexK4_internal_principal_initial
    {i j : Fin 3} (hij : i ≠ j) :
    vertexK4InternalClone (k := ℚ) i j ∈
      weightInitialIdeal vertexK4Weight
        (Ideal.span ({vertexK4InternalClone (k := ℚ) i j} :
          Set (MvPolynomial (TwistVariable VertexK4Label) ℚ))) := by
  apply vertexK4InternalClone_mem_initial_of_mem _ hij
  exact Ideal.subset_span (by simp)

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart23

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_024/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_024.json"

section BundlePart24
/- Source: Papers/RigidityZheng_Algebra_FilteredInitialHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/FilteredInitialHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/






@[expose] public section

/-!
# Filtered initial forms and a height-comparison interface

The project uses the minimum nonzero component for a nonnegative natural
weight. Mathlib's Rees algebra is currently the Rees algebra of powers of a
single ideal; it does not provide the flat one-parameter family attached to an
arbitrary weight filtration. Accordingly, this file proves the part of that
bridge which can be checked directly from the graded decomposition:

* multiplication by a weight-zero polynomial commutes with every weighted
  component;
* a nonzero weight-zero factor carries initial forms to initial forms;
* denominator clearing by such a factor gives a provenance receipt in the
  weight-initial ideal;
* a prime ideal containing products from disjoint variable pairs chooses one
  variable from every pair, and these choices remain distinct.

The last section names the flat-degeneration height comparison as an explicit
proposition.  The results in this file do not assume that proposition.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

section WeightZero

variable {k σ : Type*} [CommRing k]

set_option maxRecDepth 10000

/-- Weighted components of a product are the convolution of the weighted
components.  This is the multiplicativity law of the natural-number weight
filtration, exposed at the polynomial level. -/
theorem weightedHomogeneousComponent_mul
    (w : σ → ℕ) (f g : MvPolynomial σ k) (n : ℕ) :
    weightedHomogeneousComponent w n (f * g) =
      ∑ ij ∈ Finset.antidiagonal n,
        weightedHomogeneousComponent w ij.1 f *
          weightedHomogeneousComponent w ij.2 g := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule k w) :=
    weightedGradedAlgebra k w
  rw [← weightedDecomposition.decompose'_apply k w (f * g) n]
  change
    ((DirectSum.decompose (weightedHomogeneousSubmodule k w) (f * g)) n :
        MvPolynomial σ k) = _
  rw [DirectSum.decompose_mul,
    DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [← weightedDecomposition.decompose'_apply k w f ij.1,
    ← weightedDecomposition.decompose'_apply k w g ij.2]
  rfl

/-- Initial components multiply over a domain.  In particular, the minimum
weight of a product is the sum of the two minimum weights. -/
theorem IsInitialComponent.mul [IsDomain k]
    (w : σ → ℕ) {f f₀ g g₀ : MvPolynomial σ k}
    (hf : IsInitialComponent w f f₀)
    (hg : IsInitialComponent w g g₀) :
    IsInitialComponent w (f * g) (f₀ * g₀) := by
  rcases hf with ⟨d, hfd, hf₀, hflow⟩
  rcases hg with ⟨e, hge, hg₀, hglow⟩
  refine ⟨d + e, ?_, mul_ne_zero hf₀ hg₀, ?_⟩
  · rw [weightedHomogeneousComponent_mul]
    rw [Finset.sum_eq_single (d, e)]
    · rw [hfd, hge]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = d + e := by
        simpa using (Finset.mem_antidiagonal.mp hij)
      by_cases hi : i < d
      · rw [hflow i hi, zero_mul]
      by_cases hj : j < e
      · rw [hglow j hj, mul_zero]
      exfalso
      apply hne
      apply Prod.ext <;> omega
    · simp
  · intro n hn
    rw [weightedHomogeneousComponent_mul]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij' : i + j = n := by
      simpa using (Finset.mem_antidiagonal.mp hij)
    by_cases hi : i < d
    · rw [hflow i hi, zero_mul]
    · have hj : j < e := by omega
      rw [hglow j hj, mul_zero]

/-- Multiplication on the left by a weight-zero homogeneous polynomial
commutes with projection to every weighted component. -/
theorem weightedHomogeneousComponent_mul_left_zero
    (w : σ → ℕ) {s f : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (d : ℕ) :
    weightedHomogeneousComponent w d (s * f) =
      s * weightedHomogeneousComponent w d f := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule k w) :=
    weightedGradedAlgebra k w
  rw [← weightedDecomposition.decompose'_apply k w (s * f) d,
    ← weightedDecomposition.decompose'_apply k w f d]
  exact DirectSum.coe_decompose_mul_of_left_mem_zero
    (weightedHomogeneousSubmodule k w) (a := s) (b := f) (j := d) hs

/-- The right-handed form; it is stated separately so callers do not need to
normalize commutative products by hand. -/
theorem weightedHomogeneousComponent_mul_right_zero
    (w : σ → ℕ) {s f : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (d : ℕ) :
    weightedHomogeneousComponent w d (f * s) =
      weightedHomogeneousComponent w d f * s := by
  rw [mul_comm f s, weightedHomogeneousComponent_mul_left_zero w hs d,
    mul_comm s]

/-- A nonzero weight-zero factor preserves the exact initial degree and
multiplies the initial form. The domain assumption is used only to prevent
the displayed product from vanishing. -/
theorem IsInitialComponent.mul_left_weightZero
    [IsDomain k] (w : σ → ℕ) {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hfg : IsInitialComponent w f g) :
    IsInitialComponent w (s * f) (s * g) := by
  rcases hfg with ⟨d, hd, hg0, hlow⟩
  refine ⟨d, ?_, mul_ne_zero hs0 hg0, ?_⟩
  · rw [weightedHomogeneousComponent_mul_left_zero w hs d, hd]
  · intro e he
    rw [weightedHomogeneousComponent_mul_left_zero w hs e, hlow e he,
      mul_zero]

/-- Right multiplication by a nonzero weight-zero factor preserves an
initial component. -/
theorem IsInitialComponent.mul_right_weightZero
    [IsDomain k] (w : σ → ℕ) {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hfg : IsInitialComponent w f g) :
    IsInitialComponent w (f * s) (g * s) := by
  simpa only [mul_comm f s, mul_comm g s] using
    hfg.mul_left_weightZero w hs hs0

/-- The weight-initial ideal is monotone in the source ideal. -/
theorem weightInitialIdeal_mono
    (w : σ → ℕ) {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) :
    weightInitialIdeal w I ≤ weightInitialIdeal w J := by
  rw [weightInitialIdeal, weightInitialIdeal, Ideal.span_le]
  rintro g ⟨f, hfI, hfg⟩
  exact Ideal.subset_span ⟨f, hIJ hfI, hfg⟩

/-- Denominator-clearing receipt for localization at nonzero weight-zero
elements. If s * f lies in I and g is the initial form of f, then
s * g lies in the initial ideal of I.

This is the exact algebraic statement needed before passing to fractions; it
does not assume or claim a localization/initial-ideal equivalence. -/
theorem weightZero_denominatorClearing_mem_weightInitialIdeal
    [IsDomain k] (w : σ → ℕ) (I : Ideal (MvPolynomial σ k))
    {s f g : MvPolynomial σ k}
    (hs : IsWeightedHomogeneous w s 0) (hs0 : s ≠ 0)
    (hsf : s * f ∈ I) (hfg : IsInitialComponent w f g) :
    s * g ∈ weightInitialIdeal w I :=
  initialComponent_mem_weightInitialIdeal w I hsf
    (hfg.mul_left_weightZero w hs hs0)

/-- The multiplicative system of nonzero weight-zero homogeneous
polynomials. -/
def nonzeroWeightZeroSubmonoid [IsDomain k] (w : σ → ℕ) :
    Submonoid (MvPolynomial σ k) where
  carrier := {s | IsWeightedHomogeneous w s 0 ∧ s ≠ 0}
  one_mem' := ⟨isWeightedHomogeneous_one k w, one_ne_zero⟩
  mul_mem' hs ht := ⟨hs.1.mul ht.1, mul_ne_zero hs.2 ht.2⟩

@[simp]
theorem mem_nonzeroWeightZeroSubmonoid [IsDomain k]
    (w : σ → ℕ) (s : MvPolynomial σ k) :
    s ∈ nonzeroWeightZeroSubmonoid (k := k) w ↔
      IsWeightedHomogeneous w s 0 ∧ s ≠ 0 :=
  Iff.rfl

/-- Actual localization compatibility.  If `f` belongs to the extension of
`I` after inverting all nonzero weight-zero elements, then every initial form
`g` of `f` belongs to the extension of `weightInitialIdeal w I` in the same
localization.

The proof extracts a genuine denominator from mathlib's localization
membership theorem and applies the denominator-clearing receipt above. -/
theorem initialComponent_mem_localized_weightInitialIdeal
    [IsDomain k] (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k))
    {A : Type*} [CommRing A] [Algebra (MvPolynomial σ k) A]
    [IsLocalization (nonzeroWeightZeroSubmonoid (k := k) w) A]
    {f g : MvPolynomial σ k}
    (hf : algebraMap (MvPolynomial σ k) A f ∈
      I.map (algebraMap (MvPolynomial σ k) A))
    (hfg : IsInitialComponent w f g) :
    algebraMap (MvPolynomial σ k) A g ∈
      (weightInitialIdeal w I).map
        (algebraMap (MvPolynomial σ k) A) := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    (nonzeroWeightZeroSubmonoid (k := k) w) A] at hf ⊢
  obtain ⟨s, hs, hsf⟩ := hf
  exact ⟨s, hs,
    weightZero_denominatorClearing_mem_weightInitialIdeal
      w I hs.1 hs.2 hsf hfg⟩

end WeightZero

section DisjointPairs

variable {k σ ι : Type*} [CommRing k]

/-! ### Coordinate ideals -/

/-- The ideal generated by the coordinate variables named by `S`. -/
def coordinateVariableIdeal (S : Set σ) : Ideal (MvPolynomial σ k) :=
  Ideal.span (X '' S)

/-- Set the variables in `S` to zero and retain the complementary variables.
The target variable type remembers the complement membership. -/
def coordinateComplementHom (S : Set σ) :
    MvPolynomial σ k →+* MvPolynomial {x : σ // x ∉ S} k :=
  (MvPolynomial.killCompl (R := k)
    (f := fun x : {x : σ // x ∉ S} ↦ (x : σ))
    Subtype.val_injective).toRingHom

/-- A coordinate variable belongs to the coordinate ideal exactly when its
name belongs to the chosen set. -/
theorem X_mem_coordinateVariableIdeal_iff [Nontrivial k]
    (S : Set σ) (x : σ) :
    X x ∈ coordinateVariableIdeal (k := k) S ↔ x ∈ S := by
  rw [coordinateVariableIdeal, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    obtain ⟨i, hiS, hi⟩ := h (Finsupp.single x 1) (by simp [support_X])
    have hix : i = x := by
      by_contra hne
      simp [hne] at hi
    simpa [hix] using hiS
  · intro hxS m hm
    rw [support_X] at hm
    simp only [Finset.mem_singleton] at hm
    subst m
    exact ⟨x, hxS, by simp⟩

/-- The coordinate ideal is exactly the kernel of evaluation which kills
those coordinates.  This is the substantive bridge used to prove primality;
it is proved coefficientwise, rather than postulated. -/
theorem coordinateVariableIdeal_eq_ker_coordinateComplementHom
    (S : Set σ) :
    coordinateVariableIdeal (k := k) S =
      RingHom.ker (coordinateComplementHom (k := k) S) := by
  classical
  apply le_antisymm
  · rw [coordinateVariableIdeal, Ideal.span_le]
    rintro _ ⟨x, hxS, rfl⟩
    change coordinateComplementHom (k := k) S (X x) = 0
    simp [coordinateComplementHom, MvPolynomial.killCompl, hxS]
  · intro p hp
    rw [coordinateVariableIdeal, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hexists
    push Not at hexists
    let f : {x : σ // x ∉ S} → σ := fun x ↦ (x : σ)
    have hf : Function.Injective f := Subtype.val_injective
    have hmSub : (↑m.support : Set σ) ⊆ Set.range f := by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      intro hxS
      exact (Finsupp.mem_support_iff.mp hx) (hexists x hxS)
    let n : {x : σ // x ∉ S} →₀ ℕ :=
      m.comapDomain f hf.injOn
    have hmap : n.mapDomain f = m := by
      exact m.mapDomain_comapDomain f hf hmSub
    change coordinateComplementHom (k := k) S p = 0 at hp
    have hcoeff := congrArg (fun q : MvPolynomial {x : σ // x ∉ S} k ↦ q.coeff n) hp
    have hcoeff' : p.coeff (n.mapDomain f) = 0 := by
      change ((MvPolynomial.killCompl (R := k) (f := f) hf) p).coeff n = 0 at hcoeff
      rw [MvPolynomial.coeff_killCompl] at hcoeff
      exact hcoeff
    rw [hmap] at hcoeff'
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff'

/-- Coordinate ideals over a domain are prime: their quotient is witnessed
by the polynomial ring on the complementary variables. -/
theorem coordinateVariableIdeal_isPrime [IsDomain k] (S : Set σ) :
    (coordinateVariableIdeal (k := k) S).IsPrime := by
  rw [coordinateVariableIdeal_eq_ker_coordinateComplementHom]
  exact RingHom.ker_isPrime (coordinateComplementHom (k := k) S)

/-! ### Height of a finite coordinate ideal -/

/-- The variables among an injectively labelled finite family whose indices
occur strictly before `j`. -/
def coordinatePrefixSet {n : ℕ} (c : Fin n → σ) (j : Fin (n + 1)) : Set σ :=
  {x | ∃ i : Fin n, i.1 < j.1 ∧ c i = x}

theorem coordinatePrefixSet_mono {n : ℕ} (c : Fin n → σ)
    {j l : Fin (n + 1)} (hjl : j ≤ l) :
    coordinatePrefixSet c j ⊆ coordinatePrefixSet c l := by
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, lt_of_lt_of_le hi hjl, rfl⟩

/-- Successive prefix coordinate ideals are genuinely distinct. -/
theorem coordinatePrefixIdeal_lt [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c)
    {j l : Fin (n + 1)} (hjl : j < l) :
    coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) <
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) := by
  have hle :
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) ≤
        coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) := by
    exact Ideal.span_mono (Set.image_mono
      (coordinatePrefixSet_mono c hjl.le))
  refine lt_of_le_of_ne hle ?_
  let i : Fin n := ⟨j.1, by omega⟩
  have hiL : c i ∈ coordinatePrefixSet c l := by
    exact ⟨i, hjl, rfl⟩
  have hiJ : c i ∉ coordinatePrefixSet c j := by
    rintro ⟨q, hq, hqc⟩
    have hqi : q = i := hc hqc
    subst q
    exact (Nat.lt_irrefl j.1) hq
  intro heq
  have hxL : X (c i) ∈
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c l) :=
    (X_mem_coordinateVariableIdeal_iff
      (k := k) (coordinatePrefixSet c l) (c i)).2 hiL
  have hxJ : X (c i) ∈
      coordinateVariableIdeal (k := k) (coordinatePrefixSet c j) := by
    rw [heq]
    exact hxL
  exact hiJ ((X_mem_coordinateVariableIdeal_iff
    (k := k) (coordinatePrefixSet c j) (c i)).1 hxJ)

theorem coordinatePrefixSet_last {n : ℕ} (c : Fin n → σ) :
    coordinatePrefixSet c (Fin.last n) = Set.range c := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Set.mem_range_self i
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

/-- The coordinate ideal generated by `n` distinct variables has height at
least `n`.  The proof is an explicit chain of `n + 1` prime coordinate
ideals, not a dimension formula imported from algebraic geometry. -/
theorem coordinateVariableIdeal_height_ge_card [IsDomain k] {n : ℕ}
    (c : Fin n → σ) (hc : Function.Injective c) :
    (n : ℕ∞) ≤ (coordinateVariableIdeal (k := k) (Set.range c)).height := by
  let p : Fin (n + 1) → PrimeSpectrum (MvPolynomial σ k) := fun j ↦
    ⟨coordinateVariableIdeal (k := k) (coordinatePrefixSet c j),
      coordinateVariableIdeal_isPrime (k := k) (coordinatePrefixSet c j)⟩
  have hp : StrictMono p := by
    intro j l hjl
    exact coordinatePrefixIdeal_lt (k := k) c hc hjl
  let chain : LTSeries (PrimeSpectrum (MvPolynomial σ k)) :=
    LTSeries.mk n p hp
  have hchain := Order.length_le_height_last (p := chain)
  have hlast : chain.last.asIdeal =
      coordinateVariableIdeal (k := k) (Set.range c) := by
    change coordinateVariableIdeal (k := k)
      (coordinatePrefixSet c (Fin.last n)) = _
    rw [coordinatePrefixSet_last]
  haveI : (coordinateVariableIdeal (k := k) (Set.range c)).IsPrime :=
    coordinateVariableIdeal_isPrime (k := k) (Set.range c)
  have hlast' : chain.last =
      (⟨coordinateVariableIdeal (k := k) (Set.range c), inferInstance⟩ :
        PrimeSpectrum (MvPolynomial σ k)) :=
    PrimeSpectrum.ext hlast
  rw [hlast'] at hchain
  rw [← PrimeSpectrum.height_eq_orderHeight] at hchain
  simpa [chain] using hchain

/-- The monomial ideal generated by a family of variable products. -/
def pairedVariableIdeal (a b : ι → σ) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range fun i ↦ X (a i) * X (b i))

/-- Every named pair product belongs to its paired-variable ideal. -/
theorem pairProduct_mem_pairedVariableIdeal (a b : ι → σ) (i : ι) :
    X (a i) * X (b i) ∈ pairedVariableIdeal (k := k) a b :=
  Ideal.subset_span (Set.mem_range_self i)

/-- A prime containing the paired-variable ideal contains at least one
endpoint of every pair. -/
theorem prime_mem_left_or_right_of_pairedVariableIdeal_le
    (a b : ι → σ) (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : pairedVariableIdeal (k := k) a b ≤ P) (i : ι) :
    X (a i) ∈ P ∨ X (b i) ∈ P := by
  exact Ideal.IsPrime.mem_or_mem (I := P) inferInstance
    (hP (pairProduct_mem_pairedVariableIdeal (k := k) a b i))

/-- A convenient disjointness formulation for the two endpoint maps: no
endpoint of one named pair is equal to any endpoint of another pair, and the
two endpoints of each pair are also different. -/
def PairwiseDisjointEndpoints (a b : ι → σ) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧
    ∀ i j, a i ≠ b j

/-- From a prime cover of pair products, choose one endpoint in every pair.
Under PairwiseDisjointEndpoints, the chosen variables are still indexed
injectively, and their coordinate ideal is contained in the prime. -/
theorem exists_injective_coordinateChoice_le_prime
    (a b : ι → σ) (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hdisj : PairwiseDisjointEndpoints a b)
    (hP : pairedVariableIdeal (k := k) a b ≤ P) :
    ∃ c : ι → σ,
      Function.Injective c ∧
      (∀ i, c i = a i ∨ c i = b i) ∧
      Ideal.span (Set.range fun i ↦ X (c i)) ≤ P := by
  classical
  let c : ι → σ := fun i ↦ if X (a i) ∈ P then a i else b i
  have hcSide : ∀ i, c i = a i ∨ c i = b i := by
    intro i
    by_cases hi : X (a i) ∈ P
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  have hcP : ∀ i, X (c i) ∈ P := by
    intro i
    by_cases hi : X (a i) ∈ P
    · simp [c, hi]
    · have hir := prime_mem_left_or_right_of_pairedVariableIdeal_le
        (k := k) a b P hP i
      exact by simpa [c, hi] using hir.resolve_left hi
  refine ⟨c, ?_, hcSide, ?_⟩
  · intro i j hij
    rcases hcSide i with hia | hib <;>
      rcases hcSide j with hja | hjb
    · exact hdisj.1 (hia.symm.trans (hij.trans hja))
    · exact ((hdisj.2.2 i j) (hia.symm.trans (hij.trans hjb))).elim
    · exact ((hdisj.2.2 j i) (hja.symm.trans (hij.symm.trans hib))).elim
    · exact hdisj.2.1 (hib.symm.trans (hij.trans hjb))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hcP i

/-- The monomial ideal generated by `n` pairwise-disjoint variable products
has height at least `n`.  Every minimal prime must choose one endpoint from
each pair; the preceding explicit coordinate-prime chain then supplies the
height bound. -/
theorem pairedVariableIdeal_height_ge_card [IsDomain k] {n : ℕ}
    (a b : Fin n → σ) (hdisj : PairwiseDisjointEndpoints a b) :
    (n : ℕ∞) ≤ (pairedVariableIdeal (k := k) a b).height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  apply le_iInf
  intro P
  apply le_iInf
  intro hP
  letI : P.IsPrime := hP.1.1
  obtain ⟨c, hc, _, hcoord⟩ :=
    exists_injective_coordinateChoice_le_prime
      (k := k) a b P hdisj hP.1.2
  have himage :
      (X '' Set.range c : Set (MvPolynomial σ k)) =
        Set.range (fun i ↦ (X (c i) : MvPolynomial σ k)) := by
    ext q
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨c i, ⟨i, rfl⟩, rfl⟩
  have hcoord' :
      coordinateVariableIdeal (k := k) (Set.range c) ≤ P := by
    simpa [coordinateVariableIdeal, himage] using hcoord
  have hge := coordinateVariableIdeal_height_ge_card (k := k) c hc
  have hfinal := hge.trans (Ideal.height_mono hcoord')
  exact hfinal

/-- Over a Noetherian coefficient ring with finitely many ambient variables,
the preceding lower bound meets Krull's height theorem.  Hence the
pairwise-disjoint product ideal has height exactly the number of pairs. -/
theorem pairedVariableIdeal_height_eq_card
    [IsDomain k] [IsNoetherianRing k] [Finite σ] {n : ℕ}
    (a b : Fin n → σ) (hdisj : PairwiseDisjointEndpoints a b) :
    (pairedVariableIdeal (k := k) a b).height = (n : ℕ∞) := by
  let g : Fin n → MvPolynomial σ k := fun i ↦ X (a i) * X (b i)
  let cc : MvPolynomial σ k →+* k := MvPolynomial.constantCoeff
  have hker : pairedVariableIdeal (k := k) a b ≤ RingHom.ker cc := by
    rw [pairedVariableIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change cc (X (a i) * X (b i)) = 0
    simp [cc]
  have hne : pairedVariableIdeal (k := k) a b ≠ ⊤ :=
    ne_top_of_le_ne_top (RingHom.ker_ne_top cc) hker
  have hspan : (pairedVariableIdeal (k := k) a b).spanFinrank ≤ n := by
    change (Ideal.span (Set.range g)).spanFinrank ≤ n
    refine (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.finite_range g)).trans ?_
    rw [← Set.image_univ]
    simpa using Set.ncard_image_le (f := g) (s := Set.univ)
  apply le_antisymm
  · apply (Ideal.height_le_spanFinrank _ hne).trans
    exact_mod_cast hspan
  · exact pairedVariableIdeal_height_ge_card (k := k) a b hdisj

/-- A directly usable initial-ideal bridge: inclusion of a disjoint-pair
monomial ideal forces the weight-initial ideal itself to have height at least
the number of pairs.  This statement needs no flatness comparison. -/
theorem weightInitialIdeal_height_ge_card_of_pairedVariableIdeal_le
    [IsDomain k] {n : ℕ} (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k)) (a b : Fin n → σ)
    (hdisj : PairwiseDisjointEndpoints a b)
    (hpair : pairedVariableIdeal (k := k) a b ≤ weightInitialIdeal w I) :
    (n : ℕ∞) ≤ (weightInitialIdeal w I).height :=
  (pairedVariableIdeal_height_ge_card (k := k) a b hdisj).trans
    (Ideal.height_mono hpair)

/-- Membership form of the preceding theorem.  It matches local initial-form
certificates, which normally establish the pair products one at a time. -/
theorem weightInitialIdeal_height_ge_card_of_disjoint_pair_members
    [IsDomain k] {n : ℕ} (w : σ → ℕ)
    (I : Ideal (MvPolynomial σ k)) (a b : Fin n → σ)
    (hdisj : PairwiseDisjointEndpoints a b)
    (hpair : ∀ i, X (a i) * X (b i) ∈ weightInitialIdeal w I) :
    (n : ℕ∞) ≤ (weightInitialIdeal w I).height := by
  apply weightInitialIdeal_height_ge_card_of_pairedVariableIdeal_le
    (k := k) w I a b hdisj
  rw [pairedVariableIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hpair i

end DisjointPairs

/-! ## Height-comparison interface

The proposition below states the height comparison associated with a flat
weighted Rees family.  It is defined here without being assumed by any
theorem in this file.
-/

section HeightInterface

variable {k σ : Type*} [CommRing k]

/-- Height monotonicity from a weighted initial ideal to its source ideal. -/
def WeightInitialHeightMonotone : Prop :=
  ∀ (w : σ → ℕ) (I : Ideal (MvPolynomial σ k)),
    (weightInitialIdeal w I).height ≤ I.height

end HeightInterface

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart24

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_025/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_025.json"

section BundlePart25
/- Source: Papers/RigidityZheng_Algebra_LinearFormIdeal.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/LinearFormIdeal.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/





@[expose] public section

/-!
# Prime ideals generated by finite linear row systems

For a finite coordinate type, every ideal generated by homogeneous linear
forms over a field is prime.  The proof retains the actual row family:
it extends a basis of the row span to an ambient basis and constructs the
induced polynomial linear-change automorphism explicitly.  Under this
automorphism the row ideal is a coordinate-variable ideal.

No rank or primality statement is supplied as a premise.
-/

namespace RB31E2E

namespace LinearFormIdeal

noncomputable section

open MvPolynomial
open NullCellulePolynomial

variable {k I : Type*} [Field k] [Fintype I] [DecidableEq I]

/-- The homogeneous linear polynomial with coefficient vector `v`. -/
def linearPolynomial (v : I → k) : MvPolynomial I k :=
  ∑ i, C (v i) * X i

omit [DecidableEq I] in
@[simp] theorem linearPolynomial_zero :
    linearPolynomial (k := k) (I := I) 0 = 0 := by
  simp [linearPolynomial]

omit [DecidableEq I] in
theorem linearPolynomial_add (u v : I → k) :
    linearPolynomial (u + v) = linearPolynomial u + linearPolynomial v := by
  simp only [linearPolynomial, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

omit [DecidableEq I] in
theorem linearPolynomial_smul (a : k) (v : I → k) :
    linearPolynomial (a • v) = C a * linearPolynomial v := by
  simp only [linearPolynomial, Pi.smul_apply, smul_eq_mul, map_mul,
    Finset.mul_sum, mul_assoc]

/-- Linearization of `linearPolynomial`. -/
def linearPolynomialLinear : (I → k) →ₗ[k] MvPolynomial I k where
  toFun := linearPolynomial
  map_add' := linearPolynomial_add
  map_smul' a v := by
    rw [linearPolynomial_smul]
    simp [Algebra.smul_def]

omit [DecidableEq I] in
@[simp] theorem linearPolynomialLinear_apply (v : I → k) :
    linearPolynomialLinear v = linearPolynomial v := rfl

@[simp] theorem linearPolynomial_basisFun (i : I) :
    linearPolynomial ((Pi.basisFun k I) i) = X i := by
  rw [Pi.basisFun_apply]
  simp [linearPolynomial, Pi.single_apply]

/-- Polynomial substitution induced by an ambient linear equivalence. -/
def linearChangeHom (e : (I → k) ≃ₗ[k] (I → k)) :
    MvPolynomial I k →ₐ[k] MvPolynomial I k :=
  MvPolynomial.aeval (fun i ↦ linearPolynomial (e ((Pi.basisFun k I) i)))

@[simp] theorem linearChangeHom_X
    (e : (I → k) ≃ₗ[k] (I → k)) (i : I) :
    linearChangeHom e (X i) =
      linearPolynomial (e ((Pi.basisFun k I) i)) := by
  simp [linearChangeHom]

theorem linearChangeHom_linearPolynomial
    (e : (I → k) ≃ₗ[k] (I → k)) (v : I → k) :
    linearChangeHom e (linearPolynomial v) = linearPolynomial (e v) := by
  calc
    linearChangeHom e (linearPolynomial v) =
        ∑ i, C (v i) * linearPolynomial (e ((Pi.basisFun k I) i)) := by
      simp [linearPolynomial, linearChangeHom]
    _ = ∑ i, linearPolynomialLinear
        (v i • e ((Pi.basisFun k I) i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (linearPolynomial_smul (v i)
        (e ((Pi.basisFun k I) i))).symm
    _ = linearPolynomialLinear
        (∑ i, v i • e ((Pi.basisFun k I) i)) := by
      rw [map_sum]
    _ = linearPolynomial (e v) := by
      change linearPolynomial (∑ i, v i • e ((Pi.basisFun k I) i)) =
        linearPolynomial (e v)
      have he := congrArg e ((Pi.basisFun k I).sum_repr v)
      simp only [map_sum, map_smul] at he
      exact congrArg linearPolynomial he

/-- The explicit polynomial automorphism induced by a linear equivalence. -/
def linearChangeEquiv (e : (I → k) ≃ₗ[k] (I → k)) :
    MvPolynomial I k ≃ₐ[k] MvPolynomial I k := by
  apply AlgEquiv.ofAlgHom (linearChangeHom e) (linearChangeHom e.symm)
  · apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linearChangeHom_X,
      linearChangeHom_linearPolynomial, e.apply_symm_apply,
      linearPolynomial_basisFun]
    rfl
  · apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, linearChangeHom_X,
      linearChangeHom_linearPolynomial, e.symm_apply_apply,
      linearPolynomial_basisFun]
    rfl

@[simp] theorem linearChangeEquiv_linearPolynomial
    (e : (I → k) ≃ₗ[k] (I → k)) (v : I → k) :
    linearChangeEquiv e (linearPolynomial v) = linearPolynomial (e v) := by
  exact linearChangeHom_linearPolynomial e v

/-- The ideal generated by a labelled family of finite linear forms. -/
def linearFormIdeal {J : Type*} (row : J → I → k) :
    Ideal (MvPolynomial I k) :=
  Ideal.span (Set.range (fun j ↦ linearPolynomial (row j)))

/-- Coefficient vectors whose linear polynomials lie in an ideal. -/
def linearPolynomialPreimage
    (Q : Ideal (MvPolynomial I k)) : Submodule k (I → k) :=
  { carrier := {v | linearPolynomial v ∈ Q}
    zero_mem' := by simp
    add_mem' := by
      intro u v hu hv
      change linearPolynomial (u + v) ∈ Q
      rw [linearPolynomial_add]
      exact Q.add_mem hu hv
    smul_mem' := by
      intro a v hv
      change linearPolynomial (a • v) ∈ Q
      rw [linearPolynomial_smul]
      exact Q.mul_mem_left _ hv }

omit [DecidableEq I] in
theorem linearPolynomial_mem_linearFormIdeal_of_mem_span
    {J : Type*} (row : J → I → k) (v : I → k)
    (hv : v ∈ Submodule.span k (Set.range row)) :
    linearPolynomial v ∈ linearFormIdeal row := by
  let S := linearPolynomialPreimage (linearFormIdeal row)
  have hrange : Set.range row ⊆ (S : Set (I → k)) := by
    rintro _ ⟨j, rfl⟩
    change linearPolynomial (row j) ∈ linearFormIdeal row
    exact Ideal.subset_span ⟨j, rfl⟩
  exact Submodule.span_le.mpr hrange hv

omit [DecidableEq I] in
theorem linearFormIdeal_eq_basisIdeal
    {J : Type*} (row : J → I → k) :
    let W := Submodule.span k (Set.range row)
    let b := Module.finBasis k W
    linearFormIdeal row =
      Ideal.span (Set.range (fun i ↦ linearPolynomial (b i : I → k))) := by
  dsimp only
  let W := Submodule.span k (Set.range row)
  let b := Module.finBasis k W
  let Q : Ideal (MvPolynomial I k) :=
    Ideal.span (Set.range (fun i ↦ linearPolynomial (b i : I → k)))
  apply le_antisymm
  · rw [linearFormIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    let S := linearPolynomialPreimage Q
    have hb : Set.range (fun i ↦ (b i : I → k)) ⊆
        (S : Set (I → k)) := by
      rintro _ ⟨i, rfl⟩
      change linearPolynomial (b i : I → k) ∈ Q
      exact Ideal.subset_span ⟨i, rfl⟩
    have hW : W ≤ S := by
      intro x hx
      let xW : W := ⟨x, hx⟩
      have hrepr := b.sum_repr xW
      have hreprVal :
          ∑ i, (b.repr xW) i • (b i : I → k) = x := by
        calc
          ∑ i, (b.repr xW) i • (b i : I → k) =
              W.subtype (∑ i, (b.repr xW) i • b i) := by
            rw [map_sum]
            rfl
          _ = W.subtype xW := congrArg W.subtype hrepr
          _ = x := rfl
      rw [← hreprVal]
      apply S.sum_mem
      intro i _hi
      exact S.smul_mem _ (hb ⟨i, rfl⟩)
    have hj := hW (Submodule.subset_span ⟨j, rfl⟩)
    exact hj
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact linearPolynomial_mem_linearFormIdeal_of_mem_span row
      (b i : I → k) (b i).2

set_option backward.isDefEq.respectTransparency.types false in
/-- Every ideal generated by a finite-coordinate family of linear forms is
prime. -/
theorem linearFormIdeal_isPrime
    {J : Type*} (row : J → I → k) :
    (linearFormIdeal row).IsPrime := by
  classical
  let W := Submodule.span k (Set.range row)
  let r := Module.finrank k W
  let bW := Module.finBasis k W
  let family : Fin r → I → k := fun i ↦ (bW i : I → k)
  have hfamily : LinearIndependent k family := by
    exact bW.linearIndependent.map' W.subtype
      ((LinearMap.ker_eq_bot).2 W.subtype_injective)
  let bExt := Module.Basis.sumExtend hfamily
  let idx : (Fin r ⊕ Module.Basis.sumExtendIndex hfamily) ≃ I :=
    bExt.indexEquiv (Pi.basisFun k I)
  let bI : Module.Basis I k (I → k) := bExt.reindex idx
  let e : (I → k) ≃ₗ[k] (I → k) :=
    (Pi.basisFun k I).equiv bI (Equiv.refl I)
  let S : Set I := Set.range (fun i : Fin r ↦ idx (Sum.inl i))
  have he (i : Fin r) :
      e ((Pi.basisFun k I) (idx (Sum.inl i))) = family i := by
    dsimp [e]
    rw [Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply]
    dsimp [bI]
    rw [Module.Basis.reindex_apply]
    have hidx : idx.symm (idx (Sum.inl i)) = Sum.inl i :=
      idx.symm_apply_apply (Sum.inl i)
    rw [hidx]
    change (Module.Basis.sumExtend hfamily) (Sum.inl i) = family i
    rw [Module.Basis.sumExtend, Module.Basis.reindex_apply]
    exact Module.Basis.extend_apply_self _ _
  have hX (i : Fin r) :
      linearChangeEquiv e (X (idx (Sum.inl i))) =
        linearPolynomial (family i) := by
    change linearChangeHom e (X (idx (Sum.inl i))) = _
    rw [linearChangeHom_X, he]
  have hmap :
      Ideal.map (linearChangeEquiv e).toRingEquiv
          (coordinateVariableIdeal (k := k) S) =
        Ideal.span (Set.range (fun i ↦ linearPolynomial (family i))) := by
    rw [coordinateVariableIdeal, Ideal.map_span]
    congr 1
    ext q
    constructor
    · rintro ⟨x, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, (hX i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨X (idx (Sum.inl i)), ?_, ?_⟩
      · refine ⟨idx (Sum.inl i), ?_, rfl⟩
        exact ⟨i, rfl⟩
      · simpa using hX i
  letI : (coordinateVariableIdeal (k := k) S).IsPrime :=
    coordinateVariableIdeal_isPrime S
  have hprime : (Ideal.span (Set.range
      (fun i ↦ linearPolynomial (family i)))).IsPrime := by
    rw [← hmap]
    exact Ideal.map_isPrime_of_equiv (linearChangeEquiv e).toRingEquiv
  rw [linearFormIdeal_eq_basisIdeal row]
  simpa [W, bW, family] using hprime

end


end LinearFormIdeal

end RB31E2E


end
end BundlePart25

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_026/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_026.json"

section BundlePart26
/- Source: Papers/RigidityZheng_Algebra_LinearFormIdealHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/LinearFormIdealHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Height of a finite linear-form ideal

The explicit linear change of coordinates used to prove primality also
exhibits a prime chain of length equal to the row-space rank.  Only the
lower height bound needed by the selected-null argument is recorded here.
-/

namespace RB31E2E

namespace LinearFormIdeal

noncomputable section

open MvPolynomial
open NullCellulePolynomial

variable {k I : Type*} [Field k] [Fintype I] [DecidableEq I]

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite homogeneous linear row ideal has height at least the dimension
of its coefficient row span. -/
theorem finrank_span_le_linearFormIdeal_height
    {J : Type*} (row : J → I → k) :
    (Module.finrank k (Submodule.span k (Set.range row)) : ℕ∞) ≤
      (linearFormIdeal row).height := by
  classical
  let W := Submodule.span k (Set.range row)
  let r := Module.finrank k W
  let bW := Module.finBasis k W
  let family : Fin r → I → k := fun i ↦ (bW i : I → k)
  have hfamily : LinearIndependent k family := by
    exact bW.linearIndependent.map' W.subtype
      ((LinearMap.ker_eq_bot).2 W.subtype_injective)
  let bExt := Module.Basis.sumExtend hfamily
  let idx : (Fin r ⊕ Module.Basis.sumExtendIndex hfamily) ≃ I :=
    bExt.indexEquiv (Pi.basisFun k I)
  let bI : Module.Basis I k (I → k) := bExt.reindex idx
  let e : (I → k) ≃ₗ[k] (I → k) :=
    (Pi.basisFun k I).equiv bI (Equiv.refl I)
  let c : Fin r → I := fun i ↦ idx (Sum.inl i)
  have hc : Function.Injective c := by
    intro i j hij
    exact Sum.inl_injective (idx.injective hij)
  have he (i : Fin r) :
      e ((Pi.basisFun k I) (c i)) = family i := by
    dsimp [e, c]
    rw [Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply]
    dsimp [bI]
    rw [Module.Basis.reindex_apply]
    have hidx : idx.symm (idx (Sum.inl i)) = Sum.inl i :=
      idx.symm_apply_apply (Sum.inl i)
    rw [hidx]
    change (Module.Basis.sumExtend hfamily) (Sum.inl i) = family i
    rw [Module.Basis.sumExtend, Module.Basis.reindex_apply]
    exact Module.Basis.extend_apply_self _ _
  have hX (i : Fin r) :
      linearChangeEquiv e (X (c i)) =
        linearPolynomial (family i) := by
    change linearChangeHom e (X (c i)) = _
    rw [linearChangeHom_X, he]
  have hmap :
      Ideal.map (linearChangeEquiv e).toRingEquiv
          (coordinateVariableIdeal (k := k) (Set.range c)) =
        Ideal.span (Set.range
          (fun i ↦ linearPolynomial (family i))) := by
    rw [coordinateVariableIdeal, Ideal.map_span]
    congr 1
    ext q
    constructor
    · rintro ⟨x, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, (hX i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨X (c i), ?_, ?_⟩
      · exact ⟨c i, ⟨i, rfl⟩, rfl⟩
      · simpa using hX i
  have hcoord : (r : ℕ∞) ≤
      (coordinateVariableIdeal (k := k) (Set.range c)).height :=
    coordinateVariableIdeal_height_ge_card (k := k) c hc
  have hlinear : (r : ℕ∞) ≤
      (Ideal.span (Set.range
        (fun i ↦ linearPolynomial (family i)))).height := by
    rw [← hmap, (linearChangeEquiv e).toRingEquiv.height_map]
    exact hcoord
  rw [linearFormIdeal_eq_basisIdeal row]
  simpa [W, r, bW, family] using hlinear

end

end LinearFormIdeal

end RB31E2E


end
end BundlePart26

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_027/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_027.json"

section BundlePart27
/- Source: Papers/RigidityLinearIdealRank.lean -/





@[expose] public section

/-!
# A linear motion ideal has exactly the rank of its actual rows

The rank used here is the rank of the literal coefficient matrix.  This
bridge converts a lower codimension bound for its ordinary polynomial
ideal into a lower bound for the original linear constraints.
-/

namespace Papers.Rigidity.LinearIdealRank

noncomputable section

open RB31E2E.LinearFormIdeal
open MvPolynomial

variable {k I J : Type*} [Field k] [Fintype I] [DecidableEq I]

/-- No more than a basis of the row space is needed to generate the ideal.
Krull's height theorem therefore supplies the upper height bound. -/
theorem linearFormIdeal_height_le_finrank_span (row : J → I → k) :
    (linearFormIdeal row).height ≤
      (Module.finrank k (Submodule.span k (Set.range row)) : ℕ∞) := by
  classical
  let W := Submodule.span k (Set.range row)
  let b := Module.finBasis k W
  let f : Fin (Module.finrank k W) → MvPolynomial I k :=
    fun i => linearPolynomial (b i : I → k)
  let s : Finset (MvPolynomial I k) := Finset.univ.image f
  have hs : (s : Set (MvPolynomial I k)) = Set.range f := by
    ext q
    simp [s]
  have hI : linearFormIdeal row = Ideal.span (s : Set (MvPolynomial I k)) := by
    rw [hs]
    exact linearFormIdeal_eq_basisIdeal row
  have hnot : Ideal.span (s : Set (MvPolynomial I k)) ≠ ⊤ := by
    rw [← hI]
    exact (linearFormIdeal_isPrime row).ne_top
  have hheight := Ideal.height_span_le_card_of_span_ne_top hnot
  have hcard : s.card ≤ Module.finrank k W := by
    exact (Finset.card_image_le).trans_eq (by simp)
  rw [hI]
  exact hheight.trans (by exact_mod_cast hcard)

/-- The prime ideal of a homogeneous linear system has its literal row rank
as height, over every field. -/
theorem linearFormIdeal_height_eq_finrank_span (row : J → I → k) :
    (linearFormIdeal row).height =
      (Module.finrank k (Submodule.span k (Set.range row)) : ℕ∞) :=
  le_antisymm (linearFormIdeal_height_le_finrank_span row)
    (finrank_span_le_linearFormIdeal_height row)

theorem linearFormIdeal_height_eq_matrix_rank [Finite J]
    (A : Matrix J I k) :
    (linearFormIdeal A.row).height = (A.rank : ℕ∞) := by
  rw [linearFormIdeal_height_eq_finrank_span, Matrix.rank_eq_finrank_span_row]

/-- A height estimate for the genuine row ideal implies the same rank
estimate for the actual coefficient matrix, without a geometric premise. -/
theorem rank_ge_of_linearFormIdeal_height_ge [Finite J]
    (A : Matrix J I k) (r : ℕ)
    (h : (r : ℕ∞) ≤ (linearFormIdeal A.row).height) : r ≤ A.rank := by
  rw [linearFormIdeal_height_eq_matrix_rank] at h
  exact_mod_cast h

end

end Papers.Rigidity.LinearIdealRank

end
end BundlePart27

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_028/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_028.json"

section BundlePart28
/- Source: Papers/RigidityZheng_Algebra_HomogeneousPrimeChartHeight.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/HomogeneousPrimeChartHeight.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# Height loss on a homogeneous affine chart

Let `P` be a homogeneous prime in the standard-graded polynomial ring
`k[X₀, ..., Xₙ₋₁]`.  If one coordinate `X i` does not vanish modulo `P`,
then `P` is strictly below the irrelevant maximal ideal.  The latter has
height `n`, so `P` has height at most `n - 1`.

This is the algebraic end of the normalized-chart argument used by the
body--pin project.  The proof is elementary and keeps all provenance visible:

* homogeneity extracts the degree-zero component of every member of `P`;
* primality/properness over a field forces that constant component to vanish;
* hence `P` lies in the coordinate ideal generated by all variables;
* the omitted coordinate makes this inclusion strict;
* an explicit coordinate-prime chain and Krull's height theorem compute the
  height of that coordinate ideal.

The argument uses only homogeneity, primality, and an explicit coordinate
prime chain.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- The standard irrelevant ideal in a finite-variable polynomial ring,
written using the coordinate-ideal implementation from
`FilteredInitialHeight`. -/
def finiteIrrelevantIdeal (n : ℕ) :
    Ideal (MvPolynomial (Fin n) k) :=
  coordinateVariableIdeal (k := k) (Set.univ : Set (Fin n))

/-- The finite-variable irrelevant ideal is prime.  Its quotient is the
coefficient field. -/
theorem finiteIrrelevantIdeal_isPrime (n : ℕ) :
    (finiteIrrelevantIdeal (k := k) n).IsPrime := by
  exact coordinateVariableIdeal_isPrime
    (k := k) (Set.univ : Set (Fin n))

/-- The height of the irrelevant ideal in `n` variables is exactly `n`.

The lower bound is the explicit chain obtained by adjoining the variables
one at a time.  The upper bound uses that the ideal is generated by the `n`
coordinate variables. -/
theorem finiteIrrelevantIdeal_height (n : ℕ) :
    (finiteIrrelevantIdeal (k := k) n).height = (n : ℕ∞) := by
  let c : Fin n → Fin n := fun i ↦ i
  have hc : Function.Injective c := Function.injective_id
  have hlower :
      (n : ℕ∞) ≤ (finiteIrrelevantIdeal (k := k) n).height := by
    simpa [finiteIrrelevantIdeal, c] using
      (coordinateVariableIdeal_height_ge_card (k := k) c hc)
  have hspan :
      (finiteIrrelevantIdeal (k := k) n).spanFinrank ≤ n := by
    let g : Fin n → MvPolynomial (Fin n) k := fun i ↦ X i
    rw [finiteIrrelevantIdeal, coordinateVariableIdeal, Set.image_univ]
    change (Ideal.span (Set.range g)).spanFinrank ≤ n
    refine (Submodule.spanFinrank_span_le_ncard_of_finite
      (Set.finite_range g)).trans ?_
    rw [← Set.image_univ]
    simpa using Set.ncard_image_le (f := g) (s := Set.univ)
  have hne : finiteIrrelevantIdeal (k := k) n ≠ ⊤ :=
    (finiteIrrelevantIdeal_isPrime (k := k) n).ne_top
  apply le_antisymm
  · apply (Ideal.height_le_spanFinrank _ hne).trans
    exact_mod_cast hspan
  · exact hlower

/-- A proper standard-homogeneous ideal over a field is contained in the
irrelevant ideal.  The field hypothesis is used exactly once: a nonzero
constant is a unit and therefore cannot belong to a proper ideal. -/
theorem homogeneousIdeal_le_finiteIrrelevantIdeal
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k))
    (hPproper : P ≠ ⊤)
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k)) :
    P ≤ finiteIrrelevantIdeal (k := k) n := by
  intro f hf
  have hcomponent : homogeneousComponent 0 f ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply f 0]
    exact hPhom 0 hf
  have hconstant : C (f.coeff 0) ∈ P := by
    simpa using hcomponent
  have hcoeff : f.coeff 0 = 0 := by
    by_contra hne
    have hunit : IsUnit (C (f.coeff 0) : MvPolynomial (Fin n) k) :=
      (isUnit_iff_ne_zero.mpr hne).map C
    exact hPproper (P.eq_top_of_isUnit_mem hconstant hunit)
  rw [finiteIrrelevantIdeal, coordinateVariableIdeal,
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    intro hzero
    subst m
    exact (MvPolynomial.mem_support_iff.mp hm) hcoeff
  rw [Finsupp.ne_iff] at hm0
  obtain ⟨j, hj⟩ := hm0
  exact ⟨j, Set.mem_univ j, hj⟩

/-- Strict height loss on a nonvanishing homogeneous coordinate chart.

This `< n` form is often the most convenient one for dimension arguments. -/
theorem homogeneousPrime_height_lt_of_X_not_mem
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n) (hi : X i ∉ P) :
    P.height < (n : ℕ∞) := by
  have hle : P ≤ finiteIrrelevantIdeal (k := k) n :=
    homogeneousIdeal_le_finiteIrrelevantIdeal P
      Ideal.IsPrime.ne_top' hPhom
  have hXi : X i ∈ finiteIrrelevantIdeal (k := k) n := by
    exact (X_mem_coordinateVariableIdeal_iff
      (k := k) (Set.univ : Set (Fin n)) i).2 (Set.mem_univ i)
  have hlt : P < finiteIrrelevantIdeal (k := k) n := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hi
    rw [heq]
    exact hXi
  rw [← finiteIrrelevantIdeal_height (k := k) n]
  exact Ideal.height_strict_mono_of_isPrime hlt

/-- A homogeneous prime missing one coordinate has height at most `n - 1`.
This is the exact affine-chart bound: normalizing a nonvanishing homogeneous
coordinate removes one dimension from the possible prime height. -/
theorem homogeneousPrime_height_le_pred_of_X_not_mem
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n) (hi : X i ∉ P) :
    P.height ≤ ((n - 1 : ℕ) : ℕ∞) := by
  have hlt := homogeneousPrime_height_lt_of_X_not_mem
    (k := k) P hPhom i hi
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hre : (n : ℕ∞) = ((n - 1 : ℕ) : ℕ∞) + 1 := by
    norm_cast
    omega
  rw [hre, ENat.lt_add_one_iff (ENat.coe_ne_top (n - 1))] at hlt
  exact hlt

/-- Equivalent irrelevant-ideal formulation: if a homogeneous prime has
height at least the number of ambient variables, then every coordinate
variable belongs to it. -/
theorem all_X_mem_homogeneousPrime_of_card_le_height
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (hheight : (n : ℕ∞) ≤ P.height) :
    ∀ i : Fin n, X i ∈ P := by
  intro i
  by_contra hi
  exact (not_lt_of_ge hheight)
    (homogeneousPrime_height_lt_of_X_not_mem
      (k := k) P hPhom i hi)

/-- A homogeneous prime of height at least `n` is the irrelevant maximal
ideal itself.  This packages both the height obstruction and its full
coordinate provenance. -/
theorem homogeneousPrime_eq_finiteIrrelevantIdeal_of_card_le_height
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (hheight : (n : ℕ∞) ≤ P.height) :
    P = finiteIrrelevantIdeal (k := k) n := by
  apply le_antisymm
  · exact homogeneousIdeal_le_finiteIrrelevantIdeal P
      Ideal.IsPrime.ne_top' hPhom
  · rw [finiteIrrelevantIdeal, coordinateVariableIdeal, Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact all_X_mem_homogeneousPrime_of_card_le_height
      (k := k) P hPhom hheight i

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart28

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_029/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_029.json"

section BundlePart29
/- Source: Papers/RigidityZheng_Algebra_HomogeneousChartContradiction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/HomogeneousChartContradiction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/




@[expose] public section

/-!
# The homogeneous-chart contradiction

This file closes the abstract elimination step at the end of a normalized
homogeneous chart.  Let `J` be a homogeneous ideal in a polynomial ring in
`n` variables and fix a coordinate `X i`.  Suppose that every homogeneous
prime over `J` which misses `X i` has height at least `n`.

There can then be no (even nonhomogeneous) prime over `J` which misses
`X i`.  Indeed, the homogeneous core of such a prime is again prime, still
contains `J`, and still misses `X i`; the height lower bound contradicts the
strict chart-height bound proved in `HomogeneousPrimeChartHeight`.

Prime existence disjoint from the powers of `X i` then gives the concrete
elimination certificate `X i ^ m ∈ J` for some `m`.  Consequently every
algebra chart in which `X i` becomes a unit sends `J` to the top ideal.

No incidence-specific dimension or null-cellule height assertion enters
this argument.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- If every homogeneous prime over `J` and avoiding `X i` has height at
least the number of variables, then no prime over `J` can avoid `X i`.

The input prime is not assumed homogeneous.  Passing to its homogeneous
core is what retains the homogeneous provenance of `J` while making the
chart-height theorem applicable. -/
theorem not_exists_prime_over_avoiding_X_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ¬ ∃ P : Ideal (MvPolynomial (Fin n) k),
      P.IsPrime ∧ J ≤ P ∧ X i ∉ P := by
  rintro ⟨P, hPprime, hJP, hiP⟩
  let Q : Ideal (MvPolynomial (Fin n) k) :=
    (P.homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin n) k)).toIdeal
  have hQprime : Q.IsPrime := by
    dsimp [Q]
    exact hPprime.homogeneousCore
  letI : Q.IsPrime := hQprime
  have hQhom : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k) := by
    dsimp [Q]
    exact HomogeneousIdeal.isHomogeneous _
  have hJQ : J ≤ Q := by
    dsimp [Q]
    exact hJhom.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono _ hJP)
  have hiQ : X i ∉ Q := by
    intro hi
    apply hiP
    exact P.toIdeal_homogeneousCore_le _ hi
  exact (not_lt_of_ge (hheight Q hQprime hQhom hJQ hiQ))
    (homogeneousPrime_height_lt_of_X_not_mem
      (k := k) Q hQhom i hiQ)

/-- Under the same chart-height hypothesis, some power of the selected
coordinate belongs to `J`.  This is the concrete finite certificate that
the principal open chart `D(X i)` has empty intersection with `V(J)`. -/
theorem exists_X_pow_mem_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ∃ m : ℕ, X i ^ m ∈ J := by
  by_contra hpow
  have hnoPow : ∀ m : ℕ, X i ^ m ∉ J := by
    intro m hm
    exact hpow ⟨m, hm⟩
  have hdisjoint :
      Disjoint (J : Set (MvPolynomial (Fin n) k))
        (Submonoid.powers (X i : MvPolynomial (Fin n) k) :
          Set (MvPolynomial (Fin n) k)) := by
    rw [Set.disjoint_left]
    intro f hfJ hfPow
    change f ∈ Submonoid.powers
      (X i : MvPolynomial (Fin n) k) at hfPow
    rw [Submonoid.mem_powers_iff] at hfPow
    obtain ⟨m, rfl⟩ := hfPow
    exact hnoPow m hfJ
  obtain ⟨P, hPprime, hJP, hPdisjoint⟩ :=
    J.exists_le_prime_disjoint
      (Submonoid.powers (X i : MvPolynomial (Fin n) k)) hdisjoint
  have hiP : X i ∉ P := by
    intro hi
    exact Set.disjoint_left.mp hPdisjoint hi
      (Submonoid.mem_powers (X i : MvPolynomial (Fin n) k))
  exact
    (not_exists_prime_over_avoiding_X_of_homogeneousPrime_height
      (k := k) J hJhom i hheight) ⟨P, hPprime, hJP, hiP⟩

/-- Radical form of the same elimination conclusion. -/
theorem X_mem_radical_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height) :
    X i ∈ J.radical := by
  rw [Ideal.mem_radical_iff]
  exact exists_X_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom i hheight

/-- Any target algebra in which the chosen coordinate is a unit sees `J`
as the unit ideal.  In particular this applies to localization away from
`X i`, without coupling the theorem to a particular localization model. -/
theorem map_eq_top_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (i : Fin n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → X i ∉ Q → (n : ℕ∞) ≤ Q.height)
    {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin n) k) S]
    (hunit : IsUnit
      (algebraMap (MvPolynomial (Fin n) k) S (X i))) :
    Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J = ⊤ := by
  obtain ⟨m, hm⟩ := exists_X_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom i hheight
  have hmapped :
      algebraMap (MvPolynomial (Fin n) k) S (X i ^ m) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J :=
    Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) k) S) hm
  have hmappedUnit :
      IsUnit (algebraMap (MvPolynomial (Fin n) k) S (X i ^ m)) := by
    rw [map_pow]
    exact hunit.pow m
  exact (Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J).eq_top_of_isUnit_mem
    hmapped hmappedUnit

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart29

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_030/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_030.json"

section BundlePart30
/- Source: Papers/RigidityZheng_Algebra_HomogeneousDenominatorContradiction.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/Algebra/HomogeneousDenominatorContradiction.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/


@[expose] public section

/-!
# Homogeneous contradiction on a provenance denominator

The one-coordinate chart theorem is too narrow for a distinctness chart:
excluding every unwanted equality component requires a finite product of
provenance-labelled twist differences.  This file replaces `X i` by an
arbitrary polynomial `s` in the irrelevant ideal.

If a homogeneous prime avoids `s`, then it is strictly below the irrelevant
ideal, because `s` belongs to the latter.  Hence its height is strictly less
than the number of twist variables.  The same homogeneous-core and prime-
avoidance argument as for a single coordinate then produces a concrete
receipt `s ^ m ∈ J`.

No assertion about which incidence denominator has the required height is
made here.  This is only the reusable commutative-algebra mechanism needed
once a provenance chart supplies that height.
-/

namespace RB31E2E

namespace NullCellulePolynomial

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- A homogeneous prime avoiding any specified member of the irrelevant
ideal has height strictly below the number of ambient variables. -/
theorem homogeneousPrime_height_lt_of_irrelevant_mem_not_mem
    {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hsP : s ∉ P) :
    P.height < (n : ℕ∞) := by
  have hle : P ≤ finiteIrrelevantIdeal (k := k) n :=
    homogeneousIdeal_le_finiteIrrelevantIdeal P
      Ideal.IsPrime.ne_top' hPhom
  have hlt : P < finiteIrrelevantIdeal (k := k) n := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hsP
    rw [heq]
    exact hsIrrelevant
  rw [← finiteIrrelevantIdeal_height (k := k) n]
  exact Ideal.height_strict_mono_of_isPrime hlt

/-- If every homogeneous prime over `J` that avoids a provenance
denominator has full ambient height, then no prime over `J` can avoid that
denominator. -/
theorem not_exists_prime_over_avoiding_denominator_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ¬ ∃ P : Ideal (MvPolynomial (Fin n) k),
      P.IsPrime ∧ J ≤ P ∧ s ∉ P := by
  rintro ⟨P, hPprime, hJP, hsP⟩
  let Q : Ideal (MvPolynomial (Fin n) k) :=
    (P.homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin n) k)).toIdeal
  have hQprime : Q.IsPrime := by
    dsimp [Q]
    exact hPprime.homogeneousCore
  letI : Q.IsPrime := hQprime
  have hQhom : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k) := by
    dsimp [Q]
    exact HomogeneousIdeal.isHomogeneous _
  have hJQ : J ≤ Q := by
    dsimp [Q]
    exact hJhom.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono _ hJP)
  have hsQ : s ∉ Q := by
    intro hs
    apply hsP
    exact P.toIdeal_homogeneousCore_le _ hs
  exact (not_lt_of_ge (hheight Q hQprime hQhom hJQ hsQ))
    (homogeneousPrime_height_lt_of_irrelevant_mem_not_mem
      (k := k) Q hQhom s hsIrrelevant hsQ)

/-- The full-height condition on the principal provenance chart gives a
finite saturation receipt in the original homogeneous ideal. -/
theorem exists_denominator_pow_mem_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    ∃ m : ℕ, s ^ m ∈ J := by
  by_contra hpow
  have hnoPow : ∀ m : ℕ, s ^ m ∉ J := by
    intro m hm
    exact hpow ⟨m, hm⟩
  have hdisjoint :
      Disjoint (J : Set (MvPolynomial (Fin n) k))
        (Submonoid.powers s : Set (MvPolynomial (Fin n) k)) := by
    rw [Set.disjoint_left]
    intro f hfJ hfPow
    change f ∈ Submonoid.powers s at hfPow
    rw [Submonoid.mem_powers_iff] at hfPow
    obtain ⟨m, rfl⟩ := hfPow
    exact hnoPow m hfJ
  obtain ⟨P, hPprime, hJP, hPdisjoint⟩ :=
    J.exists_le_prime_disjoint (Submonoid.powers s) hdisjoint
  have hsP : s ∉ P := by
    intro hs
    exact Set.disjoint_left.mp hPdisjoint hs
      (Submonoid.mem_powers s)
  exact
    (not_exists_prime_over_avoiding_denominator_of_homogeneousPrime_height
      (k := k) J hJhom s hsIrrelevant hheight)
      ⟨P, hPprime, hJP, hsP⟩

/-- Radical form of the provenance-denominator receipt. -/
theorem denominator_mem_radical_of_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height) :
    s ∈ J.radical := by
  rw [Ideal.mem_radical_iff]
  exact exists_denominator_pow_mem_of_homogeneousPrime_height
    (k := k) J hJhom s hsIrrelevant hheight

/-- Every algebra in which the provenance denominator becomes a unit sees
the homogeneous chart ideal as the unit ideal. -/
theorem map_eq_top_of_denominator_homogeneousPrime_height
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k))
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (s : MvPolynomial (Fin n) k)
    (hsIrrelevant : s ∈ finiteIrrelevantIdeal (k := k) n)
    (hheight :
      ∀ (Q : Ideal (MvPolynomial (Fin n) k)),
        Q.IsPrime →
        Q.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin n) k) →
        J ≤ Q → s ∉ Q → (n : ℕ∞) ≤ Q.height)
    {S : Type*} [CommRing S]
    [Algebra (MvPolynomial (Fin n) k) S]
    (hunit : IsUnit
      (algebraMap (MvPolynomial (Fin n) k) S s)) :
    Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J = ⊤ := by
  obtain ⟨m, hm⟩ :=
    exists_denominator_pow_mem_of_homogeneousPrime_height
      (k := k) J hJhom s hsIrrelevant hheight
  have hmapped :
      algebraMap (MvPolynomial (Fin n) k) S (s ^ m) ∈
        Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J :=
    Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) k) S) hm
  have hmappedUnit :
      IsUnit (algebraMap (MvPolynomial (Fin n) k) S (s ^ m)) := by
    rw [map_pow]
    exact hunit.pow m
  exact (Ideal.map (algebraMap (MvPolynomial (Fin n) k) S) J).eq_top_of_isUnit_mem
    hmapped hmappedUnit

end

end NullCellulePolynomial

end RB31E2E


end
end BundlePart30

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_031/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_031.json"

section BundlePart31
/- Source: Papers/RigidityZheng_NullCellule_GroundScale.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Adapted from RB31EndToEnd/NullCellule/GroundScale.lean.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
Only module visibility and import paths are changed at initial staging.
-/



@[expose] public section

/-!
# Grounding and the free common-scaling orbit

This file proves the point-set content of the one-dimensional orbit drop.
The later algebraic-geometric layer still has to convert this free orbit into
a dimension inequality; that conversion is deliberately not postulated here.
-/

namespace RB31E2E

variable {k V W E : Type*} [Field k]

/-- Scaling every twist by the same scalar preserves all pin equations. -/
theorem IsTwistMotion.smul {src dst : E → W} {p : E → Vec3 k}
    {X : W → Twist k} (hX : IsTwistMotion src dst p X) (a : k) :
    IsTwistMotion src dst p (fun w ↦ a • X w) := by
  intro e
  have he := congrArg (fun z : Vec3 k ↦ a • z) (hX e)
  simpa [Twist.eval, Vec3.cross_smul_left] using he

/-- A nonzero common scalar preserves and reflects equality of two labels. -/
theorem smul_twist_eq_smul_twist_iff {a : k} (ha : a ≠ 0)
    (X Y : Twist k) : a • X = a • Y ↔ X = Y := by
  constructor
  · intro hXY
    have hzero : a • (X - Y) = 0 := by
      rw [smul_sub, hXY, sub_self]
    have : X - Y = 0 := by
      rcases smul_eq_zero.mp hzero with h | h
      · exact (ha h).elim
      · exact h
    exact sub_eq_zero.mp this
  · rintro rfl
    rfl

/-- Hence a nonzero common scalar preserves the exact equality partition. -/
theorem commonScale_eq_iff {a : k} (ha : a ≠ 0) (X : V → Twist k) (u v : V) :
    a • X u = a • X v ↔ X u = X v :=
  smul_twist_eq_smul_twist_iff ha _ _

/-- Grounding is stable under common scaling. -/
theorem commonScale_grounded {root : V} {X : V → Twist k}
    (hroot : X root = 0) (a : k) :
    (fun v ↦ a • X v) root = 0 := by
  simp [hroot]

/-- On a nonzero assignment, the scalar parameter itself is recoverable.
This is the algebraic freeness statement behind the `G_m` orbit. -/
theorem commonScale_injective_of_ne_zero {X : V → Twist k} (hX : X ≠ 0) :
    Function.Injective (fun a : k ↦ (a • X : V → Twist k)) := by
  intro a b hab
  have hzero : (a - b) • X = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hab
  have habScalar : a - b = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact (hX h).elim
  exact sub_eq_zero.mp habScalar

/-- The multiplicative-group action is free on every nonzero assignment. -/
theorem units_commonScale_injective_of_ne_zero {X : V → Twist k} (hX : X ≠ 0) :
    Function.Injective (fun a : kˣ ↦ ((a : k) • X : V → Twist k)) := by
  intro a b hab
  apply Units.ext
  exact commonScale_injective_of_ne_zero hX hab

/-- A grounded assignment with at least two distinct labels is nonzero. -/
theorem ne_zero_of_grounded_of_ne {root v : V} {X : V → Twist k}
    (hroot : X root = 0) (hne : X v ≠ X root) : X ≠ 0 := by
  have hv : X v ≠ 0 := by
    simpa [hroot] using hne
  intro hX
  apply hv
  rw [hX]
  rfl

/-- Combined form used by the fixed-partition incidence stratum: after
grounding, any genuinely distinct block value has a free common-scaling
orbit, and every point of that orbit satisfies the same pin equations. -/
theorem grounded_scale_orbit_free_and_motion
    {src dst : E → W} {p : E → Vec3 k} {X : W → Twist k}
    {root v : W} (hMotion : IsTwistMotion src dst p X)
    (hroot : X root = 0) (hne : X v ≠ X root) :
    Function.Injective (fun a : kˣ ↦ ((a : k) • X : W → Twist k)) ∧
      ∀ a : kˣ, IsTwistMotion src dst p (fun w ↦ (a : k) • X w) := by
  have hX : X ≠ 0 := ne_zero_of_grounded_of_ne hroot hne
  exact ⟨units_commonScale_injective_of_ne_zero hX,
    fun a ↦ hMotion.smul (a : k)⟩

end RB31E2E


end
end BundlePart31

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_032/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_032.json"

section BundlePart32
/- Source: Papers/RigidityZheng_Incidence_SparseNullCore.lean -/

/- Copyright 2026 Dongzhe (Denzel) Zheng. Apache-2.0.
Extracted without changing statements or proofs from
RB31EndToEnd/Incidence/SmallBundleCertificate.lean, initial incidence section.
Source commit e457fde9100c9b7226bd4d81af6860f210a531ab
https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture
The later zero-defect body-pin assembly remains in SmallBundleCertificate.
-/






@[expose] public section

/-! # Literal sparse-null incidence semantics and explicit coordinate charts -/

namespace RB31E2E

namespace SparseNullIncidence

noncomputable section

 /-- Point-set incidence semantics used by the elimination statement.  The
vertex twists must be pairwise distinct, and every selected occurrence is a
zero of its nonzero relative twist. -/
def IsIncidenceRealization {V E : Type*} [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (p : E → Vec3 ℝ) (Y : V → Twist ℝ) : Prop :=
  Function.Injective Y ∧
    ∀ e : active,
      Twist.eval (Y (src e.1) - Y (dst e.1)) (p e.1) = 0

/-! ## Explicit finite charts for the incidence fibres -/

/-- Ground at `root` and then apply one common scalar.  Pin equations depend
only on differences, so this is the point-set representative used by the
finite normalization charts. -/
def groundAndScale {k V : Type*} [Field k]
    (Y : V → Twist k) (root : V) (a : k) : V → Twist k :=
  fun v ↦ a • (Y v - Y root)

@[simp]
theorem groundAndScale_root {k V : Type*} [Field k]
    (Y : V → Twist k) (root : V) (a : k) :
    groundAndScale Y root a root = 0 := by
  simp [groundAndScale]

/-- Grounding and nonzero common scaling preserve the exact distinct
incidence realization, with the same provenance-labelled pin placement. -/
theorem IsIncidenceRealization.groundAndScale
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (root : V) {a : ℝ} (ha : a ≠ 0) :
    IsIncidenceRealization src dst active p
      (SparseNullIncidence.groundAndScale Y root a) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    apply hY.1
    have huv' : Y u - Y root = Y v - Y root :=
      (smul_twist_eq_smul_twist_iff ha _ _).mp huv
    have := congrArg (fun Z : Twist ℝ ↦ Z + Y root) huv'
    simpa only [sub_add_cancel] using this
  · intro e
    have he := congrArg (fun z : Vec3 ℝ ↦ a • z) (hY.2 e)
    have hdiff :
        SparseNullIncidence.groundAndScale Y root a (src e.1) -
            SparseNullIncidence.groundAndScale Y root a (dst e.1) =
          a • (Y (src e.1) - Y (dst e.1)) := by
      simp only [SparseNullIncidence.groundAndScale]
      module
    rw [hdiff]
    simpa [Twist.eval, Vec3.cross_smul_left] using he

/-- One of the six provenance coordinates detects every nonzero twist. -/
theorem exists_twistCoordinate_ne_zero {k : Type*} [Field k]
    {Z : Twist k} (hZ : Z ≠ 0) :
    ∃ c : GroundedTwistPolynomial.TwistCoordinate,
      GroundedTwistPolynomial.twistCoordinates Z c ≠ 0 := by
  by_contra h
  push Not at h
  apply hZ
  apply GroundedTwistPolynomial.twistCoordinates.injective
  funext c
  simpa using h c

/-- A chosen nonzero grounded coordinate can be normalized to `1`.  Together
with `groundAndScale`, this replaces the free common `G_m` orbit by finitely
many explicit affine charts. -/
theorem exists_grounded_normalization_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    {root other : V} (hne : other ≠ root) :
    ∃ c : GroundedTwistPolynomial.TwistCoordinate, ∃ a : ℝ,
      a ≠ 0 ∧
      GroundedTwistPolynomial.twistCoordinates
          (groundAndScale Y root a other) c = 1 ∧
      IsIncidenceRealization src dst active p
        (groundAndScale Y root a) := by
  have hDifference : Y other - Y root ≠ 0 := by
    exact sub_ne_zero.mpr (hY.1.ne hne)
  obtain ⟨c, hc⟩ := exists_twistCoordinate_ne_zero hDifference
  let z : ℝ := GroundedTwistPolynomial.twistCoordinates
    (Y other - Y root) c
  refine ⟨c, z⁻¹, inv_ne_zero hc, ?_, hY.groundAndScale root (inv_ne_zero hc)⟩
  change GroundedTwistPolynomial.twistCoordinates
      (z⁻¹ • (Y other - Y root)) c = 1
  rw [map_smul]
  change z⁻¹ * z = 1
  exact inv_mul_cancel₀ hc

/-- The stationary pin written in the angular-coordinate chart `i`.  The
coordinate `c` is free; the other two coordinates are rational expressions
in the relative twist and `c`. -/
def stationaryPinChart {k : Type*} [Field k]
    (Z : Twist k) (i : Fin 3) (c : k) : Vec3 k :=
  if _hi₀ : i = 0 then
    ![c,
      (Z.1 1 * c - Z.2 2) / Z.1 0,
      (Z.2 1 + Z.1 2 * c) / Z.1 0]
  else if _hi₁ : i = 1 then
    ![(Z.2 2 + Z.1 0 * c) / Z.1 1,
      c,
      (Z.1 2 * c - Z.2 0) / Z.1 1]
  else
    ![(Z.1 0 * c - Z.2 1) / Z.1 2,
      (Z.2 0 + Z.1 1 * c) / Z.1 2,
      c]

/-- Exact one-free-parameter formula for a stationary pin on an angular
coordinate chart.  This formula supplies the field-generation step for the
universal coordinate ring. -/
theorem eq_stationaryPinChart_of_eval_eq_zero
    {k : Type*} [Field k] (Z : Twist k) (p : Vec3 k)
    (i : Fin 3) (hi : Z.1 i ≠ 0) (hp : Twist.eval Z p = 0) :
    p = stationaryPinChart Z i (p i) := by
  have h₀ := congrFun hp (0 : Fin 3)
  have h₁ := congrFun hp (1 : Fin 3)
  have h₂ := congrFun hp (2 : Fin 3)
  simp [Twist.eval, Vec3.cross] at h₀ h₁ h₂
  fin_cases i
  · change Z.1 0 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₂
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₁
  · change Z.1 1 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₂
    · simp [stationaryPinChart]
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₀
  · change Z.1 2 ≠ 0 at hi
    funext j
    fin_cases j
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination h₁
    · simp [stationaryPinChart]
      apply (eq_div_iff hi).2
      linear_combination -h₀
    · simp [stationaryPinChart]

/-- The finite generating set for one angular pin chart: the six relative
twist coordinates and the single free pin coordinate. -/
def pinChartGeneratorSet (Z : Twist ℝ) (p : Vec3 ℝ) (i : Fin 3) : Set ℝ :=
  Set.range (GroundedTwistPolynomial.twistCoordinates Z) ∪ {p i}

/-- Field-generation form of `eq_stationaryPinChart_of_eval_eq_zero`.
Every pin coordinate lies in the field generated over `ℚ` by the six
relative-twist coordinates and one free pin coordinate.  This is the exact
input required for a transcendence-degree count on a universal chart; it is
strictly stronger than a pointwise dimension slogan. -/
theorem pinCoordinate_mem_adjoin_of_eval_eq_zero
    (Z : Twist ℝ) (p : Vec3 ℝ) (i j : Fin 3)
    (hi : Z.1 i ≠ 0) (hp : Twist.eval Z p = 0) :
    p j ∈ IntermediateField.adjoin ℚ (pinChartGeneratorSet Z p i) := by
  let K : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ (pinChartGeneratorSet Z p i)
  have hAngular (r : Fin 3) : Z.1 r ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inl ⟨⟨false, r⟩, rfl⟩
  have hTranslational (r : Fin 3) : Z.2 r ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inl ⟨⟨true, r⟩, rfl⟩
  have hFree : p i ∈ K := by
    apply IntermediateField.subset_adjoin
    exact Or.inr (Set.mem_singleton _)
  have hEq := eq_stationaryPinChart_of_eval_eq_zero Z p i hi hp
  rw [hEq]
  fin_cases i <;> fin_cases j
  all_goals simp [stationaryPinChart]
  all_goals first
    | exact hFree
    | exact K.div_mem
        (K.sub_mem (hAngular _) (hTranslational _)) (hAngular _)
    | exact K.div_mem
        (K.add_mem (hTranslational _) (K.mul_mem (hAngular _) hFree))
        (hAngular _)
    | exact K.div_mem
        (K.sub_mem (K.mul_mem (hAngular _) hFree) (hTranslational _))
        (hAngular _)

/-- Every selected incidence occurrence belongs to one of the three angular
charts, and its whole pin position is generated by the relative twist and
one retained pin coordinate. -/
theorem IsIncidenceRealization.exists_angular_pin_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 ∧
      p e.1 = stationaryPinChart
        (Y (src e.1) - Y (dst e.1)) i (p e.1 i) := by
  let Z : Twist ℝ := Y (src e.1) - Y (dst e.1)
  have hZ : Z ≠ 0 := sub_ne_zero.mpr (hY.1.ne (hLoop e.1 e.2))
  have hAngular : Z.1 ≠ 0 :=
    Twist.angular_ne_zero_of_ne_zero_of_eval_eq_zero Z (p e.1) hZ (hY.2 e)
  have hi : ∃ i : Fin 3, Z.1 i ≠ 0 := by
    by_contra h
    push Not at h
    apply hAngular
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, hi,
    eq_stationaryPinChart_of_eval_eq_zero Z (p e.1) i hi (hY.2 e)⟩

/-- Field-generation packet for one selected occurrence.  The angular chart
is chosen from the actual nonzero relative twist, and all three pin
coordinates then lie in the field generated by that twist and one free pin
coordinate. -/
theorem IsIncidenceRealization.exists_angular_pin_generation_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) :
    ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 ∧
      ∀ j : Fin 3,
        p e.1 j ∈ IntermediateField.adjoin ℚ
          (pinChartGeneratorSet
            (Y (src e.1) - Y (dst e.1)) (p e.1) i) := by
  obtain ⟨i, hi, _⟩ := hY.exists_angular_pin_chart hLoop e
  refine ⟨i, hi, ?_⟩
  intro j
  exact pinCoordinate_mem_adjoin_of_eval_eq_zero
    (Y (src e.1) - Y (dst e.1)) (p e.1) i j hi (hY.2 e)

/-- Global generators after choosing one angular chart per active
occurrence: all twist coordinates, one free coordinate for each active pin,
and all three coordinates of every inactive pin. -/
def incidenceChartGeneratorSet {V E : Type*} [DecidableEq E]
    (Y : V → Twist ℝ) (p : E → Vec3 ℝ) (active : Finset E)
    (chart : active → Fin 3) : Set ℝ :=
  Set.range (fun vc : V × GroundedTwistPolynomial.TwistCoordinate ↦
      GroundedTwistPolynomial.twistCoordinates (Y vc.1) vc.2) ∪
    Set.range (fun e : active ↦ p e.1 (chart e)) ∪
    Set.range (fun ej : {e : E // e ∉ active} × Fin 3 ↦
      p ej.1.1 ej.2)

/-- Simultaneous field-generation theorem for an entire incidence
realization.  This is the rigorous point-set/field bridge behind the count
"one free coordinate per crossing pin, three per inactive pin".  It still
does not infer a uniform eliminated polynomial; that final passage belongs
to the universal coordinate algebra in `PropernessPrinciple`. -/
theorem IsIncidenceRealization.exists_global_generation_chart
    {V E : Type*} [DecidableEq E]
    {src dst : E → V} {active : Finset E}
    {p : E → Vec3 ℝ} {Y : V → Twist ℝ}
    (hY : IsIncidenceRealization src dst active p Y)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) :
    ∃ chart : active → Fin 3,
      (∀ e : active,
        (Y (src e.1) - Y (dst e.1)).1 (chart e) ≠ 0) ∧
      ∀ (e : E) (j : Fin 3),
        p e j ∈ IntermediateField.adjoin ℚ
          (incidenceChartGeneratorSet Y p active chart) := by
  have hChart : ∀ e : active, ∃ i : Fin 3,
      (Y (src e.1) - Y (dst e.1)).1 i ≠ 0 := by
    intro e
    obtain ⟨i, hi, _⟩ := hY.exists_angular_pin_chart hLoop e
    exact ⟨i, hi⟩
  choose chart hchart using hChart
  refine ⟨chart, hchart, ?_⟩
  intro e j
  let K : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ
      (incidenceChartGeneratorSet Y p active chart)
  by_cases he : e ∈ active
  · let e' : active := ⟨e, he⟩
    let Z : Twist ℝ := Y (src e) - Y (dst e)
    have hSmallLe :
        IntermediateField.adjoin ℚ
            (pinChartGeneratorSet Z (p e) (chart e')) ≤ K := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨c, rfl⟩ := hx
        rcases c with ⟨b, r⟩
        have hSrc :
            GroundedTwistPolynomial.twistCoordinates (Y (src e)) ⟨b, r⟩ ∈ K := by
          apply IntermediateField.subset_adjoin
          exact Or.inl (Or.inl ⟨⟨src e, ⟨b, r⟩⟩, rfl⟩)
        have hDst :
            GroundedTwistPolynomial.twistCoordinates (Y (dst e)) ⟨b, r⟩ ∈ K := by
          apply IntermediateField.subset_adjoin
          exact Or.inl (Or.inl ⟨⟨dst e, ⟨b, r⟩⟩, rfl⟩)
        simpa [Z] using K.sub_mem hSrc hDst
      · have hx' : x = p e (chart e') := by simpa using hx
        subst x
        apply IntermediateField.subset_adjoin
        exact Or.inl (Or.inr ⟨e', rfl⟩)
    apply hSmallLe
    exact pinCoordinate_mem_adjoin_of_eval_eq_zero
      Z (p e) (chart e') j (hchart e') (hY.2 e')
  · apply IntermediateField.subset_adjoin
    exact Or.inr ⟨⟨⟨e, he⟩, j⟩, rfl⟩

/-- An occurrence selected by `active` determines a genuine simple edge.
The membership proof is retained so that the non-loop hypothesis is applied
to the exact occurrence used by the incidence equation. -/
def activeEdge {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src dst : E → V) (active : Finset E)
    (hLoop : ∀ e ∈ active, src e ≠ dst e) (e : active) : SimpleEdge V :=
  ⟨s(src e.1, dst e.1), by
    rw [Sym2.mk_isDiag_iff]
    exact hLoop e.1 e.2⟩

/--
For any finite provenance-labelled occurrence system, a sparse null
skeleton of the exact dimension-budget cardinality forces the image of the
distinct incidence locus to lie in a proper integer hypersurface of the pin
coordinate space.  Inactive occurrences are deliberately retained in the
ambient polynomial ring; the resulting polynomial may ignore them, but its
nonvanishing is asserted in the full provenance-labelled ring.

This proposition contains no body--pin graph, partition, or rigidity
predicate.
-/
def PropernessPrinciple : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E]
      (src dst : E → V) (active : Finset E)
      (hLoop : ∀ e ∈ active, src e ≠ dst e)
      (F : SimpleEdgeSet V),
    2 ≤ Fintype.card V →
    Sparse22 F →
    (∀ f ∈ F, ∃ e : active,
      activeEdge src dst active hLoop e = f) →
    F.card = 6 * (Fintype.card V - 1) - 2 * active.card →
    ∃ Q : MvPolynomial (GroundedTwistPolynomial.PinVariable E) ℤ,
      Q ≠ 0 ∧
      ∀ (p : E → Vec3 ℝ) (Y : V → Twist ℝ),
        IsIncidenceRealization src dst active p Y →
        MvPolynomial.eval₂ (Int.castRingHom ℝ)
          (GroundedTwistPolynomial.assignmentOfPins p) Q = 0

end

end SparseNullIncidence

end RB31E2E

end
end BundlePart32

set_option maxHeartbeats 0 in
#checked_checkpoint ".lake/checkpoints/PairPinProgress02/block_033/PairPinProgress02.olean" record ".lake/reports/audit/current/lsp_checkpoints/block_033.json"


module
public import ideal_integral_closure
public import determinantal_transfer
public import determinantal_transfer_scores
public import rational_polytope_certificates
public import Mathlib.Data.Pi.Interval
public import ideal_real_weight
public import schur_quotient_count

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


@[expose] public section

/- Generated from the separately readable proof sources listed in
   audit/IntegralClosureTheory_sources.json. All mathematical commands are copied verbatim.
   Generation alone is not evidence of successful kernel verification. -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory IMPORTS_LOADED\n"
  logInfo "IntegralClosureTheory IMPORTS_LOADED"

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN IdealIntegralClosureTransitivity\n"
  logInfo "IntegralClosureTheory BEGIN IdealIntegralClosureTransitivity"

/- Begin IdealIntegralClosureTransitivity.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Transitivity of ideal integral dependence

Mathlib's degree-one generation of the actual Rees algebra turns ideal
integrality into an integral ring extension.  Ring-integrality transitivity
then proves idempotence of the ideal integral closure.  No Noetherian,
domain, characteristic, or finite-generation hypothesis is needed.

These closure laws supply the idempotence used by the subsequent
quadratic determinant-exchange argument.
-/

noncomputable section

namespace CommAlg

open Polynomial

universe u v
variable {R : Type u} [CommRing R]

/-- If every element of `J` is integral over `I`, the entire actual Rees
algebra of `J` lies in the ring integral closure of the Rees algebra of `I`.
The proof checks the genuine degree-one algebra generators. -/
theorem reesAlgebra_le_integralClosure_of_le
    {I J : Ideal R} (hJI : J ≤ idealIntegralClosure I) :
    reesAlgebra J ≤
      (integralClosure (reesAlgebra I) (Polynomial R)).restrictScalars R := by
  rw [← adjoin_monomial_eq_reesAlgebra]
  apply Algebra.adjoin_le
  rintro _ ⟨x, hx, rfl⟩
  exact (hJI hx).isIntegral_rees

set_option synthInstance.maxHeartbeats 100000 in
/-- Integral dependence over an ideal is transitive through an ideal whose
elements are all integral over the original ideal. -/
theorem IntegralOverIdeal.trans {I J : Ideal R} {x : R}
    (hx : IntegralOverIdeal J x) (hJI : J ≤ idealIntegralClosure I) :
    IntegralOverIdeal I x := by
  let A := integralClosure (reesAlgebra I) (Polynomial R)
  let f : reesAlgebra J →ₐ[R] A :=
    Subalgebra.inclusion (reesAlgebra_le_integralClosure_of_le hJI)
  have hxA : IsIntegral A (Polynomial.monomial 1 x) := by
    exact IsIntegral.map_of_comp_eq f.toRingHom (RingHom.id (Polynomial R))
      (by ext; rfl) hx.isIntegral_rees
  apply integralOverIdeal_of_isIntegral_rees
  exact isIntegral_trans (R := reesAlgebra I) (A := A) (B := Polynomial R)
    (Polynomial.monomial 1 x) hxA

@[simp] theorem idealIntegralClosure_idem (I : Ideal R) :
    idealIntegralClosure (idealIntegralClosure I) = idealIntegralClosure I := by
  apply le_antisymm
  · intro x hx
    exact hx.trans le_rfl
  · exact le_idealIntegralClosure _

theorem idealIntegralClosure_isIntegrallyClosed (I : Ideal R) :
    IsIntegrallyClosedIdeal (idealIntegralClosure I) :=
  (integrallyClosedIdeal_iff_integralClosure_eq _).mpr (idealIntegralClosure_idem I)

/-- The integral closure is the least integrally closed ideal containing
the given ideal.  This also specifies its universal property literally in
the complete lattice of ideals. -/
theorem idealIntegralClosure_le_iff {I J : Ideal R}
    (hJ : IsIntegrallyClosedIdeal J) :
    idealIntegralClosure I ≤ J ↔ I ≤ J := by
  constructor
  · intro h
    exact (le_idealIntegralClosure I).trans h
  · intro h
    exact idealIntegralClosure_le_of_integrallyClosed h hJ

/-- Arbitrary intersections of integrally closed ideals are integrally
closed; this statement does not assume that a sum of such ideals is closed. -/
theorem isIntegrallyClosedIdeal_iInf {ι : Sort v} (J : ι → Ideal R)
    (hJ : ∀ i, IsIntegrallyClosedIdeal (J i)) :
    IsIntegrallyClosedIdeal (⨅ i, J i) := by
  intro x hx
  apply Ideal.mem_iInf.mpr
  intro i
  exact hJ i x (hx.mono (iInf_le J i))

end CommAlg
end
end
/- End IdealIntegralClosureTransitivity.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN IdealIntegralClosureMap\n"
  logInfo "IntegralClosureTheory BEGIN IdealIntegralClosureMap"

/- Begin IdealIntegralClosureMap.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Functoriality of the actual ideal integral equation

These helpers use the monic-equation definition, without a valuation or
Noetherian hypothesis.  In particular an integrally closed ideal contracts
to an integrally closed ideal under an arbitrary ring homomorphism.
-/

namespace CommAlg

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem IntegralOverIdeal.map (φ : R →+* S) {I : Ideal R} {x : R}
    (hx : IntegralOverIdeal I x) : IntegralOverIdeal (I.map φ) (φ x) := by
  obtain ⟨n, hn, c, hc, heq⟩ := hx
  refine ⟨n, hn, fun i => φ (c i), ?_, ?_⟩
  · intro i hi
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ (hc i hi)
  · simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg φ heq

theorem IntegralOverIdeal.map_of_le (φ : R →+* S)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map φ ≤ J) {x : R}
    (hx : IntegralOverIdeal I x) : IntegralOverIdeal J (φ x) :=
  (hx.map φ).mono hIJ

theorem IsIntegrallyClosedIdeal.comap (φ : R →+* S) {J : Ideal S}
    (hJ : IsIntegrallyClosedIdeal J) : IsIntegrallyClosedIdeal (J.comap φ) := by
  intro x hx
  exact hJ (φ x) (hx.map_of_le φ Ideal.map_comap_le)

theorem idealIntegralClosure_map_le (φ : R →+* S) (I : Ideal R) :
    (idealIntegralClosure I).map φ ≤ idealIntegralClosure (I.map φ) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  exact hx.map φ

theorem idealIntegralClosure_comap_le (φ : R →+* S) (J : Ideal S) :
    idealIntegralClosure (J.comap φ) ≤ (idealIntegralClosure J).comap φ := by
  intro x hx
  exact hx.map_of_le φ Ideal.map_comap_le

end CommAlg
end
/- End IdealIntegralClosureMap.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN IdealIntegralPowerRoot\n"
  logInfo "IntegralClosureTheory BEGIN IdealIntegralPowerRoot"

/- Begin IdealIntegralPowerRoot.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! # Clearing positive powers in genuine ideal integrality

The substitution of the Rees variable by its `q`th power sends the Rees
algebra of `I^q` into that of `I`. This supplies the exact positive-power
root step after denominators of a convex certificate have been cleared.
-/

noncomputable section
namespace CommAlg
open Polynomial
universe u
variable {R : Type u} [CommRing R]

/-- Expanding the Rees variable sends the Rees algebra of `I^q` into
that of `I`, with coefficients in the unchanged original ring. -/
theorem expand_mem_rees (I : Ideal R) (q : ℕ) {p : Polynomial R}
    (hp : p ∈ reesAlgebra (I ^ q)) : Polynomial.expand R q p ∈ reesAlgebra I := by
  classical
  rw [p.as_sum_support, map_sum]
  apply Subalgebra.sum_mem
  intro i hi
  rw [Polynomial.expand_monomial]
  apply reesAlgebra.monomial_mem.mpr
  have hc := hp i
  simpa only [← pow_mul, Nat.mul_comm] using hc

def reesPowerExpand (I : Ideal R) (q : ℕ) : reesAlgebra (I ^ q) →+* reesAlgebra I where
  toFun p := ⟨Polynomial.expand R q p.val, expand_mem_rees I q p.property⟩
  map_one' := Subtype.ext (map_one (Polynomial.expand R q))
  map_mul' p r := Subtype.ext (map_mul (Polynomial.expand R q) p.val r.val)
  map_zero' := Subtype.ext (map_zero (Polynomial.expand R q))
  map_add' p r := Subtype.ext (map_add (Polynomial.expand R q) p.val r.val)

/-- Clearing a positive power does not lose ideal integrality.  This uses
the genuine Rees-algebra characterization, not an assertion that the
ordinary power is radical. -/
theorem IntegralOverIdeal.of_pow {I : Ideal R} {x : R} {q : ℕ} (hq : 0 < q)
    (hx : IntegralOverIdeal (I ^ q) (x ^ q)) : IntegralOverIdeal I x := by
  have h := IsIntegral.map_of_comp_eq (reesPowerExpand I q)
    (Polynomial.expand R q).toRingHom (by ext p; rfl) hx.isIntegral_rees
  change IsIntegral (reesAlgebra I) (Polynomial.expand R q (Polynomial.monomial 1 (x ^ q))) at h
  have hqint : IsIntegral (reesAlgebra I) ((Polynomial.monomial 1 x) ^ q) := by
    simpa only [Polynomial.expand_monomial, Polynomial.monomial_pow, one_mul] using h
  exact integralOverIdeal_of_isIntegral_rees (hqint.of_pow hq)

end CommAlg
end
end
/- End IdealIntegralPowerRoot.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalIntegralExchange\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalIntegralExchange"

/- Begin DeterminantalIntegralExchange.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000

/-!
# The quadratic form of the determinant-transfer recurrence

Multiplying the universal exchange by the original product rewrites its
square as a linear term from balanced minor sizes plus products of two
terms with smaller row-set gaps.  Integral-closure idempotence allows a
lexicographic induction on size energy and row-set gap.  The statements
here prove the actual polynomial identity and its precise integral-ideal
consequence; they do not postulate a determinantal product containment.

-/

noncomputable section

namespace CommAlg

variable {R : Type*} [CommRing R]

/-- The exact quadratic ideal equation used in the recurrence. -/
theorem IsIntegrallyClosedIdeal.mem_of_quadratic {C : Ideal R}
    (hC : IsIntegrallyClosedIdeal C) {x a b : R}
    (ha : a ∈ C) (hb : b ∈ C ^ 2) (heq : x ^ 2 = a * x + b) : x ∈ C := by
  apply hC x
  refine ⟨2, by decide, (fun i => if i = 0 then -b else -a), ?_, ?_⟩
  · intro i hi
    have he : i = 0 ∨ i = 1 := by omega
    rcases he with rfl | rfl
    · simpa using (C ^ 2).neg_mem hb
    · simpa using C.neg_mem ha
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      if_pos rfl, Nat.one_ne_zero, if_false, if_true, pow_zero, pow_one, mul_one]
    rw [heq]
    ring

end CommAlg

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {R ι κ : Type*} [CommRing R]

/-- Isolate the first term of the universal alternating exchange. -/
theorem first_row_exchange (X : Matrix ι κ R) {u w : ℕ}
    (a : Fin u → ι) (B : Fin u → κ) (c : ι)
    (C : Fin w → ι) (D : Fin (w + 1) → κ) :
    minor X a B * minor X (Fin.cons c C) D =
      (∑ j : Fin (w + 1), (-1 : R) ^ j.val *
        minor X (Fin.cons c a) (Fin.cons (D j) B) *
        minor X C (D ∘ j.succAbove)) +
      ∑ i : Fin u, (-1 : R) ^ i.val *
        minor X ((Fin.cons c a) ∘ i.succ.succAbove) B *
        minor X (Fin.cons (a i) C) D := by
  have h := double_laplace X (Fin.cons c a) B C D
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.cons_zero,
    Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, Fin.val_succ,
    pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib] at h
  apply sub_eq_iff_eq_add.mp
  simpa only [sub_eq_add_neg, Function.comp_def] using h

/-- An identity for the square of the actual product, with each exchange
term factored into the two products that improve the row-set gap. -/
theorem square_row_exchange (X : Matrix ι κ R) {u w : ℕ}
    (a : Fin u → ι) (B : Fin u → κ) (c : ι)
    (C : Fin w → ι) (D : Fin (w + 1) → κ) (z : R) :
    (z * minor X a B * minor X (Fin.cons c C) D) ^ 2 =
      (z * ∑ j : Fin (w + 1), (-1 : R) ^ j.val *
        minor X (Fin.cons c a) (Fin.cons (D j) B) *
        minor X C (D ∘ j.succAbove)) *
          (z * minor X a B * minor X (Fin.cons c C) D) +
      ∑ i : Fin u, (-1 : R) ^ i.val *
        (z * minor X ((Fin.cons c a) ∘ i.succ.succAbove) B *
          minor X (Fin.cons c C) D) *
        (z * minor X a B * minor X (Fin.cons (a i) C) D) := by
  let p := z * minor X a B * minor X (Fin.cons c C) D
  calc
    _ = z * (minor X a B * minor X (Fin.cons c C) D) * p := by
      dsimp only [p]
      ring
    _ = _ := by
      rw [first_row_exchange, mul_add, add_mul]
      simp only [Finset.mul_sum, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [p]
      ring

/-- The actual exchange gives membership in an integrally closed ideal
once its balanced terms and the two strictly improved terms are known.
The disjunction permits a repeated-row determinant to vanish directly. -/
theorem mem_of_integral_row_exchange (X : Matrix ι κ R) {u w : ℕ}
    (a : Fin u → ι) (B : Fin u → κ) (c : ι)
    (C : Fin w → ι) (D : Fin (w + 1) → κ) (z : R)
    (J : Ideal R) (hJ : CommAlg.IsIntegrallyClosedIdeal J)
    (hbalanced : ∀ j : Fin (w + 1),
      z * minor X (Fin.cons c a) (Fin.cons (D j) B) *
        minor X C (D ∘ j.succAbove) ∈ J)
    (hexchanged : ∀ i : Fin u,
      minor X (Fin.cons (a i) C) D = 0 ∨
        (z * minor X ((Fin.cons c a) ∘ i.succ.succAbove) B *
          minor X (Fin.cons c C) D ∈ J ∧
        z * minor X a B * minor X (Fin.cons (a i) C) D ∈ J)) :
    z * minor X a B * minor X (Fin.cons c C) D ∈ J := by
  apply hJ.mem_of_quadratic (heq := square_row_exchange X a B c C D z)
  · rw [Finset.mul_sum]
    apply Ideal.sum_mem
    intro j hj
    convert J.mul_mem_left ((-1 : R) ^ j.val) (hbalanced j) using 1 <;> ring
  · apply Ideal.sum_mem
    intro i hi
    rcases hexchanged i with hz | ⟨hR, hS⟩
    · simp only [hz, mul_zero]
      exact (J ^ 2).zero_mem
    · rw [pow_two]
      have h := Ideal.mul_mem_mul hR hS
      convert (J * J).mul_mem_left ((-1 : R) ^ i.val) h using 1 <;> ring

section RowSets

variable {α : Type*} [DecidableEq α]

/-- The first exchanged row set loses exactly the selected outside row
from its difference with the large row set. -/
theorem exchanged_small_sdiff (A B : Finset α) {a c : α}
    (hc : c ∈ B) : (insert c (A.erase a)) \ B = (A \ B).erase a := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨rfl | ⟨hxa, hxA⟩, hxB⟩
    · exact False.elim (hxB hc)
    · exact ⟨hxa, hxA, hxB⟩
  · rintro ⟨hxa, hxA, hxB⟩
    exact ⟨Or.inr ⟨hxa, hxA⟩, hxB⟩

/-- The second exchanged row set removes the same outside row from the
small row set's difference, since the removed large row was outside it. -/
theorem exchanged_large_sdiff (A B : Finset α) {a c : α}
    (hc : c ∉ A) : A \ insert a (B.erase c) = (A \ B).erase a := by
  ext x
  by_cases hxA : x ∈ A
  · have hxc : x ≠ c := by intro h; subst x; exact hc hxA
    simp [Finset.mem_sdiff, Finset.mem_erase, hxA, hxc, and_comm, and_left_comm]
  · simp [Finset.mem_sdiff, Finset.mem_erase, hxA]

theorem exchanged_row_gaps_drop (A B : Finset α) {a c : α}
    (haA : a ∈ A) (haB : a ∉ B) (hcB : c ∈ B) (hcA : c ∉ A) :
    ((insert c (A.erase a)) \ B).card + 1 = (A \ B).card ∧
      (A \ insert a (B.erase c)).card + 1 = (A \ B).card := by
  rw [exchanged_small_sdiff A B hcB, exchanged_large_sdiff A B hcA]
  exact ⟨Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨haA, haB⟩),
    Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨haA, haB⟩)⟩

end RowSets

end FourPapers.Symmetric.DeterminantalTransfer

end

end
/- End DeterminantalIntegralExchange.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalProductData\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalProductData"

/- Begin DeterminantalProductData.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 900000

/-!
# Literal minor products for the transfer induction

Rows and columns are arbitrary finite tuples.  A repeated index therefore
gives zero by the ordinary determinant theorem, rather than requiring an
unproved normalization into increasing minors.  This is exactly the
generating convention used by the actual ideal of all matrix minors.
The size energy is the sum of squares of the individual minor sizes.

-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {R ι κ : Type*} [CommRing R]

structure TupleMinor (ι κ : Type*) where
  size : ℕ
  rows : Fin size → ι
  cols : Fin size → κ

def TupleMinor.value (δ : TupleMinor ι κ) (X : Matrix ι κ R) : R :=
  minor X δ.rows δ.cols

def TupleMinor.unit : TupleMinor ι κ := ⟨0, Fin.elim0, Fin.elim0⟩

@[simp] theorem TupleMinor.value_unit (X : Matrix ι κ R) :
    (TupleMinor.unit : TupleMinor ι κ).value X = 1 := by
  simp [TupleMinor.unit, TupleMinor.value, minor, Matrix.det_isEmpty]

def tupleProduct (X : Matrix ι κ R) (P : List (TupleMinor ι κ)) : R :=
  (P.map (fun δ => δ.value X)).prod

def tupleSizes (P : List (TupleMinor ι κ)) : List ℕ := P.map TupleMinor.size

def sizeEnergy (P : List (TupleMinor ι κ)) : ℕ :=
  (P.map (fun δ => δ.size ^ 2)).sum

@[simp] theorem tupleProduct_nil (X : Matrix ι κ R) : tupleProduct X [] = 1 := rfl
@[simp] theorem tupleProduct_cons (X : Matrix ι κ R) (δ : TupleMinor ι κ)
    (P : List (TupleMinor ι κ)) : tupleProduct X (δ :: P) = δ.value X * tupleProduct X P := rfl
@[simp] theorem tupleProduct_append (X : Matrix ι κ R) (P Q : List (TupleMinor ι κ)) :
    tupleProduct X (P ++ Q) = tupleProduct X P * tupleProduct X Q := by
  simp [tupleProduct]

theorem tupleProduct_perm (X : Matrix ι κ R) {P Q : List (TupleMinor ι κ)}
    (h : P.Perm Q) : tupleProduct X P = tupleProduct X Q :=
  (h.map (fun δ : TupleMinor ι κ => δ.value X)).prod_eq

theorem sizeEnergy_perm {P Q : List (TupleMinor ι κ)} (h : P.Perm Q) :
    sizeEnergy P = sizeEnergy Q := (h.map (fun δ : TupleMinor ι κ => δ.size ^ 2)).sum_eq

theorem gamma_tupleSizes_perm {P Q : List (TupleMinor ι κ)} (h : P.Perm Q) (j : ℕ) :
    gamma (tupleSizes P) j = gamma (tupleSizes Q) j := by
  exact ((h.map TupleMinor.size).map (fun a => a + 1 - j)).sum_eq

/-- The actual ideal generated by all selected `t`-by-`t` determinants.
It is definitionally the usual all-tuples matrix-minor ideal. -/
def tupleMinorIdeal (X : Matrix ι κ R) (t : ℕ) : Ideal R :=
  Ideal.span {z | ∃ (a : Fin t → ι) (b : Fin t → κ), minor X a b = z}

theorem TupleMinor.value_mem (X : Matrix ι κ R) (δ : TupleMinor ι κ) :
    δ.value X ∈ tupleMinorIdeal X δ.size :=
  Ideal.subset_span ⟨δ.rows, δ.cols, rfl⟩

/-- If all factors have size at most `t`, their product already belongs
to the ordinary power measured by `γ_t`. -/
theorem tupleProduct_mem_power_of_sizes_le (X : Matrix ι κ R)
    (P : List (TupleMinor ι κ)) (t : ℕ) (ht : 1 ≤ t)
    (hP : ∀ δ ∈ P, δ.size ≤ t) :
    tupleProduct X P ∈ (tupleMinorIdeal X t) ^ gamma (tupleSizes P) t := by
  induction P with
  | nil => simp [tupleSizes, pow_zero, Ideal.one_eq_top]
  | cons δ P ih =>
      have hδ := hP δ (by simp)
      have htail := ih (fun ε hε => hP ε (by simp [hε]))
      by_cases he : δ.size = t
      · have hm : δ.value X ∈ tupleMinorIdeal X t := by
          rw [← he]
          exact δ.value_mem X
        have hscore : δ.size + 1 - t = 1 := by omega
        simpa only [tupleProduct_cons, tupleSizes, List.map_cons, gamma_cons,
          hscore, pow_add, pow_one] using Ideal.mul_mem_mul hm htail
      · have hscore : δ.size + 1 - t = 0 := by omega
        simpa only [tupleProduct_cons, tupleSizes, List.map_cons, gamma_cons,
          hscore, zero_add] using
          ((tupleMinorIdeal X t) ^ gamma (tupleSizes P) t).mul_mem_left (δ.value X) htail

theorem tupleProduct_mem_power_of_no_large (X : Matrix ι κ R)
    (P : List (TupleMinor ι κ)) (t s : ℕ) (ht : 1 ≤ t)
    (hP : ∀ δ ∈ P, δ.size ≤ t) (hs : s ≤ gamma (tupleSizes P) t) :
    tupleProduct X P ∈ (tupleMinorIdeal X t) ^ s :=
  Ideal.pow_le_pow_right hs (tupleProduct_mem_power_of_sizes_le X P t ht hP)

theorem balanced_size_energy_drop (u v E : ℕ) (huv : u + 1 < v) :
    (u + 1) ^ 2 + (v - 1) ^ 2 + E < u ^ 2 + v ^ 2 + E := by
  have hv : 1 ≤ v := by omega
  have hvsub : v - 1 + 1 = v := Nat.sub_add_cancel hv
  nlinarith

theorem minor_comp_perm (X : Matrix ι κ R) {u : ℕ}
    (a : Fin u → ι) (b : Fin u → κ) (σ : Equiv.Perm (Fin u)) :
    minor X (a ∘ σ) b = (Equiv.Perm.sign σ : R) * minor X a b := by
  simpa only [minor, Matrix.submatrix_submatrix, Function.comp_id] using
    Matrix.det_permute σ (X.submatrix a b)

/-- Reordering a row tuple changes a determinant only by its actual
integer sign, and therefore preserves membership after any scalar factor. -/
theorem mul_minor_comp_perm_mem_iff (X : Matrix ι κ R) {u : ℕ}
    (a : Fin u → ι) (b : Fin u → κ) (σ : Equiv.Perm (Fin u))
    (z : R) (J : Ideal R) :
    z * minor X (a ∘ σ) b ∈ J ↔ z * minor X a b ∈ J := by
  constructor
  · intro h
    have h' := J.mul_mem_left (Equiv.Perm.sign σ⁻¹ : R) h
    have he : (Equiv.Perm.sign σ⁻¹ : R) * (z * minor X (a ∘ σ) b) =
        z * minor X a b := by
      calc
        _ = z * ((Equiv.Perm.sign σ⁻¹ : R) * minor X (a ∘ σ) b) := by ring
        _ = z * minor X ((a ∘ σ) ∘ (σ⁻¹ : Equiv.Perm (Fin u))) b := by
          exact congrArg (fun y => z * y) (minor_comp_perm X (a ∘ σ) b σ⁻¹).symm
        _ = _ := by
          congr 1
          congr 1
          funext i
          simp
    rwa [he] at h'
  · intro h
    rw [minor_comp_perm]
    convert J.mul_mem_left (Equiv.Perm.sign σ : R) h using 1 <;> ring

section RowTuples

variable [DecidableEq ι]

def tupleRange {u : ℕ} (a : Fin u → ι) : Finset ι := Finset.univ.image a

@[simp] theorem mem_tupleRange {u : ℕ} (a : Fin u → ι) (x : ι) :
    x ∈ tupleRange a ↔ ∃ i, a i = x := by simp [tupleRange]

theorem tupleRange_cons {u : ℕ} (c : ι) (a : Fin u → ι) :
    tupleRange (Fin.cons c a) = insert c (tupleRange a) := by
  ext x
  simp only [mem_tupleRange, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact Or.inl hi.symm
    · exact Or.inr ⟨j, hi⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, Fin.cons_zero _ _⟩
    · exact ⟨i.succ, Fin.cons_succ _ _ _⟩

theorem cons_injective_of_not_mem {u : ℕ} (c : ι) (a : Fin u → ι)
    (ha : Function.Injective a) (hc : c ∉ tupleRange a) :
    Function.Injective (Fin.cons c a) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rfl
  · exact False.elim (hc ((mem_tupleRange a c).mpr ⟨j, hij.symm⟩))
  · exact False.elim (hc ((mem_tupleRange a c).mpr ⟨i, hij⟩))
  · exact congrArg Fin.succ (ha hij)

theorem tupleRange_remove {u : ℕ} (a : Fin (u + 1) → ι)
    (ha : Function.Injective a) (i : Fin (u + 1)) :
    tupleRange (a ∘ i.succAbove) = (tupleRange a).erase (a i) := by
  ext x
  simp only [mem_tupleRange, Finset.mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => i.succAbove_ne j (ha h), ⟨i.succAbove j, rfl⟩⟩
  · rintro ⟨hne, j, rfl⟩
    have hji : j ≠ i := fun h => hne (congrArg a h)
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    exact ⟨k, congrArg a hk⟩

theorem tupleRange_card {u : ℕ} (a : Fin u → ι) (ha : Function.Injective a) :
    (tupleRange a).card = u := by
  rw [tupleRange, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]

theorem rows_injective_of_minor_ne_zero (X : Matrix ι κ R) {u : ℕ}
    (a : Fin u → ι) (b : Fin u → κ) (h : minor X a b ≠ 0) : Function.Injective a := by
  intro i j hij
  by_contra hne
  apply h
  exact Matrix.det_zero_of_row_eq hne (by funext l; exact congrArg (fun x => X x (b l)) hij)

theorem row_outside_of_larger (X : Matrix ι κ R) {u v : ℕ}
    (a : Fin u → ι) (b : Fin u → κ) (c : Fin v → ι) (d : Fin v → κ)
    (ha : minor X a b ≠ 0) (hc : minor X c d ≠ 0) (huv : u < v) :
    ∃ j, c j ∉ tupleRange a := by
  have hcard : (tupleRange a).card < (tupleRange c).card := by
    rw [tupleRange_card a (rows_injective_of_minor_ne_zero X a b ha),
      tupleRange_card c (rows_injective_of_minor_ne_zero X c d hc)]
    exact huv
  obtain ⟨x, hx, hxa⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨j, rfl⟩ := (mem_tupleRange c x).mp hx
  exact ⟨j, hxa⟩

/-- Put a selected tuple entry first, preserving all the other entries
in their original relative order. -/
def headPermutation {u : ℕ} (j : Fin (u + 1)) : Equiv.Perm (Fin (u + 1)) :=
  (finSuccEquiv' 0).trans (finSuccEquiv' j).symm

@[simp] theorem headPermutation_zero {u : ℕ} (j : Fin (u + 1)) :
    headPermutation j 0 = j := by simp [headPermutation]

@[simp] theorem headPermutation_succ {u : ℕ} (j : Fin (u + 1)) (i : Fin u) :
    headPermutation j i.succ = j.succAbove i := by
  simp only [headPermutation, Equiv.trans_apply]
  have h : finSuccEquiv' (0 : Fin (u + 1)) i.succ = some i := by
    simpa only [Fin.succAbove_zero] using finSuccEquiv'_succAbove (0 : Fin (u + 1)) i
  rw [h, finSuccEquiv'_symm_some]

theorem comp_headPermutation {u : ℕ} (a : Fin (u + 1) → ι) (j : Fin (u + 1)) :
    a ∘ headPermutation j = Fin.cons (a j) (a ∘ j.succAbove) := by
  funext i
  exact Fin.cases (by simp) (fun k => by simp) i

theorem tupleRange_comp_perm {u : ℕ} (a : Fin u → ι) (σ : Equiv.Perm (Fin u)) :
    tupleRange (a ∘ σ) = tupleRange a := by
  ext x
  simp only [mem_tupleRange, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩

end RowTuples

end FourPapers.Symmetric.DeterminantalTransfer

end
end
/- End DeterminantalProductData.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalIntegralTransfer\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalIntegralTransfer"

/- Begin DeterminantalIntegralTransfer.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Universal two-factor transfer into an integrally closed ideal

The row-set-gap induction is carried out on actual minors of an arbitrary
matrix over an arbitrary commutative ring.  Its only ideal hypothesis is
integral closedness.  The balanced products in the hypothesis are literal
products of minors of sizes `u+1` and `v-1`; the conclusion concerns sizes
`u` and `v`.  The next component supplies these balanced products by a
strictly decreasing induction on the sum of squared minor sizes.

-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

variable {R ι κ : Type*} [CommRing R]

/-- The unrestricted integral version of the two-factor size transfer.
No factorial is inverted, and no restriction on the characteristic, row
sets, column sets, or matrix dimensions is imposed. -/
theorem minor_product_mem_of_balanced
    (X : Matrix ι κ R) (J : Ideal R)
    (hJ : CommAlg.IsIntegrallyClosedIdeal J) (z : R) {u w : ℕ}
    (huv : u < w + 1)
    (hbalanced : ∀ (a : Fin (u + 1) → ι) (b : Fin (u + 1) → κ)
      (c : Fin w → ι) (d : Fin w → κ),
      z * minor X a b * minor X c d ∈ J)
    (a : Fin u → ι) (b : Fin u → κ)
    (c : Fin (w + 1) → ι) (d : Fin (w + 1) → κ) :
    z * minor X a b * minor X c d ∈ J := by
  classical
  have main : ∀ q : ℕ,
      ∀ (a : Fin u → ι) (b : Fin u → κ)
        (c : Fin (w + 1) → ι) (d : Fin (w + 1) → κ),
        ((tupleRange a) \ (tupleRange c)).card = q →
        z * minor X a b * minor X c d ∈ J := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro a b c d hq
      by_cases ha0 : minor X a b = 0
      · simpa only [ha0, mul_zero, zero_mul] using J.zero_mem
      by_cases hc0 : minor X c d = 0
      · simpa only [hc0, mul_zero] using J.zero_mem
      have ha := rows_injective_of_minor_ne_zero X a b ha0
      have hc := rows_injective_of_minor_ne_zero X c d hc0
      obtain ⟨j, hj⟩ := row_outside_of_larger X a b c d ha0 hc0 huv
      let c₀ := c j
      let C := c ∘ j.succAbove
      have hcA : c₀ ∉ tupleRange a := hj
      have hcB : c₀ ∈ tupleRange c := (mem_tupleRange c c₀).mpr ⟨j, rfl⟩
      have hC : tupleRange C = (tupleRange c).erase c₀ :=
        tupleRange_remove c hc j
      have hZ : tupleRange (Fin.cons c₀ C) = tupleRange c := by
        rw [← comp_headPermutation c j]
        exact tupleRange_comp_perm c (headPermutation j)
      apply (mul_minor_comp_perm_mem_iff X c d (headPermutation j)
        (z * minor X a b) J).mp
      rw [comp_headPermutation]
      apply mem_of_integral_row_exchange X a b c₀ C d z J hJ
      · intro l
        exact hbalanced (Fin.cons c₀ a) (Fin.cons (d l) b)
          C (d ∘ l.succAbove)
      · intro i
        by_cases hiC : a i ∈ tupleRange C
        · left
          obtain ⟨l, hl⟩ := (mem_tupleRange C (a i)).mp hiC
          exact minor_cons_rows_eq_zero X (a i) C d ⟨l, hl.symm⟩
        · right
          have hiA : a i ∈ tupleRange a := (mem_tupleRange a (a i)).mpr ⟨i, rfl⟩
          have hic : a i ≠ c₀ := by
            intro he
            exact hcA (he ▸ hiA)
          have hiB : a i ∉ tupleRange c := by
            intro hi
            apply hiC
            rw [hC]
            exact Finset.mem_erase.mpr ⟨hic, hi⟩
          let A' := (Fin.cons c₀ a) ∘ i.succ.succAbove
          have hA' : tupleRange A' = insert c₀ ((tupleRange a).erase (a i)) := by
            dsimp only [A']
            rw [tupleRange_remove (Fin.cons c₀ a)
              (cons_injective_of_not_mem c₀ a ha hcA) i.succ,
              tupleRange_cons]
            simp only [Fin.cons_succ]
            exact Finset.erase_insert_of_ne hic.symm
          have hB' : tupleRange (Fin.cons (a i) C) =
              insert (a i) ((tupleRange c).erase c₀) := by
            rw [tupleRange_cons, hC]
          have hdrop := exchanged_row_gaps_drop (tupleRange a) (tupleRange c)
            hiA hiB hcB hcA
          have hsmall : ((tupleRange A') \ tupleRange (Fin.cons c₀ C)).card < q := by
            rw [hA', hZ]
            omega
          have hlarge : ((tupleRange a) \ tupleRange (Fin.cons (a i) C)).card < q := by
            rw [hB']
            omega
          exact ⟨ih _ hsmall A' b (Fin.cons c₀ C) d rfl,
            ih _ hlarge a b (Fin.cons (a i) C) d rfl⟩
  exact main _ a b c d rfl

/-- The same universal result with an arbitrary positive large size.
This form is convenient for the outer size-energy induction. -/
theorem tuple_product_mem_of_balanced
    (X : Matrix ι κ R) (J : Ideal R)
    (hJ : CommAlg.IsIntegrallyClosedIdeal J) (z : R) {u v : ℕ}
    (huv : u < v)
    (hbalanced : ∀ (a : Fin (u + 1) → ι) (b : Fin (u + 1) → κ)
      (c : Fin (v - 1) → ι) (d : Fin (v - 1) → κ),
      z * minor X a b * minor X c d ∈ J)
    (a : Fin u → ι) (b : Fin u → κ)
    (c : Fin v → ι) (d : Fin v → κ) :
    z * minor X a b * minor X c d ∈ J := by
  cases v with
  | zero => omega
  | succ w =>
      exact minor_product_mem_of_balanced X J hJ z huv hbalanced a b c d

end FourPapers.Symmetric.DeterminantalTransfer

end

end
/- End DeterminantalIntegralTransfer.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalMajorization\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalMajorization"

/- Begin DeterminantalMajorization.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The finite majorization step for arbitrary minor-product shapes

The target size vector is decreasing.  A current vector has the same
total size and dominates every target prefix.  Unless the vectors agree,
one can transfer a unit from an earlier oversized component to a later
undersized component.  Every prefix inequality is preserved, and the
sum of squared sizes strictly decreases.  The current vector need not
remain sorted after a transfer.

-/

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {N : ℕ}

def prefixIndices (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val < k)

@[simp] theorem mem_prefixIndices (i : Fin N) (k : ℕ) :
    i ∈ prefixIndices N k ↔ i.val < k := by simp [prefixIndices]

def prefixSum (f : Fin N → ℕ) (k : ℕ) : ℕ := ∑ i ∈ prefixIndices N k, f i

def PrefixDominates (target current : Fin N → ℕ) : Prop :=
  ∀ k, prefixSum target k ≤ prefixSum current k

@[simp] theorem prefixIndices_full : prefixIndices N N = Finset.univ := by
  ext i
  simp only [mem_prefixIndices, Finset.mem_univ, iff_true]
  exact i.isLt

@[simp] theorem prefixSum_full (f : Fin N → ℕ) :
    prefixSum f N = ∑ i, f i := by rw [prefixSum, prefixIndices_full]

/-- Remove one unit at `a` and add one at `b`. -/
def transferSizes (f : Fin N → ℕ) (a b : Fin N) : Fin N → ℕ :=
  Function.update (Function.update f a (f a - 1)) b (f b + 1)

theorem transferSizes_balance (f : Fin N → ℕ) {a b : Fin N}
    (hab : a ≠ b) (ha : 1 ≤ f a) (i : Fin N) :
    transferSizes f a b i + (if i = a then 1 else 0) =
      f i + (if i = b then 1 else 0) := by
  by_cases hia : i = a
  · subst i
    simp only [transferSizes, Function.update_of_ne hab, Function.update_self,
      if_pos rfl, if_neg hab, if_true]
    omega
  · by_cases hib : i = b
    · subst i
      simp [transferSizes, hab.symm]
    · simp [transferSizes, hia, hib]

theorem transferSizes_prefix_balance (f : Fin N → ℕ) {a b : Fin N}
    (hab : a ≠ b) (ha : 1 ≤ f a) (k : ℕ) :
    prefixSum (transferSizes f a b) k + (if a.val < k then 1 else 0) =
      prefixSum f k + (if b.val < k then 1 else 0) := by
  have hh : (∑ i ∈ prefixIndices N k,
       (transferSizes f a b i + (if i = a then 1 else 0))) =
      ∑ i ∈ prefixIndices N k, (f i + (if i = b then 1 else 0)) :=
    Finset.sum_congr rfl (fun i hi => transferSizes_balance f hab ha i)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', mem_prefixIndices,
    prefixSum] using hh

theorem transferSizes_sum (f : Fin N → ℕ) {a b : Fin N}
    (hab : a ≠ b) (ha : 1 ≤ f a) :
    (∑ i, transferSizes f a b i) = ∑ i, f i := by
  have h := transferSizes_prefix_balance f hab ha N
  simp only [prefixSum_full, a.isLt, b.isLt, if_true] at h
  omega

theorem transferSizes_preserves_prefixes {target current : Fin N → ℕ}
    (hdom : PrefixDominates target current) {a b : Fin N}
    (hab : a < b) (ha : target a < current a)
    (hbefore : ∀ i, i < b → target i ≤ current i) :
    PrefixDominates target (transferSizes current a b) := by
  intro k
  have hb := transferSizes_prefix_balance current (ne_of_lt hab) (by omega) k
  have hbase := hdom k
  by_cases hak : a.val < k
  · by_cases hbk : b.val < k
    · simp only [hak, hbk, if_true] at hb
      omega
    · have hstrict : prefixSum target k < prefixSum current k := by
        apply Finset.sum_lt_sum
        · intro i hi
          apply hbefore i
          have hik := (mem_prefixIndices i k).mp hi
          change i.val < b.val
          omega
        · exact ⟨a, (mem_prefixIndices a k).mpr hak, ha⟩
      simp only [hak, hbk, if_true, if_false, add_zero] at hb
      omega
  · have hbk : ¬ b.val < k := by
      have habv : a.val < b.val := hab
      omega
    simp only [hak, hbk, if_false, add_zero] at hb
    omega

theorem sum_two_indices (f : Fin N → ℕ) {a b : Fin N} (hab : a ≠ b) :
    (∑ i, f i) = f a + f b +
      ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
  have ha : a ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
  have hb : b ∈ (Finset.univ : Finset (Fin N)).erase a := by simp [hab.symm]
  rw [← Finset.add_sum_erase Finset.univ f ha,
    ← Finset.add_sum_erase (Finset.univ.erase a) f hb]
  omega

theorem transferSizes_energy_drop (f : Fin N → ℕ) {a b : Fin N}
    (hab : a ≠ b) (hgap : f b + 1 < f a) :
    (∑ i, (transferSizes f a b i) ^ 2) < ∑ i, (f i) ^ 2 := by
  have hrest : (∑ i ∈ (Finset.univ.erase a).erase b, (transferSizes f a b i) ^ 2) =
      ∑ i ∈ (Finset.univ.erase a).erase b, (f i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hib : i ≠ b := (Finset.mem_erase.mp hi).1
    have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [transferSizes, hia, hib]
  rw [sum_two_indices (fun i => (transferSizes f a b i) ^ 2) hab,
    sum_two_indices (fun i => (f i) ^ 2) hab, hrest]
  simp only [transferSizes, Function.update_of_ne hab, Function.update_self]
  have hpos : 1 ≤ f a := by omega
  have hsub : f a - 1 + 1 = f a := Nat.sub_add_cancel hpos
  nlinarith

/-- An actual strictly improving transfer exists whenever two equal-mass
vectors differ.  The first deficient index has no earlier deficiency. -/
theorem exists_majorization_transfer {target current : Fin N → ℕ}
    (htarget : Antitone target) (hdom : PrefixDominates target current)
    (hmass : (∑ i, current i) = ∑ i, target i) (hne : current ≠ target) :
    ∃ a b : Fin N, a < b ∧ target a < current a ∧ current b < target b ∧
      (∀ i, i < b → target i ≤ current i) ∧ current b + 1 < current a := by
  classical
  let B := Finset.univ.filter (fun i => current i < target i)
  have hB : B.Nonempty := by
    by_contra hn
    have hle : ∀ i, target i ≤ current i := by
      intro i
      by_contra hi
      apply hn
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hex : ∃ i, target i < current i := by
      by_contra hh
      apply hne
      funext i
      have hnlt : ¬ target i < current i := fun hi => hh ⟨i, hi⟩
      exact le_antisymm (by omega) (hle i)
    obtain ⟨i, hi⟩ := hex
    have hs : (∑ j, target j) < ∑ j, current j :=
      Finset.sum_lt_sum (fun j hj => hle j) ⟨i, Finset.mem_univ _, hi⟩
    omega
  let b := B.min' hB
  have hbB : b ∈ B := Finset.min'_mem B hB
  have hb : current b < target b := (Finset.mem_filter.mp hbB).2
  have hbefore : ∀ i, i < b → target i ≤ current i := by
    intro i hib
    by_contra hbad
    have hiB : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hbi : b ≤ i := Finset.min'_le B i hiB
    exact (not_le_of_gt hib) hbi
  have hex : ∃ a, a < b ∧ target a < current a := by
    by_contra hh
    have hprior : ∀ i, i < b → current i ≤ target i := by
      intro i hib
      by_contra hi
      exact hh ⟨i, hib, by omega⟩
    have hstrict : prefixSum current (b.val + 1) < prefixSum target (b.val + 1) := by
      apply Finset.sum_lt_sum
      · intro i hi
        have hiv := (mem_prefixIndices i (b.val + 1)).mp hi
        by_cases hie : i = b
        · subst i
          exact hb.le
        · apply hprior i
          change i.val < b.val
          have hine : i.val ≠ b.val := fun he => hie (Fin.ext he)
          omega
      · exact ⟨b, (mem_prefixIndices b (b.val + 1)).mpr (by omega), hb⟩
    exact (not_lt_of_ge (hdom (b.val + 1))) hstrict
  obtain ⟨a, hab, ha⟩ := hex
  refine ⟨a, b, hab, ha, hb, hbefore, ?_⟩
  have ht := htarget hab.le
  omega

end FourPapers.Symmetric.DeterminantalTransfer
end
/- End DeterminantalMajorization.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalProductLowerInclusion\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalProductLowerInclusion"

/- Begin DeterminantalProductLowerInclusion.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Actual minor-product integrality under shape majorization

The target is a product of actual determinantal ideals.  Its decreasing
size vector is compared with the sizes of an arbitrary finite family of
actual minors.  Equal total size and all prefix inequalities imply that
the literal product is integral over the target ideal.  The proof calls
the universal two-factor transfer and discharges every balanced premise
by the strictly smaller size-energy induction.

The subsequent score-to-majorization and padding modules extend this
result to arbitrary target degrees and factor counts, completing the
determinant-product lower inclusion.
-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {R ι κ : Type*} [CommRing R] {N : ℕ}

def minorProductIdeal (X : Matrix ι κ R) (target : Fin N → ℕ) : Ideal R :=
  ∏ i, tupleMinorIdeal X (target i)

def minorFamilyProduct (X : Matrix ι κ R) (P : Fin N → TupleMinor ι κ) : R :=
  ∏ i, (P i).value X

theorem prod_two_indices (f : Fin N → R) {a b : Fin N} (hab : a ≠ b) :
    (∏ i, f i) = f a * f b * ∏ i ∈ (Finset.univ.erase a).erase b, f i := by
  have ha : a ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
  have hb : b ∈ (Finset.univ : Finset (Fin N)).erase a := by simp [hab.symm]
  rw [← Finset.mul_prod_erase Finset.univ f ha,
    ← Finset.mul_prod_erase (Finset.univ.erase a) f hb, mul_assoc]

theorem minorFamilyProduct_mem_of_sizes (X : Matrix ι κ R)
    (target : Fin N → ℕ) (P : Fin N → TupleMinor ι κ)
    (hsize : ∀ i, (P i).size = target i) :
    minorFamilyProduct X P ∈ minorProductIdeal X target := by
  apply Ideal.prod_mem_prod
  intro i hi
  simpa only [hsize i] using (P i).value_mem X

/-- Arbitrary determinantal-product lower inclusion in its exact finite
majorization form.  Both the target ideal and the proposed integral
element are defined by actual matrix minors. -/
theorem minorFamilyProduct_mem_integralClosure_of_majorization
    (X : Matrix ι κ R) (target : Fin N → ℕ) (htarget : Antitone target)
    (P : Fin N → TupleMinor ι κ)
    (hmass : (∑ i, (P i).size) = ∑ i, target i)
    (hdom : PrefixDominates target (fun i => (P i).size)) :
    minorFamilyProduct X P ∈ CommAlg.idealIntegralClosure (minorProductIdeal X target) := by
  classical
  let J := CommAlg.idealIntegralClosure (minorProductIdeal X target)
  have hJ : CommAlg.IsIntegrallyClosedIdeal J :=
    CommAlg.idealIntegralClosure_isIntegrallyClosed _
  have main : ∀ E : ℕ, ∀ P : Fin N → TupleMinor ι κ,
      (∑ i, (P i).size ^ 2) = E →
      (∑ i, (P i).size) = ∑ i, target i →
      PrefixDominates target (fun i => (P i).size) → minorFamilyProduct X P ∈ J := by
    intro E
    induction E using Nat.strong_induction_on with
    | _ E ih =>
      intro P hE hmass hdom
      let current := fun i => (P i).size
      by_cases hsame : current = target
      · apply CommAlg.le_idealIntegralClosure _
        exact minorFamilyProduct_mem_of_sizes X target P (fun i => congrFun hsame i)
      obtain ⟨a, b, hab, ha, hb, hbefore, hgap⟩ :=
        exists_majorization_transfer htarget hdom hmass hsame
      let S := (Finset.univ.erase a).erase b
      let z := ∏ i ∈ S, (P i).value X
      have hprod : minorFamilyProduct X P =
          z * minor X (P b).rows (P b).cols * minor X (P a).rows (P a).cols := by
        rw [minorFamilyProduct, prod_two_indices (fun i => (P i).value X) (ne_of_lt hab)]
        dsimp only [z, S, TupleMinor.value]
        ring
      rw [hprod]
      apply tuple_product_mem_of_balanced X J hJ z (by change (P b).size < (P a).size; omega)
      intro α β γ δ
      let small : TupleMinor ι κ := ⟨(P b).size + 1, α, β⟩
      let large : TupleMinor ι κ := ⟨(P a).size - 1, γ, δ⟩
      let P' := Function.update (Function.update P a large) b small
      have hsize : (fun i => (P' i).size) = transferSizes current a b := by
        funext i
        by_cases hia : i = a
        · subst i
          simp [P', transferSizes, ne_of_lt hab, small, large, current]
        · by_cases hib : i = b
          · subst i
            simp [P', transferSizes, ne_of_gt hab, small, large, current]
          · simp [P', transferSizes, hia, hib, current]
      have hless : (∑ i, (P' i).size ^ 2) < E := by
        rw [← hE]
        simpa only [← hsize, current] using
          transferSizes_energy_drop current (ne_of_lt hab) hgap
      have hmass' : (∑ i, (P' i).size) = ∑ i, target i := by
        calc
          (∑ i, (P' i).size) = ∑ i, current i := by
            simpa only [← hsize] using
              transferSizes_sum current (ne_of_lt hab) (by change 1 ≤ (P a).size; omega)
          _ = _ := hmass
      have hdom' : PrefixDominates target (fun i => (P' i).size) := by
        rw [hsize]
        exact transferSizes_preserves_prefixes hdom hab ha hbefore
      have hm := ih _ hless P' rfl hmass' hdom'
      have hrest : (∏ i ∈ S, (P' i).value X) = z := by
        apply Finset.prod_congr rfl
        intro i hi
        have hib : i ≠ b := (Finset.mem_erase.mp hi).1
        have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [P', hia, hib]
      have hp' : minorFamilyProduct X P' = z * minor X α β * minor X γ δ := by
        rw [minorFamilyProduct, prod_two_indices (fun i => (P' i).value X) (ne_of_lt hab)]
        change (P' a).value X * (P' b).value X * (∏ i ∈ S, (P' i).value X) = _
        rw [hrest]
        simp only [P', Function.update_of_ne (ne_of_lt hab), Function.update_self]
        dsimp only [small, large, TupleMinor.value]
        ring
      rwa [hp'] at hm
  exact main _ P rfl hmass hdom

end FourPapers.Symmetric.DeterminantalTransfer

end

end
/- End DeterminantalProductLowerInclusion.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalScoreMajorization\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalScoreMajorization"

/- Begin DeterminantalScoreMajorization.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Score inequalities and actual shape majorization

This component proves the discrete prefix/positive-part duality and
constructs a genuine permutation sorting an arbitrary finite size vector.
It therefore removes any ordering condition on the actual minor family
from the equal-total-degree product lower inclusion.

-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {N : ℕ}

def vectorGamma (f : Fin N → ℕ) (j : ℕ) : ℕ := ∑ i, (f i + 1 - j)

@[simp] theorem vectorGamma_one (f : Fin N → ℕ) : vectorGamma f 1 = ∑ i, f i := by
  simp [vectorGamma]

theorem prefixIndices_eq_univ_of_le {k : ℕ} (h : N ≤ k) :
    prefixIndices N k = Finset.univ := by
  ext i
  simp only [mem_prefixIndices, Finset.mem_univ, iff_true]
  exact i.isLt.trans_le h

theorem prefixSum_le_cut (f : Fin N → ℕ) (k c : ℕ) :
    prefixSum f k ≤ (prefixIndices N k).card * c + vectorGamma f (c + 1) := by
  have hsmall : prefixSum f k ≤
      (prefixIndices N k).card * c + ∑ i ∈ prefixIndices N k, (f i - c) := by
    calc
      prefixSum f k ≤ ∑ i ∈ prefixIndices N k, (c + (f i - c)) := by
        apply Finset.sum_le_sum
        intro i hi
        omega
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hsubset : (∑ i ∈ prefixIndices N k, (f i - c)) ≤ ∑ i, (f i - c) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hgamma : vectorGamma f (c + 1) = ∑ i, (f i - c) := by
    simp only [vectorGamma, Nat.add_sub_add_right]
  omega

/-- The cutoff given by the first unselected entry realizes the positive-
part bound exactly for a decreasing vector. -/
theorem prefixSum_eq_cut (f : Fin N → ℕ) (hf : Antitone f) {k : ℕ} (hk : k < N) :
    prefixSum f k = (prefixIndices N k).card * f ⟨k, hk⟩ +
      vectorGamma f (f ⟨k, hk⟩ + 1) := by
  let c := f ⟨k, hk⟩
  have hgamma : vectorGamma f (c + 1) = ∑ i ∈ prefixIndices N k, (f i - c) := by
    simp only [vectorGamma, Nat.add_sub_add_right]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hnot
    have hik : k ≤ i.val := by
      have hn : ¬ i.val < k := fun h => hnot ((mem_prefixIndices i k).mpr h)
      omega
    exact Nat.sub_eq_zero_of_le (hf (show (⟨k, hk⟩ : Fin N) ≤ i from hik))
  calc
    prefixSum f k = ∑ i ∈ prefixIndices N k, (c + (f i - c)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik := (mem_prefixIndices i k).mp hi
      have hle : c ≤ f i := hf (show i ≤ (⟨k, hk⟩ : Fin N) from Nat.le_of_lt hik)
      omega
    _ = (prefixIndices N k).card * c + ∑ i ∈ prefixIndices N k, (f i - c) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = _ := by rw [hgamma]

theorem prefixDominates_of_scores {target current : Fin N → ℕ}
    (hcurrent : Antitone current)
    (hmass : (∑ i, current i) = ∑ i, target i)
    (hscore : ∀ j, 1 ≤ j → vectorGamma target j ≤ vectorGamma current j) :
    PrefixDominates target current := by
  intro k
  by_cases hk : k < N
  · have hbound := prefixSum_le_cut target k (current ⟨k, hk⟩)
    have heq := prefixSum_eq_cut current hcurrent hk
    have hs := hscore (current ⟨k, hk⟩ + 1) (by omega)
    omega
  · have hN : N ≤ k := Nat.le_of_not_gt hk
    simp only [prefixSum, prefixIndices_eq_univ_of_le hN]
    exact hmass.symm.le

/-- A permutation of the original indices, ordered by descending size
and then by its original index.  The second key makes the ranking exact
even when sizes repeat. -/
theorem exists_antitone_permutation (f : Fin N → ℕ) :
    ∃ σ : Equiv.Perm (Fin N), Antitone (f ∘ σ) := by
  let key : ULift.{0} (Fin N) → ℕᵒᵈ ×ₗ Fin N := fun i => toLex (OrderDual.toDual (f i.down), i.down)
  have hk : Function.Injective key := by
    intro i j hij
    apply ULift.ext
    exact congrArg (fun p : ℕᵒᵈ ×ₗ Fin N => p.2) hij
  letI : LinearOrder (ULift.{0} (Fin N)) := LinearOrder.lift' key hk
  let e := Fintype.orderIsoFinOfCardEq (ULift.{0} (Fin N)) (k := N)
    (by simp only [Fintype.card_ulift, Fintype.card_fin])
  let σ : Equiv.Perm (Fin N) := e.toEquiv.trans Equiv.ulift
  refine ⟨σ, ?_⟩
  intro i j hij
  have hh : key (e i) ≤ key (e j) := e.map_rel_iff.mpr hij
  simp only [key, Prod.Lex.toLex_le_toLex] at hh
  rcases hh with hh | ⟨heq, hidx⟩
  · exact le_of_lt hh
  · exact le_of_eq heq.symm

theorem vectorGamma_perm (f : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) (j : ℕ) :
    vectorGamma (f ∘ σ) j = vectorGamma f j := by
  simpa only [vectorGamma, Function.comp_apply] using
    Equiv.sum_comp σ (fun i => f i + 1 - j)

variable {R ι κ : Type*} [CommRing R]

/-- Equal-total-degree arbitrary-product lower inclusion stated solely
in the original score inequalities.  Neither the target nor the actual
minor family is required to be ordered. -/
theorem minorFamilyProduct_mem_integralClosure_of_scores
    (X : Matrix ι κ R) (target : Fin N → ℕ) (P : Fin N → TupleMinor ι κ)
    (hmass : (∑ i, (P i).size) = ∑ i, target i)
    (hscore : ∀ j, 1 ≤ j → vectorGamma target j ≤
      vectorGamma (fun i => (P i).size) j) :
    minorFamilyProduct X P ∈ CommAlg.idealIntegralClosure (minorProductIdeal X target) := by
  obtain ⟨τ, hτ⟩ := exists_antitone_permutation target
  obtain ⟨σ, hσ⟩ := exists_antitone_permutation (fun i => (P i).size)
  let Q := P ∘ σ
  have hmass' : (∑ i, (Q i).size) = ∑ i, (target ∘ τ) i := by
    change (∑ i, (P (σ i)).size) = ∑ i, target (τ i)
    rw [Equiv.sum_comp σ (fun i => (P i).size), Equiv.sum_comp τ target]
    exact hmass
  have hscore' : ∀ j, 1 ≤ j → vectorGamma (target ∘ τ) j ≤
      vectorGamma (fun i => (Q i).size) j := by
    intro j hj
    rw [vectorGamma_perm target τ]
    change vectorGamma target j ≤ vectorGamma ((fun i => (P i).size) ∘ σ) j
    rw [vectorGamma_perm]
    exact hscore j hj
  have hdom := prefixDominates_of_scores hσ hmass' hscore'
  have hm := minorFamilyProduct_mem_integralClosure_of_majorization X (target ∘ τ) hτ Q
    hmass' hdom
  have hprod : minorFamilyProduct X Q = minorFamilyProduct X P :=
    Equiv.prod_comp σ (fun i => (P i).value X)
  have hideal : minorProductIdeal X (target ∘ τ) = minorProductIdeal X target :=
    Equiv.prod_comp τ (fun i => tupleMinorIdeal X (target i))
  rwa [hprod, hideal] at hm

end FourPapers.Symmetric.DeterminantalTransfer

end

end
/- End DeterminantalScoreMajorization.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalProductScoreLower\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalProductScoreLower"

/- Begin DeterminantalProductScoreLower.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Unrestricted score lower inclusion for determinantal products

This component removes both the equal-degree and the equal-factor-count
restrictions from the preceding majorization theorem.  It pads the target
by size-one factors to match total degree, then pads both lists by literal
unit minors of size zero to match their lengths.  The resulting target
ideal is contained in the original target ideal.

All size vectors, finite minor products, commutative coefficient rings,
and actual matrices are unrestricted.  This is the lower inclusion for
individual minor products; it does not assert the still-required ideal
basis or finite-polytope upper inclusion.

-/

noncomputable section

namespace FourPapers.Symmetric.DeterminantalTransfer

open scoped BigOperators

variable {R ι κ : Type*} [CommRing R]

def listMinorProductIdeal (X : Matrix ι κ R) (sizes : List ℕ) : Ideal R :=
  (sizes.map (tupleMinorIdeal X)).prod

@[simp] theorem tupleMinorIdeal_zero (X : Matrix ι κ R) : tupleMinorIdeal X 0 = 1 := by
  rw [Ideal.one_eq_top]
  apply (Ideal.eq_top_iff_one _).mpr
  have h := (TupleMinor.unit : TupleMinor ι κ).value_mem X
  change TupleMinor.unit.value X ∈ tupleMinorIdeal X 0 at h
  simpa only [TupleMinor.value_unit] using h

theorem sum_list_get_map {α : Type*} (l : List α) (f : α → ℕ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← Fin.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem prod_list_get_map {α M : Type*} [CommMonoid M] (l : List α) (f : α → M) :
    (∏ i : Fin l.length, f (l.get i)) = (l.map f).prod := by
  rw [← Fin.prod_ofFn]
  change (List.ofFn (f ∘ l.get)).prod = _
  rw [← List.map_ofFn, List.ofFn_get]

@[simp] theorem gamma_one (L : List ℕ) : gamma L 1 = L.sum := by
  simp [gamma]

theorem gamma_replicate (n a j : ℕ) :
    gamma (List.replicate n a) j = n * (a + 1 - j) := by
  simp [gamma, List.sum_replicate]

/-- The equal-length bridge checks the actual finite-index/list product
dictionary, including the harmless cast of the target index type. -/
theorem tupleProduct_mem_integralClosure_equal_degree
    (X : Matrix ι κ R) (sizes : List ℕ) (P : List (TupleMinor ι κ))
    (hlen : P.length = sizes.length)
    (hmass : (tupleSizes P).sum = sizes.sum)
    (hscore : ∀ j, 1 ≤ j → gamma sizes j ≤ gamma (tupleSizes P) j) :
    tupleProduct X P ∈ CommAlg.idealIntegralClosure (listMinorProductIdeal X sizes) := by
  let target : Fin P.length → ℕ := sizes.get ∘ finCongr hlen
  let Q : Fin P.length → TupleMinor ι κ := P.get
  have hsumQ : (∑ i, (Q i).size) = (tupleSizes P).sum := sum_list_get_map P TupleMinor.size
  have hsumT : (∑ i, target i) = sizes.sum := by
    calc
      (∑ i, target i) = ∑ i : Fin sizes.length, sizes.get i := Equiv.sum_comp _ _
      _ = sizes.sum := by simpa using sum_list_get_map sizes id
  have hgQ (j : ℕ) : vectorGamma (fun i => (Q i).size) j = gamma (tupleSizes P) j := by
    change (∑ i : Fin P.length, ((P.get i).size + 1 - j)) = _
    rw [sum_list_get_map P (fun δ => δ.size + 1 - j)]
    simp only [gamma, tupleSizes, List.map_map, Function.comp_def]
  have hgT (j : ℕ) : vectorGamma target j = gamma sizes j := by
    calc
      vectorGamma target j = ∑ i : Fin sizes.length, (sizes.get i + 1 - j) :=
        Equiv.sum_comp (finCongr hlen) (fun i => sizes.get i + 1 - j)
      _ = gamma sizes j := sum_list_get_map sizes (fun a => a + 1 - j)
  have hm := minorFamilyProduct_mem_integralClosure_of_scores X target Q
    (by rw [hsumQ, hsumT]; exact hmass)
    (fun j hj => by rw [hgQ, hgT]; exact hscore j hj)
  have hp : minorFamilyProduct X Q = tupleProduct X P :=
    prod_list_get_map P (fun δ => δ.value X)
  have hI : minorProductIdeal X target = listMinorProductIdeal X sizes := by
    calc
      minorProductIdeal X target = ∏ i : Fin sizes.length, tupleMinorIdeal X (sizes.get i) :=
        Equiv.prod_comp (finCongr hlen) (fun i => tupleMinorIdeal X (sizes.get i))
      _ = listMinorProductIdeal X sizes := prod_list_get_map sizes (tupleMinorIdeal X)
  rwa [hp, hI] at hm

/-- Full product-shape lower inclusion.  There is no assumption on total
degree, factor count, ordering of either list, characteristic, matrix size,
or the ranks of the chosen minors. -/
theorem tupleProduct_mem_integralClosure_product
    (X : Matrix ι κ R) (sizes : List ℕ) (P : List (TupleMinor ι κ))
    (hscore : ∀ j, 1 ≤ j → gamma sizes j ≤ gamma (tupleSizes P) j) :
    tupleProduct X P ∈ CommAlg.idealIntegralClosure (listMinorProductIdeal X sizes) := by
  have hdeg : sizes.sum ≤ (tupleSizes P).sum := by
    simpa only [gamma_one] using hscore 1 le_rfl
  let excess := (tupleSizes P).sum - sizes.sum
  let Q := P ++ List.replicate (sizes.length + excess) (TupleMinor.unit : TupleMinor ι κ)
  let T := sizes ++ List.replicate excess 1 ++ List.replicate P.length 0
  have hlen : Q.length = T.length := by
    simp only [Q, T, List.length_append, List.length_replicate]
    omega
  have hsizesQ : tupleSizes Q = tupleSizes P ++ List.replicate (sizes.length + excess) 0 := by
    simp only [Q, tupleSizes, List.map_append, List.map_replicate, TupleMinor.unit]
  have hmass : (tupleSizes Q).sum = T.sum := by
    rw [hsizesQ]
    simp only [T, List.sum_append, List.sum_replicate, nsmul_eq_mul,
      mul_zero, mul_one, add_zero, Nat.cast_id]
    dsimp only [excess]
    omega
  have hscores : ∀ j, 1 ≤ j → gamma T j ≤ gamma (tupleSizes Q) j := by
    intro j hj
    by_cases hj1 : j = 1
    · subst j
      simpa only [gamma_one] using hmass.symm.le
    · have hz : 0 + 1 - j = 0 := by omega
      have ho : 1 + 1 - j = 0 := by omega
      simp only [T, hsizesQ, gamma_append, gamma_replicate, hz, ho,
        mul_zero, add_zero]
      exact hscore j hj
  have hm := tupleProduct_mem_integralClosure_equal_degree X T Q hlen hmass hscores
  have hp : tupleProduct X Q = tupleProduct X P := by
    simp only [Q, tupleProduct, List.map_append, List.map_replicate,
      TupleMinor.value_unit, List.prod_append, List.prod_replicate, one_pow, mul_one]
  have hI : listMinorProductIdeal X T ≤ listMinorProductIdeal X sizes := by
    simp only [T, listMinorProductIdeal, List.map_append, List.map_replicate,
      List.prod_append, List.prod_replicate, tupleMinorIdeal_zero, one_pow, mul_one]
    exact Ideal.mul_le_left
  have hout := CommAlg.idealIntegralClosure_mono hI hm
  rwa [hp] at hout

end FourPapers.Symmetric.DeterminantalTransfer

end

end
/- End DeterminantalProductScoreLower.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN PolytopeSeparation\n"
  logInfo "IntegralClosureTheory BEGIN PolytopeSeparation"

/- Begin PolytopeSeparation.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Nonnegative supporting weights for upward convex hulls

The compact convex hull of finitely many vertices can be separated from the
closed lower orthant of a point outside its upward closure.  Boundedness of
the separating functional on that orthant forces each coordinate weight to
be nonnegative.  This is exactly the family of weights tested by the generic
Gram substitution; no appeal to an unformalized linear-programming theorem
is needed.
-/

noncomputable section
namespace FourPapers.Symmetric.RationalPolyhedra
open scoped BigOperators

/-- A point outside an upward finite convex hull has a nonnegative real
weight strictly separating it from every vertex. -/
theorem nonnegative_separation {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℝ) (x : ν → ℝ) (hx : x ∉ upperHull v) :
    ∃ w : ν → ℝ, (∀ j, 0 ≤ w j) ∧
      ∀ i, (∑ j, w j * x j) < ∑ j, w j * v i j := by
  classical
  have hdisj : Disjoint (Set.Iic x) (convexHull ℝ (Set.range v)) := by
    rw [Set.disjoint_left]
    intro y hy hc
    exact hx ⟨y,hc,hy⟩
  obtain ⟨f,u,z,hf,huz,hg⟩ := geometric_hahn_banach_closed_compact
    (convex_Iic x) isClosed_Iic (convex_convexHull ℝ (Set.range v))
    ((Set.finite_range v).isCompact_convexHull ℝ) hdisj
  let w : ν → ℝ := fun j => f (Pi.single j 1)
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    by_contra hn
    have hwj : w j < 0 := lt_of_not_ge hn
    have hfx : f x < u := hf x (le_refl x)
    let t : ℝ := (u - f x + 1) / (-w j)
    have ht : 0 < t := div_pos (by linarith) (by linarith)
    have he : t * (-w j) = u - f x + 1 :=
      div_mul_cancel₀ _ (ne_of_gt (show 0 < -w j by linarith))
    have hle : x - t • Pi.single j (1 : ℝ) ≤ x := by
      intro k
      change x k - t * ((Pi.single j (1 : ℝ) : ν → ℝ) k) ≤ x k
      apply sub_le_self
      apply mul_nonneg ht.le
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hlt := hf (x - t • Pi.single j (1 : ℝ)) hle
    have hform : f (x - t • Pi.single j (1 : ℝ)) = f x - t * w j := by
      simp only [map_sub, map_smul, smul_eq_mul, w]
    rw [hform] at hlt
    nlinarith
  have heval (y : ν → ℝ) : f y = ∑ j, w j * y j := by
    have hy : y = ∑ j, y j • Pi.single j (1 : ℝ) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc
      f y = f (∑ j, y j • Pi.single j (1 : ℝ)) := congrArg f hy
      _ = ∑ j, w j * y j := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_smul, smul_eq_mul, w, mul_comm]
  refine ⟨w,hw,?_⟩
  intro i
  have ha := hf x (le_refl x)
  have hb := hg (v i) (subset_convexHull ℝ (Set.range v) ⟨i,rfl⟩)
  rw [← heval, ← heval]
  exact ha.trans (huz.trans hb)

/-- Membership is determined by all nonnegative weights.  The finite
minimum is expressed by an actual vertex rather than an arbitrary infimum. -/
theorem mem_upperHull_iff_nonnegative_weights {ι ν : Type*}
    [Fintype ι] [Fintype ν] [Nonempty ι]
    (v : ι → ν → ℝ) (x : ν → ℝ) :
    x ∈ upperHull v ↔ ∀ w : ν → ℝ, (∀ j, 0 ≤ w j) →
      ∃ i, (∑ j, w j * v i j) ≤ ∑ j, w j * x j := by
  classical
  constructor
  · intro hx w hw
    obtain ⟨a,ha,hs,hax⟩ := (mem_upperHull_iff_combination v x).mp hx
    by_contra hn
    push_neg at hn
    have hsum : (∑ i, a i * ∑ j, w j * x j) <
        ∑ i, a i * ∑ j, w j * v i j := by
      have hpos : ∃ i, 0 < a i := by
        by_contra hnp
        push_neg at hnp
        have hzero : ∀ i, a i = 0 := fun i => le_antisymm (hnp i) (ha i)
        simp only [hzero, Finset.sum_const_zero] at hs
        norm_num at hs
      obtain ⟨i, hi⟩ := hpos
      apply Finset.sum_lt_sum
      · intro k hk
        exact mul_le_mul_of_nonneg_left (hn k).le (ha k)
      · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hn i) hi⟩
    have htotal : (∑ i, a i * ∑ j, w j * v i j) ≤ ∑ j, w j * x j := by
      calc
        (∑ i, a i * ∑ j, w j * v i j) = ∑ j, w j * ∑ i, a i * v i j := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ j, w j * x j := Finset.sum_le_sum
          (fun j _ => mul_le_mul_of_nonneg_left (hax j) (hw j))
    rw [← Finset.sum_mul, hs, one_mul] at hsum
    exact (not_lt_of_ge htotal) hsum
  · intro h
    by_contra hx
    obtain ⟨w, hw, hs⟩ := nonnegative_separation v x hx
    obtain ⟨i, hi⟩ := h w hw
    exact (not_lt_of_ge hi) (hs i)

end FourPapers.Symmetric.RationalPolyhedra
end
end
/- End PolytopeSeparation.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN PolytopeCeilings\n"
  logInfo "IntegralClosureTheory BEGIN PolytopeCeilings"

/- Begin PolytopeCeilings.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A finite symbolic-intersection formula

Only finitely many coordinatewise ceiling vectors occur in a bounded convex
hull of integer vertices.  These vectors convert the geometric membership
condition into a finite sum of intersections of integer threshold ideals.
The finite formula is what makes the integral closures members of the same
compatible lattice as the symbolic powers.
-/

noncomputable section
namespace FourPapers.Symmetric.RationalPolyhedra
open scoped BigOperators

def vertexMaximum {ι ν : Type*} [Fintype ι] (v : ι → ν → ℕ) : ν → ℕ :=
  fun j => Finset.univ.sup (fun i => v i j)

theorem convexHull_le_vertexMaximum {ι ν : Type*} [Fintype ι]
    (v : ι → ν → ℕ) {y : ν → ℝ}
    (hy : y ∈ convexHull ℝ (Set.range (fun i j => (v i j : ℝ)))) :
    ∀ j, y j ≤ (vertexMaximum v j : ℝ) := by
  have hsub : Set.range (fun i j => (v i j : ℝ)) ⊆
      Set.Iic (fun j => (vertexMaximum v j : ℝ)) := by
    rintro _ ⟨i,rfl⟩ j
    change (v i j : ℝ) ≤ ((Finset.univ.sup (fun i => v i j) : ℕ) : ℝ)
    exact_mod_cast (Finset.le_sup (f := fun i => v i j) (Finset.mem_univ i))
  exact convexHull_min hsub (convex_Iic _) hy

/-- All integer ceiling vectors attained by the actual real convex hull. -/
def ceilingVectors {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℕ) : Finset (ν → ℕ) := by
  classical
  exact (Finset.Iic (vertexMaximum v)).filter fun a =>
    ∃ y ∈ convexHull ℝ (Set.range (fun i j => (v i j : ℝ))),
      ∀ j, Nat.ceil (y j) = a j

theorem mem_ceilingVectors_iff {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℕ) (a : ν → ℕ) :
    a ∈ ceilingVectors v ↔
      ∃ y ∈ convexHull ℝ (Set.range (fun i j => (v i j : ℝ))),
        ∀ j, Nat.ceil (y j) = a j := by
  classical
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨y,hy,ha⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Iic.mpr ?_,y,hy,ha⟩
    intro j
    rw [← ha j]
    exact Nat.ceil_le.mpr (convexHull_le_vertexMaximum v hy j)

/-- Passing from all real points of the polytope to their attained ceiling
vectors changes no lattice join. This proves the exact equivalence with the
paper's symbolic-intersection sum indexed by the real polytope. -/
theorem ceilingVectors_sup_eq_iSup
    {ι ν β : Type*} [Fintype ι] [Fintype ν] [CompleteLattice β]
    (v : ι → ν → ℕ) (J : (ν → ℕ) → β) :
    (ceilingVectors v).sup J =
      ⨆ y ∈ convexHull ℝ (Set.range (fun i j => (v i j : ℝ))),
        J (fun j => Nat.ceil (y j)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨y,hy,hceil⟩ := (mem_ceilingVectors_iff v a).mp ha
    have he : (fun j => Nat.ceil (y j)) = a := funext hceil
    rw [← he]
    exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact Finset.le_sup (f := J)
      ((mem_ceilingVectors_iff v _).mpr ⟨y,hy,fun _ => rfl⟩)

/-- Exact finite integer reformulation of upward-hull membership. -/
theorem mem_upperHull_iff_ceilingVectors {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℕ) (x : ν → ℕ) :
    (fun j => (x j : ℝ)) ∈ upperHull (fun i j => (v i j : ℝ)) ↔
      ∃ a ∈ ceilingVectors v, a ≤ x := by
  classical
  constructor
  · rintro ⟨y,hy,hyx⟩
    refine ⟨fun j => Nat.ceil (y j),
      (mem_ceilingVectors_iff v _).mpr ⟨y,hy,fun _ => rfl⟩,?_⟩
    intro j
    exact Nat.ceil_le.mpr (hyx j)
  · rintro ⟨a,ha,hax⟩
    obtain ⟨y,hy,hceil⟩ := (mem_ceilingVectors_iff v a).mp ha
    refine ⟨y,hy,?_⟩
    intro j
    calc
      y j ≤ (Nat.ceil (y j) : ℝ) := Nat.le_ceil _
      _ = (a j : ℝ) := by rw [hceil]
      _ ≤ (x j : ℝ) := Nat.cast_le.mpr (hax j)

/-- A common adapted basis turns the polytope condition into a literal
finite lattice expression.  `J` may be the actual symbolic powers. -/
theorem ideal_eq_finite_sup_inf_of_basis_support
    {K R τ ι ν : Type*} [Field K] [CommRing R] [Algebra K R]
    [Fintype ι] [Fintype ν]
    (B : Module.Basis τ K R) (score : τ → ν → ℕ) (v : ι → ν → ℕ)
    (I : Ideal R) (J : ν → ℕ → Ideal R)
    (hI : ∀ f, f ∈ I ↔ ∀ t, B.repr f t ≠ 0 →
      (fun j => (score t j : ℝ)) ∈ upperHull (fun i j => (v i j : ℝ)))
    (hJ : ∀ j s f, f ∈ J j s ↔ ∀ t, B.repr f t ≠ 0 → s ≤ score t j) :
    I = (ceilingVectors v).sup (fun a => ⨅ j, J j (a j)) := by
  classical
  apply le_antisymm
  · intro f hf
    have hterms : ∀ t, B.repr f t ≠ 0 →
        B t ∈ (ceilingVectors v).sup (fun a => ⨅ j, J j (a j)) := by
      intro t ht
      obtain ⟨a,ha,hax⟩ := (mem_upperHull_iff_ceilingVectors v (score t)).mp
        ((hI f).mp hf t ht)
      apply (Finset.le_sup (f := fun a => ⨅ j, J j (a j)) ha)
      apply Ideal.mem_iInf.mpr
      intro j
      apply (hJ j (a j) (B t)).mpr
      intro u hu
      by_cases hut : u = t
      · subst u
        exact hax j
      · simp [Module.Basis.repr_self, Finsupp.single_apply, hut, Ne.symm hut] at hu
    have hsum : (B.repr f).sum (fun t c => c • B t) ∈
        (ceilingVectors v).sup (fun a => ⨅ j, J j (a j)) := by
      apply Submodule.sum_mem
      intro t ht
      simpa only [Algebra.smul_def] using
        ((ceilingVectors v).sup (fun a => ⨅ j, J j (a j))).mul_mem_left
          (algebraMap K R (B.repr f t)) (hterms t (Finsupp.mem_support_iff.mp ht))
    have he : (B.repr f).sum (fun t c => c • B t) = f := by
      simpa only [Finsupp.linearCombination_apply] using B.linearCombination_repr f
    exact he ▸ hsum
  · apply Finset.sup_le
    intro a ha f hf
    apply (hI f).mpr
    intro t ht
    apply (mem_upperHull_iff_ceilingVectors v (score t)).mpr
    refine ⟨a,ha,?_⟩
    intro j
    exact (hJ j (a j) f).mp (Ideal.mem_iInf.mp hf j) t ht

end FourPapers.Symmetric.RationalPolyhedra
end
end
/- End PolytopeCeilings.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN DeterminantalConvexLower\n"
  logInfo "IntegralClosureTheory BEGIN DeterminantalConvexLower"

/- Begin DeterminantalConvexLower.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Convex lower inclusion for sums of determinantal products

A cleared-denominator certificate is interpreted as a list of factors in an
ordinary ideal power.  The universal determinant-transfer theorem proves that
a power of the chosen literal minor product is integral over that power ideal.
The Rees-algebra power-root theorem then proves integrality of the product
itself.  Coefficients may be in any domain; no characteristic restriction occurs.
-/

noncomputable section
namespace FourPapers.Symmetric.DeterminantalTransfer
open scoped BigOperators
variable {R ι κ : Type*} [CommRing R]

@[simp] theorem gamma_flatten (L : List (List ℕ)) (j : ℕ) :
    gamma L.flatten j = (L.map fun s => gamma s j).sum := by
  induction L with
  | nil => simp
  | cons s L ih => simp only [List.flatten_cons, gamma_append, List.map_cons, List.sum_cons, ih]

@[simp] theorem tupleSizes_flatten (L : List (List (TupleMinor ι κ))) :
    tupleSizes L.flatten = (L.map tupleSizes).flatten := by
  simp only [tupleSizes, List.map_flatten]
  rfl

@[simp] theorem tupleProduct_flatten (X : Matrix ι κ R)
    (L : List (List (TupleMinor ι κ))) :
    tupleProduct X L.flatten = (L.map (tupleProduct X)).prod := by
  induction L with
  | nil => simp
  | cons s L ih =>
      simp only [List.flatten_cons, tupleProduct_append, List.map_cons, List.prod_cons, ih]

@[simp] theorem listMinorProductIdeal_flatten (X : Matrix ι κ R) (L : List (List ℕ)) :
    listMinorProductIdeal X L.flatten = (L.map (listMinorProductIdeal X)).prod := by
  simp only [listMinorProductIdeal, List.map_flatten, List.prod_flatten, List.map_map]
  rfl

/-- Multiply a finite list of ideals contained in `I`. -/
theorem listIdeal_prod_le_pow (I : Ideal R) (L : List (Ideal R))
    (hL : ∀ J ∈ L, J ≤ I) : L.prod ≤ I ^ L.length := by
  induction L with
  | nil => simp
  | cons J L ih =>
      rw [List.prod_cons, List.length_cons, pow_succ']
      exact Ideal.mul_mono (hL J (List.mem_cons_self ..))
        (ih (fun J hJ => hL J (List.mem_cons_of_mem _ hJ)))

/-- The basic power-root lower inclusion.  `L` is the literal list of
shapes chosen from a sum of products, with repetitions allowed. -/
theorem tupleProduct_integral_of_shape_certificate [IsDomain R]
    (X : Matrix ι κ R) (I : Ideal R) (P : List (TupleMinor ι κ))
    (L : List (List ℕ)) (hL : 0 < L.length)
    (hI : ∀ s ∈ L, listMinorProductIdeal X s ≤ I)
    (hscore : ∀ j, 1 ≤ j → gamma L.flatten j ≤ L.length * gamma (tupleSizes P) j) :
    CommAlg.IntegralOverIdeal I (tupleProduct X P) := by
  let Q := (List.replicate L.length P).flatten
  have hscores : ∀ j, 1 ≤ j → gamma L.flatten j ≤ gamma (tupleSizes Q) j := by
    intro j hj
    simpa only [Q, tupleSizes_flatten, List.map_replicate, gamma_repeat_flatten] using hscore j hj
  have hprod := tupleProduct_mem_integralClosure_product X L.flatten Q hscores
  have hle : listMinorProductIdeal X L.flatten ≤ I ^ L.length := by
    rw [listMinorProductIdeal_flatten]
    have hh := listIdeal_prod_le_pow I (L.map (listMinorProductIdeal X)) (by
      intro J hJ
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hJ
      exact hI s hs)
    simpa only [List.length_map] using hh
  have hm := CommAlg.idealIntegralClosure_mono hle hprod
  have hp : tupleProduct X Q = tupleProduct X P ^ L.length := by
    simp only [Q, tupleProduct_flatten, List.map_replicate, List.prod_replicate]
  rw [hp] at hm
  exact CommAlg.IntegralOverIdeal.of_pow hL hm

/-- A list with the specified finite multiplicities. -/
def repeatedShapes {α : Type*} [Fintype α] (sizes : α → List ℕ) (p : α → ℕ) :
    List (List ℕ) := (Finset.univ.toList.map fun i => List.replicate (p i) (sizes i)).flatten

@[simp] theorem repeatedShapes_length {α : Type*} [Fintype α]
    (sizes : α → List ℕ) (p : α → ℕ) :
    (repeatedShapes sizes p).length = ∑ i, p i := by
  classical
  simp only [repeatedShapes, List.length_flatten, List.map_map, Function.comp_def,
    List.length_replicate, Finset.sum_map_toList]

theorem mem_repeatedShapes {α : Type*} [Fintype α]
    (sizes : α → List ℕ) (p : α → ℕ) {s : List ℕ}
    (hs : s ∈ repeatedShapes sizes p) : ∃ i, s = sizes i := by
  classical
  obtain ⟨L,hL,hsL⟩ := List.mem_flatten.mp hs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hL
  exact ⟨i, (List.mem_replicate.mp hsL).2⟩

@[simp] theorem gamma_repeatedShapes {α : Type*} [Fintype α]
    (sizes : α → List ℕ) (p : α → ℕ) (j : ℕ) :
    gamma (repeatedShapes sizes p).flatten j = ∑ i, p i * gamma (sizes i) j := by
  classical
  rw [gamma_flatten]
  simp only [repeatedShapes, List.map_flatten, List.map_map, Function.comp_def,
    List.map_replicate, List.sum_flatten, List.map_map, List.sum_replicate,
    nsmul_eq_mul, Nat.cast_id, Finset.sum_map_toList]

/-- A genuine convex certificate implies integrality of any literal minor
product satisfying its complete shape-score inequalities. -/
theorem tupleProduct_integral_of_convex_scores [IsDomain R]
    {α : Type*} [Fintype α] (n : ℕ) (X : Matrix ι κ R)
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (P : List (TupleMinor ι κ))
    (hpoly : (fun j : Fin n => (gamma (tupleSizes P) (j.val+1) : ℝ)) ∈
      RationalPolyhedra.upperHull (fun i (j : Fin n) => (gamma (sizes i) (j.val+1) : ℝ))) :
    CommAlg.IntegralOverIdeal (⨆ i, listMinorProductIdeal X (sizes i)) (tupleProduct X P) := by
  classical
  obtain ⟨q,hq,p,hpq,hp⟩ := RationalPolyhedra.natural_certificate
    (fun i (j : Fin n) => gamma (sizes i) (j.val+1))
    (fun j : Fin n => gamma (tupleSizes P) (j.val+1)) hpoly
  let L := repeatedShapes sizes p
  have hlen : L.length = q := (repeatedShapes_length sizes p).trans hpq
  apply tupleProduct_integral_of_shape_certificate X _ P L (hlen.symm ▸ hq)
  · intro s hs
    obtain ⟨i,rfl⟩ := mem_repeatedShapes sizes p hs
    exact le_iSup (fun k => listMinorProductIdeal X (sizes k)) i
  · intro j hj
    rw [gamma_repeatedShapes, hlen]
    by_cases hjn : j ≤ n
    · have hh := hp ⟨j-1,by omega⟩
      have he : j - 1 + 1 = j := by omega
      simpa only [he] using hh
    · have hz : ∀ i, gamma (sizes i) j = 0 := by
        intro i
        exact gamma_eq_zero_of_le (sizes i) (hsizes i) (Nat.lt_of_not_ge hjn)
      simp only [hz,mul_zero,Finset.sum_const_zero]
      exact Nat.zero_le _

end FourPapers.Symmetric.DeterminantalTransfer
end
end
/- End DeterminantalConvexLower.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN ConvexIntegralCriterion\n"
  logInfo "IntegralClosureTheory BEGIN ConvexIntegralCriterion"

/- Begin ConvexIntegralCriterion.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
# An integral-closure criterion from a genuine minor-product basis

This is an abstract assembly theorem.  Its hypotheses are the literal
minor-product basis and exact Gram weight facts, proved in the Gram modules.
The paper endpoint instantiates every field of this interface; this file does
not assert those hypotheses without proofs.
-/

noncomputable section
namespace FourPapers.Symmetric.DeterminantalTransfer
open scoped BigOperators

variable {K R ι κ τ V : Type*} [Field K] [CommRing R] [IsDomain R]
  [Algebra K R] [DecidableEq V]

/-- Every product ideal satisfies a lower real-weight bound provided that
its actual determinant generators satisfy their individual score bounds. -/
theorem productIdeal_weight_bound (n : ℕ) (X : Matrix ι κ R)
    (φ : R →+* MvPolynomial V K) (w : V → ℝ)
    (h0 : ∀ f, CommAlg.RealWeight.Bound w 0 (φ f))
    (score : ℕ → ℝ)
    (hm : ∀ t (a : Fin t → ι) (b : Fin t → κ),
      CommAlg.RealWeight.Bound w (score t) (φ (minor X a b)))
    (sizes : List ℕ) {f : R} (hf : f ∈ listMinorProductIdeal X sizes) :
    CommAlg.RealWeight.Bound w ((sizes.map score).sum) (φ f) := by
  have oneBound (t : ℕ) : ∀ f ∈ tupleMinorIdeal X t,
      CommAlg.RealWeight.Bound w (score t) (φ f) := by
    intro f hf
    apply (show tupleMinorIdeal X t ≤ CommAlg.RealWeight.cutIdeal φ w h0 (score t) from ?_) hf
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨a,b,rfl⟩ := hg
    exact hm t a b
  induction sizes generalizing f with
  | nil => simpa only [listMinorProductIdeal,List.map_nil,List.prod_nil,List.sum_nil] using h0 f
  | cons a sizes ih =>
      change f ∈ tupleMinorIdeal X a * listMinorProductIdeal X sizes at hf
      rw [List.map_cons,List.sum_cons]
      refine Submodule.mul_induction_on (C := fun z =>
        CommAlg.RealWeight.Bound w (score a + (sizes.map score).sum) (φ z)) hf ?_ ?_
      · intro x hx y hy
        simpa only [map_mul] using (oneBound a x hx).mul (ih hy)
      · intro x y hx hy
        simpa only [map_add] using hx.add hy

/-- Literal minor-product bases with exact weighted support give the
finite-sum integral-closure formula.  Every matrix, field characteristic,
shape, and exponent remains unrestricted. -/
theorem integralOver_sum_products_iff_support
    {n : ℕ} {α : Type*} [Fintype α] [Nonempty α]
    (X : Matrix ι κ R) (B : Module.Basis τ K R)
    (factors : τ → List (TupleMinor ι κ))
    (hB : ∀ t, B t = tupleProduct X (factors t))
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (φ : R →+* MvPolynomial V K)
    (gramWeight : (Fin n → ℝ) → V → ℝ)
    (hzero : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ f, CommAlg.RealWeight.Bound (gramWeight a) 0 (φ f))
    (hminor : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ t (r : Fin t → ι) (c : Fin t → κ),
      CommAlg.RealWeight.Bound (gramWeight a)
        (2 * ∑ j, a j * (t + 1 - (j.val+1) : ℕ)) (φ (minor X r c)))
    (hbasis : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → ∀ f c,
      CommAlg.RealWeight.Bound (gramWeight a) c (φ f) ↔
        ∀ t, B.repr f t ≠ 0 → c ≤
          2 * ∑ j, a j * (gamma (tupleSizes (factors t)) (j.val+1) : ℕ))
    (f : R) :
    CommAlg.IntegralOverIdeal (⨆ i, listMinorProductIdeal X (sizes i)) f ↔
      ∀ t, B.repr f t ≠ 0 →
        (fun j : Fin n => (gamma (tupleSizes (factors t)) (j.val+1) : ℝ)) ∈
          RationalPolyhedra.upperHull (fun i (j : Fin n) =>
            (gamma (sizes i) (j.val+1) : ℝ)) := by
  classical
  let I : Ideal R := ⨆ i, listMinorProductIdeal X (sizes i)
  constructor
  · intro hf t ht
    apply (RationalPolyhedra.mem_upperHull_iff_nonnegative_weights _ _).mpr
    intro a ha
    let b : α → ℝ := fun i => ∑ j, a j * (gamma (sizes i) (j.val+1) : ℕ)
    obtain ⟨i,hiMem,hi⟩ := Finset.exists_min_image Finset.univ b (Finset.univ_nonempty)
    have hbound : ∀ g ∈ I, CommAlg.RealWeight.Bound (gramWeight a) (2 * b i) (φ g) := by
      have hle : I ≤ CommAlg.RealWeight.cutIdeal φ (gramWeight a) (hzero a ha) (2 * b i) := by
        apply iSup_le
        intro k g hg
        have hh := productIdeal_weight_bound n X φ (gramWeight a) (hzero a ha)
          (fun t => 2 * ∑ j : Fin n, a j * (t + 1 - (j.val+1) : ℕ))
          (hminor a ha) (sizes k) hg
        have score_sum (L : List ℕ) : (L.map fun t =>
            2 * ∑ j : Fin n, a j * (t + 1 - (j.val+1) : ℕ)).sum =
              2 * ∑ j : Fin n, a j * (gamma L (j.val+1) : ℕ) := by
          induction L with
          | nil => simp only [List.map_nil,List.sum_nil,gamma_nil,Nat.cast_zero,
              mul_zero,Finset.sum_const_zero]
          | cons t L ih =>
              simp only [List.map_cons,List.sum_cons,ih,gamma_cons,Nat.cast_add,
                mul_add,Finset.sum_add_distrib]
        have he := score_sum (sizes k)
        change ((sizes k).map fun t =>
          2 * ∑ j : Fin n, a j * (t + 1 - (j.val+1) : ℕ)).sum = 2 * b k at he
        rw [he] at hh
        exact hh.mono (mul_le_mul_of_nonneg_left (hi k (Finset.mem_univ k)) (by norm_num))
      exact fun g hg => hle hg
    have hclosed := CommAlg.RealWeight.bound_of_integral φ (gramWeight a) (hzero a ha)
      I (2 * b i) hbound hf
    have htbound := (hbasis a ha f (2*b i)).mp hclosed t ht
    refine ⟨i,?_⟩
    dsimp only [b] at htbound
    linarith
  · intro h
    have hterms : ∀ t, B.repr f t ≠ 0 → CommAlg.IntegralOverIdeal I (B t) := by
      intro t ht
      rw [hB]
      exact tupleProduct_integral_of_convex_scores n X sizes hsizes (factors t) (h t ht)
    have hsum : (B.repr f).sum (fun t c => c • B t) ∈ CommAlg.idealIntegralClosure I := by
      apply Submodule.sum_mem
      intro t ht
      have hm := hterms t (Finsupp.mem_support_iff.mp ht)
      simpa only [Algebra.smul_def] using
        (CommAlg.idealIntegralClosure I).mul_mem_left (algebraMap K R (B.repr f t)) hm
    have he : (B.repr f).sum (fun t c => c • B t) = f := by
      simpa only [Finsupp.linearCombination_apply] using B.linearCombination_repr f
    exact he ▸ hsum

end FourPapers.Symmetric.DeterminantalTransfer
end
end
/- End ConvexIntegralCriterion.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN SymbolicBasisSupport\n"
  logInfo "IntegralClosureTheory BEGIN SymbolicBasisSupport"

/- Begin SymbolicBasisSupport.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The minor-product basis is adapted to every symbolic power

The symbolic Gröbner theorem already supplies genuine minor-product
generators.  Their Gram weight bound proves one inclusion, and multiplication
of symbolic powers proves the other.  No Hilbert-function assumption or
characteristic-zero representation theory enters this argument.
-/

noncomputable section
open scoped BigOperators

namespace CommAlg.RealWeight

theorem bound_prod {V k α : Type*} [DecidableEq V] [CommRing k]
    (w : V → ℝ) (s : Finset α) (c : α → ℝ) (f : α → MvPolynomial V k)
    (hf : ∀ i ∈ s, Bound w (c i) (f i)) :
    Bound w (∑ i ∈ s, c i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Finset.prod_empty] using bound_one w
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end CommAlg.RealWeight

namespace FourPapers.Symmetric

variable {n : ℕ} {K : Type*} [Field K]

/-- Every ordered minor has its full, untruncated symbolic order. -/
theorem minorData_mem_symbolicPower_score (t : ℕ) (ht : 0 < t)
    (δ : MinorData n) :
    δ.polynomial K ∈ symbolicPower (determinantalIdeal n K t) (δ.size + 1 - t) := by
  letI := Rees.determinantal_prime n K t ht
  by_cases hsize : t ≤ δ.size
  · have hh := Pivot.minor_mem_symbolicPower_of_primality
      Rees.determinantal_prime K ht hsize δ.rows δ.cols
    have he : δ.size + 1 - t = δ.size - t + 1 := by omega
    simpa only [he,MinorData.polynomial] using hh
  · have he : δ.size + 1 - t = 0 := by omega
    simp only [he,symbolicPower_zero,Submodule.mem_top]

/-- A literal list product belongs to the symbolic power given by its
complete shape score; factors smaller than the symbolic index contribute zero. -/
theorem minorDataList_mem_symbolicPower_score (t : ℕ) (ht : 0 < t)
    (L : List (MinorData n)) :
    (L.map (MinorData.polynomial K)).prod ∈ symbolicPower (determinantalIdeal n K t)
      (DeterminantalTransfer.gamma (L.map MinorData.size) t) := by
  letI := Rees.determinantal_prime n K t ht
  induction L with
  | nil => simp [DeterminantalTransfer.gamma]
  | cons δ L ih =>
      simp only [List.map_cons,List.prod_cons,DeterminantalTransfer.gamma_cons]
      exact mul_mem_symbolicPower_add (determinantalIdeal n K t)
        (minorData_mem_symbolicPower_score t ht δ) ih

/-- Exact support characterization at a fixed positive symbolic index.
Every hypothesis refers either to a genuine basis or to the actual Gram
image of a polynomial. -/
theorem symbolicPower_iff_basis_support_of_weight
    {τ V : Type*} [DecidableEq V]
    (B : Module.Basis τ K (CoordinateRing n K)) (score : τ → ℕ)
    (t : ℕ) (ht : 0 < t) (htn : t ≤ n)
    (hB : ∀ u, B u ∈ symbolicPower (determinantalIdeal n K t) (score u))
    (φ : CoordinateRing n K →+* MvPolynomial V K) (w : V → ℝ)
    (hzero : ∀ f, CommAlg.RealWeight.Bound w 0 (φ f))
    (hminor : ∀ δ : MinorData n, CommAlg.RealWeight.Bound w
      (2 * (δ.size + 1 - t : ℕ)) (φ (δ.polynomial K)))
    (hbasis : ∀ f c, CommAlg.RealWeight.Bound w c (φ f) ↔
      ∀ u, B.repr f u ≠ 0 → c ≤ 2 * (score u : ℝ))
    (s : ℕ) (f : CoordinateRing n K) :
    f ∈ symbolicPower (determinantalIdeal n K t) s ↔
      ∀ u, B.repr f u ≠ 0 → s ≤ score u := by
  classical
  letI := Rees.determinantal_prime n K t ht
  by_cases hs : s = 0
  · simp only [hs,symbolicPower_zero,Submodule.mem_top,Nat.zero_le,implies_true]
  constructor
  · intro hf
    have hcut : symbolicPower (determinantalIdeal n K t) s ≤
        CommAlg.RealWeight.cutIdeal φ w hzero (2 * (s : ℝ)) := by
      rw [(Rees.full_symbolic_groebner n K t s ht htn (Nat.pos_of_ne_zero hs)).ideal_eq_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨k,δ,hδ,hscore,rfl⟩
      have hp := CommAlg.RealWeight.bound_prod w Finset.univ
        (fun j => 2 * ((δ j).size + 1 - t : ℕ))
        (fun j => φ ((δ j).polynomial K)) (fun j _ => hminor (δ j))
      have he : (∑ j : Fin k, 2 * ((δ j).size + 1 - t : ℕ) : ℝ) = 2 * (s : ℝ) := by
        have hsize (j : Fin k) : (δ j).size + 1 - t = (δ j).size - t + 1 := by
          have := hδ j
          omega
        simp_rw [hsize]
        rw [← Finset.mul_sum, ← Nat.cast_sum, hscore]
      change CommAlg.RealWeight.Bound w (2 * (s : ℝ))
        (φ (∏ j, (δ j).polynomial K))
      simpa only [map_prod,he] using hp
    intro u hu
    have hh := (hbasis f (2 * (s : ℝ))).mp (hcut hf) u hu
    have hreal : (s : ℝ) ≤ score u := by linarith
    exact_mod_cast hreal
  · intro hf
    have hsum : (B.repr f).sum (fun u c => c • B u) ∈
        symbolicPower (determinantalIdeal n K t) s := by
      apply Submodule.sum_mem
      intro u hu
      have hmem := symbolicPower_antitone (determinantalIdeal n K t)
        (hf u (Finsupp.mem_support_iff.mp hu)) (hB u)
      simpa only [Algebra.smul_def] using
        (symbolicPower (determinantalIdeal n K t) s).mul_mem_left
          (algebraMap K (CoordinateRing n K) (B.repr f u)) hmem
    have he : (B.repr f).sum (fun t c => c • B t) = f := by
      simpa only [Finsupp.linearCombination_apply] using B.linearCombination_repr f
    exact he ▸ hsum

end FourPapers.Symmetric
end
end
/- End SymbolicBasisSupport.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN SymmetricClosureBridge\n"
  logInfo "IntegralClosureTheory BEGIN SymmetricClosureBridge"

/- Begin SymmetricClosureBridge.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
# From the genuine symmetric minor basis to the closure formula

This file joins the universal determinant-transfer and convex arguments to
the original symmetric determinantal ideals.  The remaining interface is
the actual minor-product basis and its proved Gram weight description.
Instantiation by the Gram basis yields the complete finite symbolic-power
formula used in Corollary 7.2.
-/

noncomputable section
namespace FourPapers.Symmetric
open scoped BigOperators

def MinorData.toTupleMinor {n : ℕ} (δ : MinorData n) :
    DeterminantalTransfer.TupleMinor (Fin n) (Fin n) :=
  ⟨δ.size,δ.rows,δ.cols⟩

@[simp] theorem MinorData.toTupleMinor_size {n : ℕ} (δ : MinorData n) :
    δ.toTupleMinor.size = δ.size := rfl

@[simp] theorem MinorData.toTupleMinor_value {n : ℕ} (R : Type*) [CommRing R]
    (δ : MinorData n) : δ.toTupleMinor.value (genericMatrix n R) = δ.polynomial R := rfl

@[simp] theorem tupleSizes_minorData {n : ℕ} (L : List (MinorData n)) :
    DeterminantalTransfer.tupleSizes (L.map MinorData.toTupleMinor) = L.map MinorData.size := by
  simp only [DeterminantalTransfer.tupleSizes,List.map_map,Function.comp_def,
    MinorData.toTupleMinor_size]

@[simp] theorem tupleProduct_minorData {n : ℕ} (R : Type*) [CommRing R]
    (L : List (MinorData n)) :
    DeterminantalTransfer.tupleProduct (genericMatrix n R) (L.map MinorData.toTupleMinor) =
      (L.map (MinorData.polynomial R)).prod := by
  simp only [DeterminantalTransfer.tupleProduct,List.map_map,Function.comp_def,
    MinorData.toTupleMinor_value]

theorem tupleMinorIdeal_generic_eq (n : ℕ) (R : Type*) [CommRing R] (t : ℕ) :
    DeterminantalTransfer.tupleMinorIdeal (genericMatrix n R) t = determinantalIdeal n R t := by
  rw [determinantalIdeal_eq_matrixMinorIdeal]
  unfold DeterminantalTransfer.tupleMinorIdeal matrixMinorIdeal
  congr 1
  ext f
  simp only [Set.mem_setOf_eq,DeterminantalTransfer.minor,eq_comm]

namespace IntegralClosure

def shapeProductIdeal (n : ℕ) (R : Type*) [CommRing R] (sizes : List ℕ) :
    Ideal (CoordinateRing n R) := (sizes.map (determinantalIdeal n R)).prod

def shapeSumIdeal {α : Type*} (n : ℕ) (R : Type*) [CommRing R]
    (sizes : α → List ℕ) : Ideal (CoordinateRing n R) :=
  ⨆ i, shapeProductIdeal n R (sizes i)

theorem listMinorProductIdeal_generic_eq (n : ℕ) (R : Type*) [CommRing R]
    (sizes : List ℕ) :
    DeterminantalTransfer.listMinorProductIdeal (genericMatrix n R) sizes =
      shapeProductIdeal n R sizes := by
  unfold DeterminantalTransfer.listMinorProductIdeal shapeProductIdeal
  congr 1
  apply List.map_congr_left
  intro a ha
  exact tupleMinorIdeal_generic_eq n R a

variable {n : ℕ} {K τ V α : Type*} [Field K] [DecidableEq V]
  [Fintype α] [Nonempty α]

theorem closure_support_of_minor_basis
    (B : Module.Basis τ K (CoordinateRing n K))
    (factors : τ → List (MinorData n))
    (hB : ∀ t, B t = ((factors t).map (MinorData.polynomial K)).prod)
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (φ : CoordinateRing n K →+* MvPolynomial V K)
    (weight : (Fin n → ℝ) → V → ℝ)
    (hzero : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ f, CommAlg.RealWeight.Bound (weight a) 0 (φ f))
    (hminor : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ t (r c : Fin t → Fin n), CommAlg.RealWeight.Bound (weight a)
        (2 * ∑ j, a j * (t + 1 - (j.val+1) : ℕ))
          (φ ((genericMatrix n K).submatrix r c).det))
    (hbasis : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → ∀ f c,
      CommAlg.RealWeight.Bound (weight a) c (φ f) ↔
        ∀ t, B.repr f t ≠ 0 → c ≤ 2 * ∑ j, a j *
          (DeterminantalTransfer.gamma ((factors t).map MinorData.size) (j.val+1) : ℕ))
    (f : CoordinateRing n K) :
    f ∈ CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) ↔
      ∀ t, B.repr f t ≠ 0 →
        (fun j : Fin n =>
          (DeterminantalTransfer.gamma ((factors t).map MinorData.size) (j.val+1) : ℝ)) ∈
          RationalPolyhedra.upperHull (fun i (j : Fin n) =>
            (DeterminantalTransfer.gamma (sizes i) (j.val+1) : ℝ)) := by
  have hh := DeterminantalTransfer.integralOver_sum_products_iff_support
    (genericMatrix n K) B (fun t => (factors t).map MinorData.toTupleMinor)
    (by intro t; simpa only [tupleProduct_minorData] using hB t)
    sizes hsizes φ weight hzero hminor
    (by simpa only [tupleSizes_minorData] using hbasis) f
  simpa only [shapeSumIdeal,listMinorProductIdeal_generic_eq,tupleSizes_minorData,
    CommAlg.mem_idealIntegralClosure] using hh

/-- The full finite symbolic-intersection formula, with every scalar,
matrix size, symbolic exponent, and shape range retained. -/
theorem closure_eq_finite_symbolic_lattice_of_minor_basis
    (B : Module.Basis τ K (CoordinateRing n K))
    (factors : τ → List (MinorData n))
    (hB : ∀ t, B t = ((factors t).map (MinorData.polynomial K)).prod)
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (φ : CoordinateRing n K →+* MvPolynomial V K)
    (weight : (Fin n → ℝ) → V → ℝ)
    (hzero : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ f, CommAlg.RealWeight.Bound (weight a) 0 (φ f))
    (hminor : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) →
      ∀ t (r c : Fin t → Fin n), CommAlg.RealWeight.Bound (weight a)
        (2 * ∑ j, a j * (t + 1 - (j.val+1) : ℕ))
          (φ ((genericMatrix n K).submatrix r c).det))
    (hbasis : ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → ∀ f c,
      CommAlg.RealWeight.Bound (weight a) c (φ f) ↔
        ∀ t, B.repr f t ≠ 0 → c ≤ 2 * ∑ j, a j *
          (DeterminantalTransfer.gamma ((factors t).map MinorData.size) (j.val+1) : ℕ)) :
    CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) =
      (RationalPolyhedra.ceilingVectors (fun i (j : Fin n) =>
        DeterminantalTransfer.gamma (sizes i) (j.val+1))).sup
          (fun a => ⨅ j : Fin n, symbolicPower (determinantalIdeal n K (j.val+1)) (a j)) := by
  classical
  apply RationalPolyhedra.ideal_eq_finite_sup_inf_of_basis_support B
    (fun t (j : Fin n) => DeterminantalTransfer.gamma ((factors t).map MinorData.size) (j.val+1))
    (fun i (j : Fin n) => DeterminantalTransfer.gamma (sizes i) (j.val+1))
    _ (fun j s => symbolicPower (determinantalIdeal n K (j.val+1)) s)
  · exact closure_support_of_minor_basis B factors hB sizes hsizes φ weight hzero hminor hbasis
  · intro j s f
    let a : Fin n → ℝ := Pi.single j 1
    have ha : ∀ k, 0 ≤ a k := by
      intro k
      simp only [a,Pi.single_apply]
      split_ifs <;> norm_num
    apply symbolicPower_iff_basis_support_of_weight B
      (fun t => DeterminantalTransfer.gamma ((factors t).map MinorData.size) (j.val+1))
      (j.val+1) (by omega) (by omega) _ φ (weight a) (hzero a ha) _ _ s f
    · intro t
      rw [hB]
      exact minorDataList_mem_symbolicPower_score (j.val+1) (by omega) (factors t)
    · intro δ
      simpa only [a,Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',
        Finset.mem_univ,if_pos,MinorData.polynomial,minor] using
        hminor a ha δ.size δ.rows δ.cols
    · intro g c
      simpa only [a,Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',
        Finset.mem_univ,if_pos] using hbasis a ha g c

end IntegralClosure
end FourPapers.Symmetric
end
end
/- End SymmetricClosureBridge.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "IntegralClosureTheory BEGIN BoundedMixedLattice\n"
  logInfo "IntegralClosureTheory BEGIN BoundedMixedLattice"

/- Begin BoundedMixedLattice.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The compatible lattice with its empty intersection

Symbolic exponent zero means the whole ring.  We therefore adjoin the
empty intersection to the existing finite lattice expressions.  This also
handles an empty partition faithfully.  All operations are actual ideal
operations; their monomial sets and integral models are proved compatible
with the same simultaneous triangular basis already constructed in the core.
-/

noncomputable section
namespace FourPapers.Symmetric.BoundedLattice
open MvPolynomial Simultaneous Module
open scoped BigOperators

abbrev Expr (n : ℕ) := Option (MixedLatticeExpression n)

def ideal {n : ℕ} : Expr n → Ideal (CoordinateRing n ℤ)
  | none => ⊤
  | some e => e.ideal

def fieldIdeal {n : ℕ} (K : Type*) [Field K] : Expr n → Ideal (CoordinateRing n K)
  | none => ⊤
  | some e => e.fieldIdeal K

def baseChangedIdeal {n : ℕ} (R : Type*) [CommRing R] : Expr n → Ideal (CoordinateRing n R)
  | none => ⊤
  | some e => e.baseChangedIdeal R

def monomials {n : ℕ} : Expr n → Set (Entry n →₀ ℕ)
  | none => Set.univ
  | some e => e.monomials

def sup {n : ℕ} : Expr n → Expr n → Expr n
  | some e, some f => some (.sup e f)
  | _, _ => none

def inf {n : ℕ} : Expr n → Expr n → Expr n
  | none, f => f
  | e, none => e
  | some e, some f => some (.inf e f)

@[simp] theorem ideal_sup {n : ℕ} (e f : Expr n) :
    ideal (sup e f) = ideal e ⊔ ideal f := by
  cases e <;> cases f <;> simp [sup,ideal,MixedLatticeExpression.ideal]

@[simp] theorem ideal_inf {n : ℕ} (e f : Expr n) :
    ideal (inf e f) = ideal e ⊓ ideal f := by
  cases e <;> cases f <;> simp [inf,ideal,MixedLatticeExpression.ideal]

@[simp] theorem fieldIdeal_sup {n : ℕ} (K : Type*) [Field K] (e f : Expr n) :
    fieldIdeal K (sup e f) = fieldIdeal K e ⊔ fieldIdeal K f := by
  cases e <;> cases f <;> simp [sup,fieldIdeal,MixedLatticeExpression.fieldIdeal]

@[simp] theorem fieldIdeal_inf {n : ℕ} (K : Type*) [Field K] (e f : Expr n) :
    fieldIdeal K (inf e f) = fieldIdeal K e ⊓ fieldIdeal K f := by
  cases e <;> cases f <;> simp [inf,fieldIdeal,MixedLatticeExpression.fieldIdeal]

@[simp] theorem monomials_sup {n : ℕ} (e f : Expr n) :
    monomials (sup e f) = monomials e ∪ monomials f := by
  cases e <;> cases f <;> simp [sup,monomials,MixedLatticeExpression.monomials]

@[simp] theorem monomials_inf {n : ℕ} (e f : Expr n) :
    monomials (inf e f) = monomials e ∩ monomials f := by
  cases e <;> cases f <;> simp [inf,monomials,MixedLatticeExpression.monomials]

def bottomDatum (n : ℕ) : MixedDatum n where
  rank := fun _ _ => n
  symmetric := fun _ _ => rfl
  conditions := []
  valid := by intro ts h; simp at h

def bottom (n : ℕ) : Expr n := some (.atom (bottomDatum n))

/-- Northwest rank conditions are atoms of the same lattice. -/
def northwest {n : ℕ} (r : RankArray n) (hr : ∀ i j, r i j = r j i) : Expr n :=
  some (.atom {
    rank := r
    symmetric := hr
    conditions := []
    valid := by intro ts h; simp at h })

@[simp] theorem fieldIdeal_northwest {n : ℕ} (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i) :
    fieldIdeal K (northwest r hr) = northwestIdeal K r := by
  simp [northwest,fieldIdeal,MixedLatticeExpression.fieldIdeal,mixedIdeal]

@[simp] theorem ideal_bottom (n : ℕ) : ideal (bottom n) = ⊥ := by
  simp [bottom,ideal,MixedLatticeExpression.ideal,mixedIntegralSpan,bottomDatum,
    mixedGenerators,Schur.northwestGenerators_unconstrained]

@[simp] theorem fieldIdeal_bottom (n : ℕ) (K : Type*) [Field K] :
    fieldIdeal K (bottom n) = ⊥ := by
  simp [bottom,fieldIdeal,MixedLatticeExpression.fieldIdeal,bottomDatum,mixedIdeal,
    Schur.northwestIdeal_unconstrained]

@[simp] theorem monomials_bottom (n : ℕ) : monomials (bottom n) = ∅ := by
  change ((foldedOrder n).standardMonomials (ideal (bottom n)))ᶜ = ∅
  rw [ideal_bottom]
  ext m
  simp [MonomialOrder.standardMonomials]

theorem baseChangedIdeal_eq_map {n : ℕ} (R : Type*) [CommRing R] (e : Expr n) :
    baseChangedIdeal R e = (ideal e).map (MvPolynomial.map (Int.castRingHom R)) := by
  cases e with
  | none => simp [baseChangedIdeal,ideal,Ideal.map_top]
  | some e => exact mixed_lattice_baseChange R e

theorem baseChangedIdeal_eq_fieldIdeal {n : ℕ} (K : Type*) [Field K] (e : Expr n) :
    baseChangedIdeal K e = fieldIdeal K e := by
  cases e with
  | none => rfl
  | some e => exact e.baseChangedIdeal_eq_fieldIdeal K

/-- The integer model is functorial for every map of coefficient rings. -/
theorem baseChangedIdeal_map {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (e : Expr n) :
    (baseChangedIdeal A e).map (MvPolynomial.map φ) = baseChangedIdeal B e := by
  cases e with
  | none => simp [baseChangedIdeal,Ideal.map_top]
  | some e => exact mixed_lattice_baseChange_hom φ e

/-- Arbitrary coefficient change preserves these actual intersections. -/
theorem baseChangedIdeal_map_inf {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (e f : Expr n) :
    (baseChangedIdeal A e ⊓ baseChangedIdeal A f).map (MvPolynomial.map φ) =
      (baseChangedIdeal A e).map (MvPolynomial.map φ) ⊓
        (baseChangedIdeal A f).map (MvPolynomial.map φ) := by
  cases e <;> cases f <;>
    simp [baseChangedIdeal,Ideal.map_top,mixed_lattice_map_inf]

theorem baseChangedIdeal_map_sup {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (e f : Expr n) :
    (baseChangedIdeal A e ⊔ baseChangedIdeal A f).map (MvPolynomial.map φ) =
      (baseChangedIdeal A e).map (MvPolynomial.map φ) ⊔
        (baseChangedIdeal A f).map (MvPolynomial.map φ) := Ideal.map_sup _ _ _

theorem adapted {n : ℕ}
    (b : Basis (Entry n →₀ ℕ) ℤ (CoordinateRing n ℤ))
    (hb : ∀ D : MixedDatum n, (mixedIntegralSpan D).restrictScalars ℤ =
      coordinateSpan b ((foldedOrder n).standardMonomials (mixedIntegralSpan D))ᶜ)
    (e : Expr n) : (ideal e).restrictScalars ℤ = coordinateSpan b (monomials e) := by
  cases e with
  | none => simp [ideal,monomials,coordinateSpan,Set.image_univ,b.span_eq]
  | some e => exact e.adapted b hb

theorem baseChanged_adapted {n : ℕ} (R : Type*) [CommRing R]
    (b : Basis (Entry n →₀ ℕ) ℤ (CoordinateRing n ℤ))
    (hb : ∀ D : MixedDatum n, (mixedIntegralSpan D).restrictScalars ℤ =
      coordinateSpan b ((foldedOrder n).standardMonomials (mixedIntegralSpan D))ᶜ)
    (e : Expr n) :
    (baseChangedIdeal R e).restrictScalars R =
      coordinateSpan (coefficientBasis (S := R) b) (monomials e) := by
  rw [baseChangedIdeal_eq_map]
  exact coordinate_ideal_map (S := R) b (ideal e) (monomials e) (adapted b hb e)

/-- One integral homogeneous triangular basis simultaneously adapts to
every bounded lattice expression, hence jointly to northwest ideals,
symbolic powers, and all closure expressions in Corollary 7.2. -/
theorem exists_integral_simultaneous_basis (n : ℕ) :
    ∃ b : Basis (Entry n →₀ ℕ) ℤ (CoordinateRing n ℤ),
      (∀ m, (b m).coeff m = 1 ∧
        (b m).IsWeightedHomogeneous (fun _ : Entry n => (1 : ℕ))
          (Finsupp.weight (fun _ : Entry n => (1 : ℕ)) m) ∧
        (foldedOrder n).toSyn ((foldedOrder n).degree (b m)) ≤ (foldedOrder n).toSyn m) ∧
      ∀ e : Expr n, (ideal e).restrictScalars ℤ = coordinateSpan b (monomials e) := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  exact ⟨b,hb,adapted b hspan⟩

theorem initial_sup {n : ℕ} (K : Type*) [Field K] (e f : Expr n) :
    initialIdeal K (fieldIdeal K e ⊔ fieldIdeal K f) =
      initialIdeal K (fieldIdeal K e) ⊔ initialIdeal K (fieldIdeal K f) := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  have he := baseChanged_adapted K b hspan e
  have hf := baseChanged_adapted K b hspan f
  rw [baseChangedIdeal_eq_fieldIdeal] at he hf
  exact triangular_ideals_initial_sup (foldedOrder n) (coefficientBasis (S := K) b)
    (coefficientBasis_triangular K b (fun m => ⟨(hb m).1,(hb m).2.2⟩))
    _ _ _ _ he hf

theorem initial_inf {n : ℕ} (K : Type*) [Field K] (e f : Expr n) :
    initialIdeal K (fieldIdeal K e ⊓ fieldIdeal K f) =
      initialIdeal K (fieldIdeal K e) ⊓ initialIdeal K (fieldIdeal K f) := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  have he := baseChanged_adapted K b hspan e
  have hf := baseChanged_adapted K b hspan f
  rw [baseChangedIdeal_eq_fieldIdeal] at he hf
  exact triangular_ideals_initial_inf (foldedOrder n) (coefficientBasis (S := K) b)
    (coefficientBasis_triangular K b (fun m => ⟨(hb m).1,(hb m).2.2⟩))
    _ _ _ _ he hf

theorem coefficient_change_inf {n : ℕ} (R : Type*) [CommRing R] (e f : Expr n) :
    (ideal e ⊓ ideal f).map (MvPolynomial.map (Int.castRingHom R)) =
      (ideal e).map (MvPolynomial.map (Int.castRingHom R)) ⊓
        (ideal f).map (MvPolynomial.map (Int.castRingHom R)) := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  exact coordinate_ideals_map_inf (S := R) b (ideal e) (ideal f)
    (monomials e) (monomials f) (adapted b hspan e) (adapted b hspan f)

theorem coefficient_change_sup {n : ℕ} (R : Type*) [CommRing R] (e f : Expr n) :
    (ideal e ⊔ ideal f).map (MvPolynomial.map (Int.castRingHom R)) =
      (ideal e).map (MvPolynomial.map (Int.castRingHom R)) ⊔
        (ideal f).map (MvPolynomial.map (Int.castRingHom R)) := Ideal.map_sup _ _ _

/-- Distributivity is an equality of the actual integral ideals. -/
theorem integral_distributive {n : ℕ} (e f g : Expr n) :
    ideal e ⊓ (ideal f ⊔ ideal g) =
      (ideal e ⊓ ideal f) ⊔ (ideal e ⊓ ideal g) := by
  cases e <;> cases f <;> cases g <;>
    simp [ideal,mixed_integral_lattice_distributive]

/-- The same distributive lattice is retained over every coefficient ring. -/
theorem baseChanged_distributive {n : ℕ} (R : Type*) [CommRing R]
    (e f g : Expr n) :
    baseChangedIdeal R e ⊓ (baseChangedIdeal R f ⊔ baseChangedIdeal R g) =
      (baseChangedIdeal R e ⊓ baseChangedIdeal R f) ⊔
        (baseChangedIdeal R e ⊓ baseChangedIdeal R g) := by
  cases e <;> cases f <;> cases g <;>
    simp [baseChangedIdeal,mixed_lattice_distributive_after_baseChange]

theorem field_distributive {n : ℕ} (K : Type*) [Field K] (e f g : Expr n) :
    fieldIdeal K e ⊓ (fieldIdeal K f ⊔ fieldIdeal K g) =
      (fieldIdeal K e ⊓ fieldIdeal K f) ⊔ (fieldIdeal K e ⊓ fieldIdeal K g) := by
  cases e <;> cases f <;> cases g <;>
    simp [fieldIdeal,mixed_field_lattice_distributive]

theorem monomials_upper {n : ℕ} (e : Expr n) : IsUpperSet (monomials e) := by
  cases e with
  | none => exact isUpperSet_univ
  | some e =>
      induction e with
      | atom D =>
          intro a b hab ha hb
          apply ha
          intro p hp hp0 hpa
          exact hb p hp hp0 (hpa.trans hab)
      | sup e f he hf => exact he.union hf
      | inf e f he hf => exact he.inter hf

/-- The exponent sets record literal monomial membership in initial ideals. -/
theorem monomial_mem_initial_iff {n : ℕ} (K : Type*) [Field K]
    (e : Expr n) (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K (fieldIdeal K e) ↔ m ∈ monomials e := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  have had := baseChanged_adapted K b hspan e
  rw [baseChangedIdeal_eq_fieldIdeal] at had
  have htri := coefficientBasis_triangular K b (fun a => ⟨(hb a).1,(hb a).2.2⟩)
  have he := triangular_ideal_initial (foldedOrder n)
    (coefficientBasis (S := K) b) htri (fieldIdeal K e) (monomials e) had
  change monomial m (1 : K) ∈ orderInitialIdeal (foldedOrder n) (fieldIdeal K e) ↔ _
  rw [he]
  constructor
  · intro hm
    obtain ⟨d,hd,hdm⟩ := mem_ideal_span_monomial_image.mp hm m (by simp)
    exact monomials_upper e hdm hd
  · intro hm
    exact Ideal.subset_span ⟨m,hm,rfl⟩

/-- The same integral model has a free quotient after every coefficient change. -/
theorem quotient_free {n : ℕ} (R : Type*) [CommRing R] (e : Expr n) :
    Module.Free R (CoordinateRing n R ⧸ baseChangedIdeal R e) := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  rw [baseChangedIdeal_eq_map]
  exact coordinate_ideal_map_quotient_free (S := R) b (ideal e) (monomials e)
    (adapted b hspan e)

theorem standard_monomial_basis {n : ℕ} (R : Type*) [CommRing R] (e : Expr n) :
    let v : (foldedOrder n).standardMonomials (ideal e) →
        CoordinateRing n R ⧸ baseChangedIdeal R e :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  obtain ⟨b,hb,hspan⟩ := all_mixed_integral_simultaneous_basis n
  have htri : ∀ a, (b a).coeff a = 1 ∧
      (foldedOrder n).toSyn ((foldedOrder n).degree (b a)) ≤ (foldedOrder n).toSyn a :=
    fun a => ⟨(hb a).1,(hb a).2.2⟩
  have hG := triangular_ideal_groebner (foldedOrder n) b htri (ideal e) (monomials e)
    (adapted b hspan e)
  have hu : ∀ g ∈ b '' monomials e, g ≠ 0 → IsUnit ((foldedOrder n).leadingCoeff g) := by
    rintro _ ⟨a,ha,rfl⟩ hg
    rw [triangular_basis_leadingCoeff (foldedOrder n) b htri]
    exact isUnit_one
  have hh := hG.fixed_standard_basis_after_basechange (Int.castRingHom R) hu
  rw [baseChangedIdeal_eq_map]
  exact hh

def meetFamily {n : ℕ} {α : Type*} (f : α → Expr n) : List α → Expr n
  | [] => none
  | a :: L => inf (f a) (meetFamily f L)

def joinFamily {n : ℕ} {α : Type*} (f : α → Expr n) : List α → Expr n
  | [] => bottom n
  | a :: L => sup (f a) (joinFamily f L)

theorem mem_fieldIdeal_meetFamily {n : ℕ} {α : Type*}
    (K : Type*) [Field K] (f : α → Expr n) (L : List α) (p : CoordinateRing n K) :
    p ∈ fieldIdeal K (meetFamily f L) ↔ ∀ a ∈ L, p ∈ fieldIdeal K (f a) := by
  induction L with
  | nil => simp [meetFamily,fieldIdeal]
  | cons a L ih => simp [meetFamily,fieldIdeal_inf,ih]

theorem fieldIdeal_joinFamily {n : ℕ} {α : Type*} [DecidableEq α]
    (K : Type*) [Field K] (f : α → Expr n) (L : List α) :
    fieldIdeal K (joinFamily f L) = L.toFinset.sup (fun a => fieldIdeal K (f a)) := by
  induction L with
  | nil => simp [joinFamily]
  | cons a L ih => simp [joinFamily,fieldIdeal_sup,ih]

theorem mem_monomials_meetFamily {n : ℕ} {α : Type*}
    (f : α → Expr n) (L : List α) (m : Entry n →₀ ℕ) :
    m ∈ monomials (meetFamily f L) ↔ ∀ a ∈ L, m ∈ monomials (f a) := by
  induction L with
  | nil => simp [meetFamily,monomials]
  | cons a L ih => simp [meetFamily,monomials_inf,ih]

theorem mem_monomials_joinFamily {n : ℕ} {α : Type*}
    (f : α → Expr n) (L : List α) (m : Entry n →₀ ℕ) :
    m ∈ monomials (joinFamily f L) ↔ ∃ a ∈ L, m ∈ monomials (f a) := by
  induction L with
  | nil => simp [joinFamily]
  | cons a L ih => simp [joinFamily,monomials_sup,ih]

/-- A symbolic power as an actual compatible-lattice expression, including
exponent zero. -/
def symbolic {n : ℕ} (j : Fin n) (s : ℕ) : Expr n :=
  if hs : s = 0 then none else some (.atom {
    rank := fun _ _ => n
    symmetric := fun _ _ => rfl
    conditions := [(j.val+1,s)]
    valid := by
      intro ts hts
      have he : ts = (j.val+1,s) := by simpa using hts
      subst ts
      exact ⟨by omega,by omega,by omega⟩ })

theorem fieldIdeal_symbolic {n : ℕ} (K : Type*) [Field K]
    (j : Fin n) (s : ℕ) :
    fieldIdeal K (symbolic j s) = symbolicPower (determinantalIdeal n K (j.val+1)) s := by
  letI := Rees.determinantal_prime n K (j.val+1) (by omega)
  by_cases hs : s = 0
  · simp [symbolic,hs,fieldIdeal]
  · simp [symbolic,hs,fieldIdeal,MixedLatticeExpression.fieldIdeal,mixedIdeal,
      Schur.northwestIdeal_unconstrained]

theorem mem_monomials_symbolic {n : ℕ} (j : Fin n) (s : ℕ) (m : Entry n →₀ ℕ) :
    m ∈ monomials (symbolic j s) ↔ s ≤ gamma (j.val+1) m := by
  by_cases hs : s = 0
  · simp [symbolic,hs,monomials]
  · rw [← monomial_mem_initial_iff ℚ,fieldIdeal_symbolic]
    exact Schur.corollary_5_3_monomial n ℚ (j.val+1) s
      (by omega) (by omega) (by omega) m

/-- The common Rees-style degeneration, with the zero quotient as the
degeneration of the whole ring ideal. -/
def deformation {n : ℕ} : Expr n → Ideal (CoordinateRing n (Polynomial ℤ))
  | none => ⊤
  | some e => Deformation.latticeDeformation e

@[simp] theorem deformation_sup {n : ℕ} (e f : Expr n) :
    deformation (sup e f) = deformation e ⊔ deformation f := by
  cases e <;> cases f <;> simp [sup,deformation,Deformation.latticeDeformation]

@[simp] theorem deformation_inf {n : ℕ} (e f : Expr n) :
    deformation (inf e f) = deformation e ⊓ deformation f := by
  cases e <;> cases f <;> simp [inf,deformation,Deformation.latticeDeformation]

theorem deformation_adapted {n : ℕ}
    (b : Basis (Entry n →₀ ℕ) (Polynomial ℤ) (CoordinateRing n (Polynomial ℤ)))
    (hb : ∀ D : MixedDatum n,
      (Deformation.deformedMixedIdeal D).restrictScalars (Polynomial ℤ) =
        coordinateSpan b ((foldedOrder n).standardMonomials (mixedIntegralSpan D))ᶜ)
    (e : Expr n) :
    (deformation e).restrictScalars (Polynomial ℤ) = coordinateSpan b (monomials e) := by
  cases e with
  | none => simp [deformation,monomials,coordinateSpan,Set.image_univ,b.span_eq]
  | some e => exact Deformation.latticeDeformation_adapted b hb e

theorem deformation_free {n : ℕ} (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e : Expr n) :
    Module.Free R (CoordinateRing n R ⧸ (deformation e).map (MvPolynomial.map φ)) := by
  letI : Algebra (Polynomial ℤ) R := φ.toAlgebra
  obtain ⟨b,hb,hspan⟩ := Deformation.deformed_simultaneous_basis n
  exact coordinate_ideal_map_quotient_free (S := R) b (deformation e) (monomials e)
    (deformation_adapted b hspan e)

theorem deformation_flat {n : ℕ} (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e : Expr n) :
    Module.Flat R (CoordinateRing n R ⧸ (deformation e).map (MvPolynomial.map φ)) := by
  letI := deformation_free R φ e
  infer_instance

theorem deformation_at_one {n : ℕ} (e : Expr n) :
    (deformation e).map (Deformation.specialization 1) = ideal e := by
  cases e with
  | none => simp [deformation,ideal,Ideal.map_top]
  | some e => exact Deformation.latticeDeformation_at_one e

theorem orderInitialIdeal_top {σ R : Type*} [CommRing R]
    (m : MonomialOrder σ) : orderInitialIdeal m (⊤ : Ideal (MvPolynomial σ R)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hh : m.leadingTerm (1 : MvPolynomial σ R) ∈ orderInitialIdeal m ⊤ :=
    Ideal.subset_span ⟨1,Submodule.mem_top,rfl⟩
  simpa using hh

theorem deformation_at_zero {n : ℕ} (e : Expr n) :
    (deformation e).map (Deformation.specialization 0) =
      orderInitialIdeal (foldedOrder n) (ideal e) := by
  cases e with
  | none => simp [deformation,ideal,orderInitialIdeal_top,Ideal.map_top]
  | some e => exact Deformation.latticeDeformation_at_zero e

/-- A monic Gröbner basis for every expression in the common family. -/
theorem deformation_groebner {n : ℕ} (e : Expr n) :
    ∃ G : Set (CoordinateRing n (Polynomial ℤ)),
      (foldedOrder n).IsGroebnerBasis G (deformation e) ∧
        ∀ g ∈ G, g ≠ 0 → IsUnit ((foldedOrder n).leadingCoeff g) := by
  obtain ⟨b,hb,hspan⟩ := Deformation.deformed_simultaneous_basis n
  refine ⟨b '' monomials e,
    triangular_ideal_groebner (foldedOrder n) b hb (deformation e) (monomials e)
      (deformation_adapted b hspan e), ?_⟩
  rintro _ ⟨a,ha,rfl⟩ hg
  rw [triangular_basis_leadingCoeff (foldedOrder n) b hb]
  exact isUnit_one

theorem deformation_standardMonomials {n : ℕ} (e : Expr n) :
    (foldedOrder n).standardMonomials (deformation e) =
      (foldedOrder n).standardMonomials (ideal e) := by
  obtain ⟨G,hG,hu⟩ := deformation_groebner e
  have h := hG.standardMonomials_map_of_unit_leading (Polynomial.evalRingHom (1 : ℤ)) hu
  rw [show MvPolynomial.map (Polynomial.evalRingHom (1 : ℤ)) =
    Deformation.specialization 1 from rfl,deformation_at_one] at h
  exact h.symm

/-- The same literal standard monomial residue classes form a basis in
all coefficient specializations of the common family. -/
theorem deformation_standard_basis {n : ℕ} (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e : Expr n) :
    let I := (deformation e).map (MvPolynomial.map φ)
    let v : (foldedOrder n).standardMonomials (ideal e) → CoordinateRing n R ⧸ I :=
      fun a => Ideal.Quotient.mk I (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  obtain ⟨G,hG,hu⟩ := deformation_groebner e
  have h := hG.fixed_standard_basis_after_basechange φ hu
  rw [deformation_standardMonomials e] at h
  exact h

/-- Every invertible fiber is the specified diagonal variable rescaling. -/
theorem deformation_map_unit {n : ℕ} {R : Type*} [CommRing R]
    (φ : Polynomial ℤ →+* R) (x : Rˣ)
    (hx : φ Polynomial.X = (x : R)) (e : Expr n) :
    (deformation e).map (MvPolynomial.map φ) =
      (baseChangedIdeal R e).map
        (Deformation.variableScaling (fun i : Entry n => x ^ Deformation.entryWeight i)).toRingHom := by
  cases e with
  | none => simp [deformation,baseChangedIdeal,Ideal.map_top]
  | some e => exact Deformation.latticeDeformation_map_unit φ x hx e

theorem deformation_map_sup {n : ℕ} (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e f : Expr n) :
    (deformation e ⊔ deformation f).map (MvPolynomial.map φ) =
      (deformation e).map (MvPolynomial.map φ) ⊔
        (deformation f).map (MvPolynomial.map φ) := Ideal.map_sup _ _ _

theorem deformation_map_inf {n : ℕ} (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e f : Expr n) :
    (deformation e ⊓ deformation f).map (MvPolynomial.map φ) =
      (deformation e).map (MvPolynomial.map φ) ⊓
        (deformation f).map (MvPolynomial.map φ) := by
  letI : Algebra (Polynomial ℤ) R := φ.toAlgebra
  obtain ⟨b,hb,hspan⟩ := Deformation.deformed_simultaneous_basis n
  exact coordinate_ideals_map_inf (S := R) b (deformation e) (deformation f)
    (monomials e) (monomials f) (deformation_adapted b hspan e) (deformation_adapted b hspan f)

end FourPapers.Symmetric.BoundedLattice
end
end
/- End BoundedMixedLattice.lean -/

#print axioms CommAlg.IntegralOverIdeal.of_pow
#print axioms CommAlg.idealIntegralClosure_isIntegrallyClosed
#print axioms FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_mem_integralClosure_product
#print axioms FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_integral_of_convex_scores
#print axioms FourPapers.Symmetric.DeterminantalTransfer.integralOver_sum_products_iff_support
#print axioms FourPapers.Symmetric.RationalPolyhedra.nonnegative_separation
#print axioms FourPapers.Symmetric.RationalPolyhedra.mem_upperHull_iff_ceilingVectors
#print axioms FourPapers.Symmetric.symbolicPower_iff_basis_support_of_weight
#print axioms FourPapers.Symmetric.IntegralClosure.closure_eq_finite_symbolic_lattice_of_minor_basis
#print axioms FourPapers.Symmetric.BoundedLattice.exists_integral_simultaneous_basis
#print axioms FourPapers.Symmetric.BoundedLattice.initial_inf
#print axioms FourPapers.Symmetric.BoundedLattice.coefficient_change_inf
#print axioms FourPapers.Symmetric.BoundedLattice.standard_monomial_basis
#print axioms FourPapers.Symmetric.BoundedLattice.deformation_flat
#print axioms FourPapers.Symmetric.BoundedLattice.deformation_at_zero

#print axioms FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map
#print axioms FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map_inf
#print axioms FourPapers.Symmetric.BoundedLattice.deformation_standard_basis
#print axioms FourPapers.Symmetric.BoundedLattice.deformation_map_unit

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "CommAlg.IntegralOverIdeal.of_pow".toName,
    "CommAlg.idealIntegralClosure_isIntegrallyClosed".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_mem_integralClosure_product".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_integral_of_convex_scores".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.integralOver_sum_products_iff_support".toName,
    "FourPapers.Symmetric.RationalPolyhedra.nonnegative_separation".toName,
    "FourPapers.Symmetric.RationalPolyhedra.mem_upperHull_iff_ceilingVectors".toName,
    "FourPapers.Symmetric.symbolicPower_iff_basis_support_of_weight".toName,
    "FourPapers.Symmetric.IntegralClosure.closure_eq_finite_symbolic_lattice_of_minor_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.exists_integral_simultaneous_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.initial_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.coefficient_change_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.standard_monomial_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_flat".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_at_zero".toName,
    "FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map".toName,
    "FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_standard_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_map_unit".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/integral_closure_dependency_graph.json" (Json.compress graph)
  logInfo m!"INTEGRAL_CLOSURE_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."


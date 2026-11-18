module
public import Mathlib
-- Match the original curated import closure's polynomial module dictionary.
-- Mathlib's umbrella additionally imports IrreducibleQuadratic.instModuleSelf;
-- the raw exported source types use AddMonoidAlgebra.instModule directly.
attribute [-instance] MvPolynomial.instModuleSelf

/-!
# Symmetric northwest rank and symbolic conditions

Theorems 1.1 and 1.2 of Caius Folkerts, *Gröbner bases for symmetric rank
conditions*, pages 2–3. Theorem 1.1 retains independent realization and
coefficient fields and the literal vanishing ideal of the rank locus.
Theorem 1.2 retains all symmetric nonnegative arrays, valid finite lists of
symbolic thresholds, and arbitrary commutative base change of the integral
monic family. Custom definitions are inlined, preserving source names/bodies.

The graded reverse lexicographic construction below is adapted verbatim from
Tau Ceti contributors' Apache-2.0 code preserved in symmetric_local.lean;
its order compares total degree and then reverse colex at equal degree.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace Finsupp

variable {α : Type*} [LinearOrder α]

/-- If `toColex y < toColex x` for nonzero `y`, compare the largest indices `mx`, `my` of the
supports: either `my < mx`, or they agree and then either `y my < x mx`, or these exponents
also agree and the comparison persists after erasing that index. -/
theorem max'_lt_or_of_toColex_lt {x y : α →₀ ℕ} (hx : x.support.Nonempty)
    (hy : y.support.Nonempty) (h : toColex y < toColex x) :
    y.support.max' hy < x.support.max' hx ∨ y.support.max' hy = x.support.max' hx ∧
      (y (y.support.max' hy) < x (x.support.max' hx) ∨
        y (y.support.max' hy) = x (x.support.max' hx) ∧
          toColex (y.erase (y.support.max' hy)) < toColex (x.erase (x.support.max' hx))) := by
  -- `Colex (α →₀ ℕ)` is a type synonym and Mathlib has no evaluation lemma for `toColex` on
  -- `Finsupp`, so `Colex.lt_iff` evaluates `toColex f` through the coercion of `α →₀ ℕ`, which
  -- is definitionally `f`. We restate its components, and the goals below, at `α →₀ ℕ`.
  obtain ⟨i, hi, hlt⟩ := Colex.lt_iff.1 h
  have hi : ∀ j, i < j → y j = x j := hi
  have hlt : y i < x i := hlt
  have hix : i ≤ x.support.max' hx := x.support.le_max' i (mem_support_iff.2 (by omega))
  rcases lt_trichotomy (y.support.max' hy) (x.support.max' hx) with hm | hm | hm
  · exact Or.inl hm
  · refine Or.inr ⟨hm, ?_⟩
    rw [hm]
    rcases hix.lt_or_eq with hix | hix
    · refine Or.inr ⟨hi _ hix, Colex.lt_iff.2 ⟨i, fun j hj ↦ ?_, ?_⟩⟩
      · change (y.erase _) j = (x.erase _) j
        by_cases hjm : j = x.support.max' hx
        · simp [hjm]
        · simp [erase_ne hjm, hi j hj]
      · change (y.erase _) i < (x.erase _) i
        simpa [erase_ne hix.ne] using hlt
    · exact Or.inl (hix ▸ hlt)
  · exfalso
    have hxm : x (y.support.max' hy) = 0 :=
      notMem_support_iff.1 fun h ↦ (x.support.le_max' _ h).not_gt hm
    exact mem_support_iff.1 (y.support.max'_mem hy) ((hi _ (hix.trans_lt hm)).trans hxm)

/-- When `α` has no infinite ascending chains, the colexicographic order on exponents of degree
at most `n` has no infinite ascending chains either. -/
theorem wellFoundedOn_setOf_degree_le_toColex_gt [WellFoundedGT α] (n : ℕ) :
    {a : α →₀ ℕ | a.degree ≤ n}.WellFoundedOn (fun a b ↦ toColex b < toColex a) := by
  induction n with
  | zero =>
    refine Set.Subsingleton.wellFoundedOn fun a ha b hb ↦ ?_
    simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero, degree_eq_zero_iff] at ha hb
    rw [ha, hb]
  | succ n ih =>
    rw [Set.wellFoundedOn_iff] at ih ⊢
    -- A nonzero exponent is recorded by its largest index `m`, the exponent at `m`, and the
    -- remaining exponent of smaller degree; colex ascents increase this triple lexicographically.
    let F : {x : α →₀ ℕ // x ≠ 0} → α × ℕ × (α →₀ ℕ) := fun x ↦
      (x.1.support.max' (support_nonempty_iff.2 x.2),
        x.1 (x.1.support.max' (support_nonempty_iff.2 x.2)),
        x.1.erase (x.1.support.max' (support_nonempty_iff.2 x.2)))
    have hbdd : WellFounded fun e e' : ℕ ↦ e' < e ∧ e ≤ n + 1 :=
      (wellFounded_lt.onFun (f := fun e : ℕ ↦ n + 1 - e)).mono fun e e' h ↦ by
        simp only [Function.onFun]; omega
    have hwf := InvImage.wf F ((wellFounded_gt (α := α)).prod_lex (hbdd.prod_lex ih))
    have hdeg (x : α →₀ ℕ) (m : α) (hm : m ∈ x.support) :
        (x.erase m).degree + 1 ≤ x.degree := by
      have h := congr_arg degree (single_add_erase m x)
      rw [map_add, degree_single] at h
      have := mem_support_iff.1 hm
      omega
    have hacc (y : {x : α →₀ ℕ // x ≠ 0}) :
        Acc (fun a b ↦ toColex b < toColex a ∧ a ∈ {a : α →₀ ℕ | a.degree ≤ n + 1} ∧
          b ∈ {a : α →₀ ℕ | a.degree ≤ n + 1}) y.1 := by
      induction y using hwf.induction with
      | _ y ihy =>
        refine ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩
        have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
        refine ihy ⟨x, hx0⟩ ?_
        simp only [Set.mem_ofPred_eq] at hx hy
        have hxm := x.support.max'_mem (support_nonempty_iff.2 hx0)
        have hym := y.1.support.max'_mem (support_nonempty_iff.2 y.2)
        rcases max'_lt_or_of_toColex_lt _ _ hxy with hm | ⟨hm, he | ⟨he, hr⟩⟩
        · exact Prod.Lex.left _ _ hm
        · simp only [InvImage, F, hm]
          refine Prod.Lex.right _ (Prod.Lex.left _ _ ⟨hm ▸ he, ?_⟩)
          exact (le_degree _ _).trans hx
        · have hdx := hdeg x _ hxm
          have hdy := hdeg y.1 _ hym
          rw [hm] at he hr hdy
          simp only [InvImage, F, hm, he]
          exact Prod.Lex.right _ (Prod.Lex.right _ ⟨hr, by simp only [Set.mem_ofPred_eq]; omega,
            by simp only [Set.mem_ofPred_eq]; omega⟩)
    refine ⟨fun y ↦ ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
    exact hacc ⟨x, hx0⟩

end Finsupp
section
namespace TauCeti

/-- A type synonym to equip a type with its graded reverse lexicographic order. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}

/-- `toDegRevLex` is the identity function to the `DegRevLex` of a type. -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

theorem toDegRevLex_injective : Function.Injective (toDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

/-- `ofDegRevLex` is the identity function from the `DegRevLex` of a type. -/
@[match_pattern] def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

theorem ofDegRevLex_injective : Function.Injective (ofDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegRevLex_inj {a b : DegRevLex α} : ofDegRevLex a = ofDegRevLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegRevLex_symm_eq : (@ofDegRevLex α).symm = toDegRevLex := rfl

@[simp] theorem toDegRevLex_symm_eq : (@toDegRevLex α).symm = ofDegRevLex := rfl

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) : ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) : toDegRevLex (ofDegRevLex a) = a := rfl

/-- A recursor for `DegRevLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegRevLex.rec {β : DegRevLex α → Sort*} (h : ∀ a, β (toDegRevLex a)) :
    ∀ a, β a := fun a ↦ h (ofDegRevLex a)

@[simp] lemma DegRevLex.forall_iff {p : DegRevLex α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (toDegRevLex a) := Iff.rfl

@[simp] lemma DegRevLex.exists_iff {p : DegRevLex α → Prop} :
    (∃ a, p a) ↔ ∃ a, p (toDegRevLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] : AddCommMonoid (DegRevLex α) :=
  ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) :
    toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

end TauCeti

end

section

namespace TauCeti

namespace DegRevLex

open Finsupp

variable [LinearOrder α]

/-- Injectivity of the literal degree/reverse-colex key; separately compared. -/
theorem degreeColexKey_injective : Function.Injective
    (fun f : DegRevLex (α →₀ ℕ) =>
      toLex ((ofDegRevLex f).degree, OrderDual.toDual (toColex (ofDegRevLex f)))) :=
  fun f g h => by simpa using congr_arg (fun p => ofColex (OrderDual.ofDual (ofLex p).2)) h
/-- The graded reverse lexicographic order on `α →₀ ℕ`: compare total degrees, then compare
monomials of equal degree by the reverse of the colexicographic order. -/
noncomputable instance : LinearOrder (DegRevLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun f => toLex ((ofDegRevLex f).degree, OrderDual.toDual (toColex (ofDegRevLex f))))
    degreeColexKey_injective

/-- The graded reverse lexicographic order compares degrees first, then reverses the
colexicographic order. -/
theorem lt_iff {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) < toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_lt_toLex

/-- The non-strict form of `TauCeti.DegRevLex.lt_iff`. -/
theorem le_iff {a b : DegRevLex (α →₀ ℕ)} :
    a ≤ b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) ≤ toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_le_toLex

/-- The textbook description of the graded reverse lexicographic order: among monomials of equal
degree, `a < b` when `a` has the larger exponent at the largest index where they differ. -/
theorem lt_iff_exists {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        ∃ i, (∀ j, i < j → ofDegRevLex a j = ofDegRevLex b j) ∧
          ofDegRevLex b i < ofDegRevLex a i := by
  rw [lt_iff, Colex.lt_iff]
  refine or_congr_right (and_congr_right fun _ ↦ exists_congr fun i ↦ and_congr_left fun _ ↦ ?_)
  exact forall_congr' fun j ↦ imp_congr_right fun _ ↦ eq_comm

/-- The ordinary ordered-cancellation laws for this exact grevlex order. -/
theorem orderedCancelAddMonoid_laws : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_right_inj, toColex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_right, add_left_inj, toColex_add,
      add_le_add_iff_right] using h

instance : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) := orderedCancelAddMonoid_laws

theorem single_strictAnti : StrictAnti (fun a : α ↦ toDegRevLex (single a 1)) := fun _ _ h ↦
  lt_iff.2 (Or.inr ⟨by simp, Colex.single_lt_iff.2 h⟩)

theorem single_antitone : Antitone (fun a : α ↦ toDegRevLex (single a 1)) :=
  single_strictAnti.antitone

@[simp]
theorem single_lt_iff {a b : α} :
    toDegRevLex (single b 1) < toDegRevLex (single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt

@[simp]
theorem single_le_iff {a b : α} :
    toDegRevLex (single b 1) ≤ toDegRevLex (single a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_ge

theorem monotone_degree :
    Monotone (fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) := fun _ _ h ↦ by
  rcases le_iff.1 h with h | h
  exacts [h.le, h.1.le]

/-- The graded reverse lexicographic order is well-founded when the indices have no infinite
ascending chains, for instance when there are finitely many of them. -/
theorem wellFoundedLT_law [WellFoundedGT α] : WellFoundedLT (DegRevLex (α →₀ ℕ)) := by
  have hfib (n : ℕ) : ((fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) ⁻¹' {n}).WellFoundedOn
      (Function.onFun (· < ·) fun x ↦ OrderDual.toDual (toColex (ofDegRevLex x))) := by
    refine Set.wellFoundedOn_image.1 (((wellFoundedOn_setOf_degree_le_toColex_gt n).subset ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_eq hx
  exact (WellFounded.prod_lex_of_wellFoundedOn_fiber wellFounded_lt.onFun hfib).mono
    fun a b (h : a < b) ↦ Prod.lex_def.2 <| by
      simpa only [OrderDual.toDual_lt_toDual] using lt_iff.1 h

instance wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegRevLex (α →₀ ℕ)) :=
  wellFoundedLT_law

end DegRevLex

namespace MonomialOrder

open Finsupp DegRevLex

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- Coordinatewise exponent domination is monotone for the exact grevlex map. -/
theorem toDegRevLex_monotone : Monotone (fun a : σ →₀ ℕ => toDegRevLex a) := by
  intro a b h
  simp only [DegRevLex.le_iff, ofDegRevLex_toDegRevLex]
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact Or.inl (by simpa [map_add, Nat.pos_iff_ne_zero, degree_eq_zero_iff] using hc)
noncomputable def degRevLex : MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegRevLex, map_add' := toDegRevLex_add }
  toSyn_monotone := toDegRevLex_monotone
end MonomialOrder
end TauCeti
end
namespace MonomialOrder
variable {σ R : Type*} (m : MonomialOrder σ)
variable [CommSemiring R]
/-- A subset `G` of an ideal `I` is a Gröbner basis of `I` for the monomial order `m` if the
leading terms of the elements of `G` span the same ideal as the leading terms of all elements
of `I`. -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)
end MonomialOrder
namespace FourPapers.Symmetric
open MvPolynomial
universe u v
/-- The independent entries of a generic symmetric `n × n` matrix, ordered by larger endpoint
and then by smaller endpoint. Indices are zero-based. -/
abbrev Entry (n : ℕ) := {p : Fin n ×ₗ Fin n // p.2 ≤ p.1}

/-- Fold a matrix position across the diagonal to its independent coordinate. -/
def fold {n : ℕ} (i j : Fin n) : Entry n :=
  ⟨toLex (max i j, min i j), min_le_max⟩
/-- The coefficient ring of the symmetric generic matrix. -/
abbrev CoordinateRing (n : ℕ) (K : Type*) [CommRing K] := MvPolynomial (Entry n) K

/-- Generic symmetric matrix over its coordinate ring. -/
def genericMatrix (n : ℕ) (K : Type*) [CommRing K] :
    Matrix (Fin n) (Fin n) (CoordinateRing n K) := fun i j => MvPolynomial.X (fold i j)
/-- A minor with strictly increasing row and column index lists. -/
def minor {n : ℕ} (K : Type*) [CommRing K] {t : ℕ}
    (a b : Fin t ↪o Fin n) : CoordinateRing n K :=
  ((genericMatrix n K).submatrix a b).det

/-- The exponent vector of the folded antidiagonal, retaining repeated variables. -/
def antidiagonalExponent {n t : ℕ} (a b : Fin t ↪o Fin n) : Entry n →₀ ℕ :=
  ∑ p : Fin t, Finsupp.single (fold (a p) (b p.rev)) 1

/-- The folded antidiagonal monomial, with coefficient one. -/
def antidiagonal {n : ℕ} (K : Type*) [CommRing K] {t : ℕ}
    (a b : Fin t ↪o Fin n) : CoordinateRing n K :=
  MvPolynomial.monomial (antidiagonalExponent a b) 1

/-- `r i j` is the rank bound in the northwest `(i+1) × (j+1)` rectangle. -/
abbrev RankArray (n : ℕ) := Fin n → Fin n → ℕ

/-- The exact set of prescribed northwest minors, including redundant ones. -/
def northwestGenerators {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Set (CoordinateRing n K) :=
  {f | ∃ (i j : Fin n) (a b : Fin (r i j + 1) ↪o Fin n),
    (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧ f = minor K a b}

/-- The ideal `I(r)` generated by all prescribed northwest minors. -/
def northwestIdeal {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Ideal (CoordinateRing n K) := Ideal.span (northwestGenerators K r)

/-- The exact corresponding folded antidiagonal generators. -/
def northwestAntidiagonals {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Set (CoordinateRing n K) :=
  {f | ∃ (i j : Fin n) (a b : Fin (r i j + 1) ↪o Fin n),
    (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧ f = antidiagonal K a b}

/-- The proposed initial ideal `J(r)`. -/
def northwestAntidiagonalIdeal {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Ideal (CoordinateRing n K) := Ideal.span (northwestAntidiagonals K r)

/-- All minors of one fixed size of the full symmetric matrix. -/
def fullMinorGenerators (n : ℕ) (K : Type*) [CommRing K] (t : ℕ) :
    Set (CoordinateRing n K) := {f | ∃ a b : Fin t ↪o Fin n, f = minor K a b}

/-- The full symmetric determinantal ideal `P_(n,t)`. -/
def determinantalIdeal (n : ℕ) (K : Type*) [CommRing K] (t : ℕ) :
    Ideal (CoordinateRing n K) := Ideal.span (fullMinorGenerators n K t)

/-- The prescribed folded graded reverse lexicographic monomial order. -/
noncomputable def foldedOrder (n : ℕ) : MonomialOrder (Entry n) :=
  TauCeti.MonomialOrder.degRevLex

/-- The initial ideal for exactly the prescribed folded monomial order. -/
noncomputable def initialIdeal {n : ℕ} (K : Type*) [CommRing K]
    (I : Ideal (CoordinateRing n K)) : Ideal (CoordinateRing n K) :=
  Ideal.span ((foldedOrder n).leadingTerm '' (I : Set (CoordinateRing n K)))
section SymbolicPowerSource
variable {R : Type*} [CommRing R]
/-- The span of fractions-clearing witnesses for the `s`th symbolic power. For prime `P`,
the span introduces no additional elements; this is proved below. -/
def symbolicPower (P : Ideal R) (s : ℕ) : Ideal R :=
  Ideal.span {f | ∃ g : R, g ∉ P ∧ g * f ∈ P ^ s}
end SymbolicPowerSource
/-- Row and column data of an arbitrary minor. -/
structure MinorData (n : ℕ) where
  size : ℕ
  rows : Fin size ↪o Fin n
  cols : Fin size ↪o Fin n

namespace MinorData
variable {n : ℕ}
/-- The genuine determinant attached to a minor datum. -/
def polynomial (K : Type*) [CommRing K] (δ : MinorData n) : CoordinateRing n K :=
  minor K δ.rows δ.cols

/-- Its folded antidiagonal exponent. -/
def exponent (δ : MinorData n) : Entry n →₀ ℕ :=
  antidiagonalExponent δ.rows δ.cols
end MinorData
variable {n : ℕ}
/-- The set `G_(n,t,s)` from the paper, with exact score `s`. -/
def symbolicGenerators (K : Type*) [CommRing K] (n t s : ℕ) :
    Set (CoordinateRing n K) :=
  {f | ∃ (k : ℕ) (δ : Fin k → MinorData n),
    (∀ j, t ≤ (δ j).size) ∧ (∑ j, ((δ j).size - t + 1)) = s ∧
    f = ∏ j, (δ j).polynomial K}

/-- The corresponding products of folded antidiagonals, with the same exact score. -/
def symbolicAntidiagonals (K : Type*) [CommRing K] (n t s : ℕ) :
    Set (CoordinateRing n K) :=
  {f | ∃ (k : ℕ) (δ : Fin k → MinorData n),
    (∀ j, t ≤ (δ j).size) ∧ (∑ j, ((δ j).size - t + 1)) = s ∧
    f = monomial (∑ j, (δ j).exponent) 1}

/-- The monomial ideal `J_(n,t,s)`. -/
def symbolicAntidiagonalIdeal (K : Type*) [CommRing K] (n t s : ℕ) :
    Ideal (CoordinateRing n K) := Ideal.span (symbolicAntidiagonals K n t s)

/-- The literal mixed generating set in Theorem 1.2. -/
def mixedGenerators (K : Type*) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Set (CoordinateRing n K) :=
  northwestGenerators K r ∪
    {f | ∃ ts ∈ conditions, f ∈ symbolicGenerators K n ts.1 ts.2}

/-- The ideal named on the left side of the field assertion of Theorem 1.2. This definition
uses actual symbolic powers, rather than defining them by the proposed generators. -/
def mixedIdeal (K : Type*) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Ideal (CoordinateRing n K) :=
  northwestIdeal K r + (conditions.map fun ts =>
    symbolicPower (determinantalIdeal n K ts.1) ts.2).sum
/-- Exact allowed range for each symbolic threshold in Theorem 1.2. -/
def ValidSymbolicConditions (n : ℕ) (conditions : List (ℕ × ℕ)) : Prop :=
  ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2

/-- The field assertion of Theorem 1.2. `mixedIdeal` uses the true symbolic powers
as defined by localization and proved equivalent to that definition for prime ideals.
The proposed product generators occur only in `mixedGenerators`. -/
def CompatibleGroebnerAssertion : Prop :=
  ∀ (n : ℕ) (K : Type v) [Field K] (r : RankArray n),
    (∀ i j, r i j = r j i) →
    ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
      (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
        (mixedIdeal K r conditions)

/-- Integral sign normalization, which is multiplication by the leading sign. -/
def normalizedMixedGenerators {n : ℕ} (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Set (CoordinateRing n ℤ) :=
  (fun f => C ((foldedOrder n).leadingCoeff f) * f) '' mixedGenerators ℤ r conditions

/-- The integral model over a general coefficient ring is defined by base change
of the displayed integral generators, exactly as in Theorem 1.2. -/
def integralMixedIdeal {n : ℕ} (K : Type v) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Ideal (CoordinateRing n K) :=
  Ideal.span ((MvPolynomial.map (Int.castRingHom K)) '' normalizedMixedGenerators r conditions)

/-- Standard exponents of the proposed monic integral generating family. -/
def MixedStandardExponents {n : ℕ} (r : RankArray n) (conditions : List (ℕ × ℕ)) :=
  {e : Entry n →₀ ℕ // monomial e (1 : ℤ) ∉
    northwestAntidiagonalIdeal ℤ r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal ℤ n ts.1 ts.2}

/-- The quotient basis assertion under every commutative base change, expressed
as independence and spanning of the specified monomial residue classes. -/
def IntegralBaseChangeAssertion : Prop :=
  ∀ (n : ℕ) (r : RankArray n), (∀ i j, r i j = r j i) →
    ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
      (foldedOrder n).IsGroebnerBasis (normalizedMixedGenerators r conditions)
        (Ideal.span (normalizedMixedGenerators r conditions)) ∧
      (∀ g ∈ normalizedMixedGenerators r conditions,
        (foldedOrder n).leadingCoeff g = 1) ∧
      ∀ (K : Type v) [CommRing K],
        let I := integralMixedIdeal K r conditions
        let b : MixedStandardExponents r conditions → CoordinateRing n K ⧸ I :=
          fun e => Ideal.Quotient.mk I (monomial e.val 1)
        LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤

/-- Northwest ranks of an actual matrix. A prefix ending at `i : Fin n` includes
all indices at most `i`; no artificial bound on a matrix rank is imposed. -/
def matrixRankArray {n : ℕ} {F : Type u} [Field F]
    (w : Matrix (Fin n) (Fin n) F) : RankArray n :=
  fun i j => (w.submatrix (fun p : {p : Fin n // p ≤ i} => p.val)
    (fun q : {q : Fin n // q ≤ j} => q.val)).rank

/-- Actual symmetric matrices satisfying all northwest rank inequalities,
identified with their independent folded coordinates. -/
def rankBoundLocus {n : ℕ} (K : Type v) [Field K] (r : RankArray n) :
    Set (Entry n → K) :=
  {x | ∀ i j, matrixRankArray (fun a b => x (fold a b)) i j ≤ r i j}
/-- The algebraic assertions of Theorem 1.1, with unrelated realization and
coefficient fields and no rank-size restriction. -/
def RankLocusAssertion : Prop :=
  ∀ (n : ℕ) (F : Type u) [Field F] (w : Matrix (Fin n) (Fin n) F),
    w.transpose = w →
    ∀ (K : Type v) [Field K],
      (northwestIdeal K (matrixRankArray w)).IsPrime ∧
      initialIdeal K (northwestIdeal K (matrixRankArray w)) =
        northwestAntidiagonalIdeal K (matrixRankArray w)

/-- The geometric conclusion of Theorem 1.1 uses the vanishing ideal of the
actual rank-bounded set over an algebraically closed field. In particular, it is
not encoded by defining the rank locus to be the zero locus of the desired ideal. -/
def RankDefiningIdealAssertion : Prop :=
  ∀ (n : ℕ) (F : Type u) [Field F] (w : Matrix (Fin n) (Fin n) F),
    w.transpose = w →
    ∀ (K : Type v) [Field K] [IsAlgClosed K],
      MvPolynomial.vanishingIdeal K (rankBoundLocus K (matrixRankArray w)) =
        northwestIdeal K (matrixRankArray w)

/-- Complete target for Theorem 1.1, including its algebraically closed
rank-locus conclusion. This conjunction is a statement target, not a proof. -/
def SymmetricRankLociTheorem : Prop :=
  RankLocusAssertion.{u, v} ∧ RankDefiningIdealAssertion.{u, v}
/-- Theorem 1.1: all-field primeness, the folded initial ideal, and the
actual rank-locus defining ideal over algebraically closed coefficients. -/
theorem symmetric_rank_loci : SymmetricRankLociTheorem.{u,v} := by sorry
/-- Theorem 1.2 over fields: prescribed northwest minors and exact-score
products form a Gröbner basis for the sum of actual symbolic powers. -/
theorem compatible_rank_and_symbolic_conditions : CompatibleGroebnerAssertion.{u} := by sorry
/-- Theorem 1.2: the same initial-ideal equality with all quantifiers visible. -/
theorem compatible_initial_ideal (n : ℕ) (K : Type u) [Field K] (r : RankArray n)
    (hr : ∀ i j, r i j = r j i) (conditions : List (ℕ × ℕ))
    (hc : ValidSymbolicConditions n conditions) :
    initialIdeal K (mixedIdeal K r conditions) = northwestAntidiagonalIdeal K r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal K n ts.1 ts.2 := by sorry
/-- Theorem 1.2 over the integers and every commutative base change, including
the specified basis of monomial residue classes of the quotient. -/
theorem integral_rank_and_symbolic_conditions : IntegralBaseChangeAssertion.{u} := by sorry
universe w
open scoped TensorProduct
/-- The corresponding complete paper consequence, retaining its original signature. -/
theorem northwest_groebner (n : ℕ) (K : Type u) [Field K] (r : RankArray n)
    (hr : ∀ i j, r i j = r j i) :
    (foldedOrder n).IsGroebnerBasis (northwestGenerators K r) (northwestIdeal K r) := by sorry
/-- The corresponding complete paper consequence, retaining its original signature. -/
theorem symmetric_rank_quotient_isDomain {n : ℕ}
    {F : Type u} [Field F] (w : Matrix (Fin n) (Fin n) F)
    (hw : w.transpose = w) (R : Type v) [CommRing R] [IsDomain R] :
    IsDomain (CoordinateRing n R ⧸ northwestIdeal R (matrixRankArray w)) := by sorry
/-- The corresponding complete paper consequence, retaining its original signature. -/
theorem symmetric_rank_baseChange_isDomain {n : ℕ} {F : Type w} [Field F]
    (w : Matrix (Fin n) (Fin n) F) (hw : w.transpose = w)
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] :
    IsDomain (S ⊗[R] (CoordinateRing n R ⧸ northwestIdeal R (matrixRankArray w))) := by sorry
/-- The corresponding complete paper consequence, retaining its original signature. -/
theorem symmetric_rank_geometric_fibers {n : ℕ} {F : Type u} [Field F]
    (w : Matrix (Fin n) (Fin n) F) (hw : w.transpose = w)
    (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L] :
    letI : CommRing (K ⊗[ℤ]
        (CoordinateRing n ℤ ⧸ northwestIdeal ℤ (matrixRankArray w))) :=
      Algebra.TensorProduct.instCommRing
    letI : Algebra K (K ⊗[ℤ]
        (CoordinateRing n ℤ ⧸ northwestIdeal ℤ (matrixRankArray w))) :=
      Algebra.TensorProduct.leftAlgebra
    IsDomain (L ⊗[K] (K ⊗[ℤ]
      (CoordinateRing n ℤ ⧸ northwestIdeal ℤ (matrixRankArray w)))) := by sorry
/-- All the exact parameters allowed in Theorem 1.2, with no bound on the
number or sizes of the positive symbolic thresholds. -/
structure MixedDatum (n : ℕ) where
  rank : RankArray n
  symmetric : ∀ i j, rank i j = rank j i
  conditions : List (ℕ × ℕ)
  valid : ValidSymbolicConditions n conditions

variable {n : ℕ}
/-- The integral span of the displayed mixed generators. -/
def mixedIntegralSpan (D : MixedDatum n) : Ideal (CoordinateRing n ℤ) :=
  Ideal.span (mixedGenerators ℤ D.rank D.conditions)

/-- Finite lattice expressions record the actual sums and intersections,
without replacing ideals by their initial monomial sets. -/
inductive MixedLatticeExpression (n : ℕ) where
  | atom : MixedDatum n → MixedLatticeExpression n
  | sup : MixedLatticeExpression n → MixedLatticeExpression n → MixedLatticeExpression n
  | inf : MixedLatticeExpression n → MixedLatticeExpression n → MixedLatticeExpression n

def MixedLatticeExpression.ideal : MixedLatticeExpression n → Ideal (CoordinateRing n ℤ)
  | .atom D => mixedIntegralSpan D
  | .sup e f => e.ideal ⊔ f.ideal
  | .inf e f => e.ideal ⊓ f.ideal
/-- The same finite ideal expression evaluated in an arbitrary coefficient ring. -/
def MixedLatticeExpression.baseChangedIdeal (S : Type*) [CommRing S] :
    MixedLatticeExpression n → Ideal (CoordinateRing n S)
  | .atom D => integralMixedIdeal S D.rank D.conditions
  | .sup e f => e.baseChangedIdeal S ⊔ f.baseChangedIdeal S
  | .inf e f => e.baseChangedIdeal S ⊓ f.baseChangedIdeal S
end FourPapers.Symmetric
namespace MonomialOrder
variable {σ R : Type*} (m : MonomialOrder σ)
variable [CommSemiring R]
/-- The standard monomials of the ideal `I` for the monomial order `m`: the exponents that are not
divisible by the leading monomial of any nonzero element of `I`. -/
def standardMonomials (I : Ideal (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  {c | ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ c}
end MonomialOrder
namespace FourPapers.Symmetric
open MvPolynomial
variable {n : ℕ}
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_baseChange (S : Type*) [CommRing S]
    (e : MixedLatticeExpression n) :
    e.baseChangedIdeal S = e.ideal.map (MvPolynomial.map (Int.castRingHom S)) := by sorry
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_quotient_free (S : Type*) [CommRing S]
    (e : MixedLatticeExpression n) :
    Module.Free S (CoordinateRing n S ⧸ e.baseChangedIdeal S) := by sorry
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_quotient_flat (S : Type*) [CommRing S]
    (e : MixedLatticeExpression n) :
    Module.Flat S (CoordinateRing n S ⧸ e.baseChangedIdeal S) := by sorry
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_standard_monomial_basis (S : Type*) [CommRing S]
    (e : MixedLatticeExpression n) :
    let v : (foldedOrder n).standardMonomials e.ideal →
        CoordinateRing n S ⧸ e.baseChangedIdeal S :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent S v ∧ Submodule.span S (Set.range v) = ⊤ := by sorry
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_baseChange_hom {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (e : MixedLatticeExpression n) :
    (e.baseChangedIdeal A).map (MvPolynomial.map φ) = e.baseChangedIdeal B := by sorry
/-- Corollary 6.3: the literal compatible finite lattice and arbitrary base change. -/
theorem mixed_lattice_map_inf {n : ℕ} {A B : Type*}
    [CommRing A] [CommRing B] (φ : A →+* B) (e f : MixedLatticeExpression n) :
    (e.baseChangedIdeal A ⊓ f.baseChangedIdeal A).map (MvPolynomial.map φ) =
      (e.baseChangedIdeal A).map (MvPolynomial.map φ) ⊓
        (f.baseChangedIdeal A).map (MvPolynomial.map φ) := by sorry
section SymbolicReesLaws
variable {R S : Type*} [CommRing R] [CommRing S]
/-- Degree zero of the localization-defined symbolic powers is the unit ideal.
This supporting law is also compared against its actual source proof. -/
@[simp] theorem symbolicPower_zero (P : Ideal R) [P.IsPrime] :
    symbolicPower P 0 = ⊤ := by sorry
/-- Multiplicativity of actual symbolic powers, also a compared supporting law. -/
theorem mul_mem_symbolicPower_add (P : Ideal R) [P.IsPrime]
    {a b : ℕ} {f g : R} (hf : f ∈ symbolicPower P a)
    (hg : g ∈ symbolicPower P b) : f * g ∈ symbolicPower P (a + b) := by sorry
end SymbolicReesLaws
end FourPapers.Symmetric
namespace FourPapers.Symmetric.Rees
open MvPolynomial Finsupp
universe u
section General
variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
/-- Closure under polynomial multiplication for the displayed coefficient constraints. -/
theorem coefficient_mul (I : ℕ → Ideal S)
    (hmul : ∀ a b f g, f ∈ I a → g ∈ I b → f * g ∈ I (a+b))
    {f g : Polynomial S} (hf : ∀ s, f.coeff s ∈ I s) (hg : ∀ s, g.coeff s ∈ I s) :
    ∀ s, (f * g).coeff s ∈ I s := by
  intro s
  rw [Polynomial.coeff_mul]
  apply Ideal.sum_mem
  rintro ⟨a,b⟩ hab
  simpa only [Finset.HasAntidiagonal.mem_antidiagonal.mp hab] using hmul a b _ _ (hf a) (hg b)
/-- The unit obeys the displayed coefficient constraints. -/
theorem coefficient_one (I : ℕ → Ideal S) (hzero : I 0 = ⊤) :
    ∀ s, (1 : Polynomial S).coeff s ∈ I s := by
  intro s
  by_cases hs : s = 0
  · subst s; simp [hzero]
  · simp [Polynomial.coeff_one, hs]
/-- Addition obeys the displayed coefficient constraints. -/
theorem coefficient_add (I : ℕ → Ideal S) {f g : Polynomial S}
    (hf : ∀ s, f.coeff s ∈ I s) (hg : ∀ s, g.coeff s ∈ I s) :
    ∀ s, (f + g).coeff s ∈ I s := by
  intro s
  rw [Polynomial.coeff_add]
  exact (I s).add_mem (hf s) (hg s)
/-- Zero obeys the displayed coefficient constraints. -/
theorem coefficient_zero (I : ℕ → Ideal S) : ∀ s, (0 : Polynomial S).coeff s ∈ I s := by
  intro s; simp
/-- Every coefficient scalar obeys the displayed polynomial constraints. -/
theorem coefficient_algebraMap (I : ℕ → Ideal S) (hzero : I 0 = ⊤) (c : K) :
    ∀ s, (algebraMap K (Polynomial S) c).coeff s ∈ I s := by
  intro s
  change (Polynomial.C (algebraMap K S c)).coeff s ∈ I s
  by_cases hs : s = 0
  · subst s; simp [hzero]
  · simp [Polynomial.coeff_C, hs]
/-- A multiplicative ideal family defines its literal polynomial subalgebra. -/
def coefficientAlgebra (I : ℕ → Ideal S) (hzero : I 0 = ⊤)
    (hmul : ∀ a b f g, f ∈ I a → g ∈ I b → f * g ∈ I (a+b)) :
    Subalgebra K (Polynomial S) where
  carrier := {f | ∀ s, f.coeff s ∈ I s}
  mul_mem' := coefficient_mul I hmul
  one_mem' := coefficient_one I hzero
  add_mem' := coefficient_add I
  zero_mem' := coefficient_zero I
  algebraMap_mem' := coefficient_algebraMap I hzero

/-- The symbolic Rees algebra, defined independently of the proposed generators. -/
def symbolicRees (P : Ideal S) [P.IsPrime] : Subalgebra K (Polynomial S) :=
  coefficientAlgebra (symbolicPower P) (symbolicPower_zero P)
    (fun _ _ _ _ hf hg => mul_mem_symbolicPower_add P hf hg)
end General
section Leading
variable {σ K : Type*} [CommRing K]
/-- The literal leading term for the order of Corollary 7.1. -/
def tFirstLeadingTerm (m : MonomialOrder σ) (f : Polynomial (MvPolynomial σ K)) :
    Polynomial (MvPolynomial σ K) :=
  Polynomial.monomial f.natDegree (m.leadingTerm f.leadingCoeff)
/-- The initial algebra is generated by leading terms of actual algebra elements. -/
def initialAlgebra (m : MonomialOrder σ)
    (A : Subalgebra K (Polynomial (MvPolynomial σ K))) :
    Subalgebra K (Polynomial (MvPolynomial σ K)) :=
  Algebra.adjoin K (tFirstLeadingTerm m '' (A : Set _))

/-- Both requirements in the paper's definition of a SAGBI basis. -/
def IsSagbiBasis (m : MonomialOrder σ)
    (A : Subalgebra K (Polynomial (MvPolynomial σ K)))
    (G : Set (Polynomial (MvPolynomial σ K))) : Prop :=
  Algebra.adjoin K G = A ∧
    Algebra.adjoin K (tFirstLeadingTerm m '' G) = initialAlgebra m A

end Leading
section SingleScore
variable {n : ℕ} (K : Type u) [Field K] (t : ℕ)
/-- A minor lifted to its actual symbolic Rees degree. -/
def minorLift (δ : MinorData n) : Polynomial (CoordinateRing n K) :=
  Polynomial.monomial (δ.size-t+1) (δ.polynomial K)

/-- Exactly the finite collection displayed in Corollary 7.1. -/
def singleGenerators : Set (Polynomial (CoordinateRing n K)) :=
  Set.range (fun e : Entry n => Polynomial.C (X e)) ∪
    minorLift K t '' {δ : MinorData n | t ≤ δ.size}
end SingleScore
/-- Primeness needed to define the actual symbolic Rees algebra, itself compared. -/
theorem determinantal_prime (n : ℕ) (K : Type u) [Field K] (t : ℕ) (ht : 0 < t) :
    (determinantalIdeal n K t).IsPrime := by sorry
/-- The actual single symbolic Rees algebra for a positive determinantal size. -/
def determinantalSymbolicRees (n : ℕ) (K : Type u) [Field K] (t : ℕ) (ht : 0 < t) :
    Subalgebra K (Polynomial (CoordinateRing n K)) := by
  letI := determinantal_prime n K t ht
  exact symbolicRees (determinantalIdeal n K t)

/-- Corollary7.1: the actual finite generator collection is a SAGBI basis of
the symbolic Rees algebra, with both generation equalities retained. -/
theorem corollary_7_1_sagbi (n : ℕ) (K : Type u) [Field K] (t : ℕ)
    (ht : 0 < t) (htn : t ≤ n) :
    (singleGenerators (n := n) K t).Finite ∧
    IsSagbiBasis (foldedOrder n) (determinantalSymbolicRees n K t ht)
      (singleGenerators K t) := by sorry
end FourPapers.Symmetric.Rees

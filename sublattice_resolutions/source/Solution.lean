module
public import Mathlib
public import paper_results.transfer_formulas
public import paper_results.part009
public import paper_results.numerical_transfer
public import graph_results.canonical_finer_monomial_homology
public import paper_results.finite_rees_presentation
public import graph_results.closed_graph_integer_betti

/-!
# A literal finite Rees Gröbner presentation for sublattice ideals

Proposition2.2 of Caius Folkerts, *Sublattice resolutions and Betti preservation
in all powers*. The variables are exactly the row/column variables and one
variable per lattice element. The target is the actual polynomial ring with
one homogenizing variable; sorting and predecessor relations give a monic
Gröbner basis, generate the kernel, and have the displayed initial ideal.
The selected entry also includes the actual ordinary and fine Koszul
homology comparisons, all four Theorem4.3 clauses, and full Corollaries5.1/5.2.
-/

@[expose] public noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
set_option backward.isDefEq.respectTransparency false
namespace PalomarSublattice.NoncommBridgeAPI
universe u v
variable {R : Type u} {S : Type v} [Ring R] [Ring S]
/-- A ring equivalence transports the actual underlying left ideals of two-sided
ideals whenever it transports their actual membership predicates. -/
theorem map_asIdeal_of_mem_iff (e : R ≃+* S) (I : TwoSidedIdeal R)
    (J : TwoSidedIdeal S) (h : ∀ x, x ∈ I ↔ e x ∈ J) :
    Ideal.map e.toRingHom I.asIdeal = J.asIdeal := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact TwoSidedIdeal.mem_asIdeal.mpr ((h x).mp (TwoSidedIdeal.mem_asIdeal.mp hx))
  · intro hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply TwoSidedIdeal.mem_asIdeal.mpr
    apply (h (e.symm y)).mpr
    simpa only [e.apply_symm_apply] using (TwoSidedIdeal.mem_asIdeal.mp hy)
/-- The inverse law on actual submodule values, with its domain pinned before
congruence elaboration. No unfolding of the underlying Finsupp construction. -/
theorem submoduleEquiv_symm_apply_apply_val
    {K M N : Type*} [Semiring K] [AddCommMonoid M] [AddCommMonoid N]
    [Module K M] [Module K N]
    (U : Submodule K M) (W : Submodule K N) (e : U ≃ₗ[K] W) (x : U) :
    (e.symm (e x)).val = x.val :=
  congrArg (fun z : U => z.val) (e.symm_apply_apply x)
end PalomarSublattice.NoncommBridgeAPI

namespace PalomarSublattice.BridgeAPI
universe u v w x
variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} {Z : Type x}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]
theorem boundaryMap_val (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : g.comp f = 0) (z : X) :
    (FourPapers.FilteredHomology.boundaryMap f g h z).val = f z := rfl
/-- The actual signed coefficient action, uniformly for every ring module. -/
theorem signed_unit_action (a : R) (e : ℤˣ) (x : X) :
    (a * ((e : ℤ) : R)) • x = a • (e • x) := by
  rw [mul_smul,Units.smul_def,Int.cast_smul_eq_zsmul]
end PalomarSublattice.BridgeAPI

namespace PalomarSublattice
open Classical MvPolynomial
open scoped MonomialOrder
universe u v
variable {d : ℕ} (n : Fin d → ℕ)
/-- The exact finite product of the row chains. -/
abbrev FiniteTuple := ∀ r, Fin (n r)
/-- Exactly one variable per row/column pair; ULift changes only its universe. -/
abbrev FiniteVariable : Type u := Σ r, ULift.{u} (Fin (n r))
/-- The squarefree exponent of the product selecting one variable in every row. -/
def finiteRowExponent (a : FiniteTuple n) : (FiniteVariable.{u} n →₀ ℕ) :=
  ∑ r, Finsupp.single ⟨r, ULift.up (a r)⟩ 1
/-- Closure of the finite tuple set under coordinatewise minimum and maximum. -/
def finiteLatticeClosed (E : Finset (FiniteTuple n)) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E) ∧ (∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)
variable {n}
/-- The disjoint sum of exact base variables and one Rees generator per tuple. -/
abbrev FiniteReesVariable (E : Finset (FiniteTuple n)) := FiniteVariable.{u} n ⊕ E
/-- The exponent of each image: base variable itself, or row product times homogenizing variable. -/
def finiteReesVariableExponent (E : Finset (FiniteTuple n)) :
    FiniteReesVariable.{u} E → Option (FiniteVariable.{u} n) →₀ ℕ
  | Sum.inl x => Finsupp.single (some x) 1
  | Sum.inr a => (finiteRowExponent n a.val).embDomain Function.Embedding.some +
      Finsupp.single none 1
/-- The induced additive map on actual polynomial exponent vectors. -/
def finiteReesExponentMap (E : Finset (FiniteTuple n)) :
    (FiniteReesVariable.{u} E →₀ ℕ) →+ (Option (FiniteVariable.{u} n) →₀ ℕ) :=
  Finsupp.weight (finiteReesVariableExponent E)
section PresentationMap
variable (E : Finset (FiniteTuple n)) (k : Type v) [CommRing k]
/-- The literal polynomial algebra map with the displayed exponent images. -/
def finiteReesPresentationMap :
    MvPolynomial (FiniteReesVariable.{u} E) k →ₐ[k] MvPolynomial (Option (FiniteVariable.{u} n)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (finiteReesExponentMap E)
end PresentationMap
variable {E : Finset (FiniteTuple n)}
/-- A product of two tuple variables. -/
def finiteSortingHeadExponent (a b : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr a) 1 + Finsupp.single (Sum.inr b) 1
/-- The product of their meet and join variables, using actual lattice closure. -/
def finiteSortingTailExponent (hE : finiteLatticeClosed n E) (a b : E) :
    FiniteReesVariable.{u} E →₀ ℕ :=
  Finsupp.single (Sum.inr ⟨a.val ⊓ b.val, hE.1 a.val a.property b.val b.property⟩) 1 +
  Finsupp.single (Sum.inr ⟨a.val ⊔ b.val, hE.2 a.val a.property b.val b.property⟩) 1
/-- The predecessor coefficient ratio times its tuple variable. -/
def finiteCoefficientHeadExponent (b a : E) : FiniteReesVariable.{u} E →₀ ℕ :=
  (finiteRowExponent n b.val - finiteRowExponent n a.val).embDomain Function.Embedding.inl +
    Finsupp.single (Sum.inr a) 1
section Relations
variable {k : Type v} [CommRing k] [Nontrivial k]
/-- The actual sorting binomial. -/
def finiteSortingRelation (hE : finiteLatticeClosed n E) (a b : E) :
    MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteSortingHeadExponent.{u} a b) 1 - monomial (finiteSortingTailExponent.{u} hE a b) 1
/-- The actual predecessor coefficient binomial. -/
def finiteCoefficientRelation (b a : E) : MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteCoefficientHeadExponent.{u} b a) 1 - monomial (finiteCoefficientHeadExponent.{u} a b) 1
/-- Exactly the sorting relations of incomparable pairs and predecessor relations of strict comparable pairs. -/
def FiniteReesRelations (hE : finiteLatticeClosed n E) : Set (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  {f | ∃ a b : E, ¬ a.val ≤ b.val ∧ ¬ b.val ≤ a.val ∧ f = finiteSortingRelation hE a b} ∪
  {f | ∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧ f = finiteCoefficientRelation b a}
end Relations
/-- Exactly the indicated initial exponents of both relation families. -/
def finiteReesInitialHeads (E : Finset (FiniteTuple n)) :
    Set (FiniteReesVariable.{u} E →₀ ℕ) :=
  {c | (∃ a b : E, ¬a.val ≤ b.val ∧ ¬b.val ≤ a.val ∧
      c = finiteSortingHeadExponent a b) ∨
    (∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧
      c = finiteCoefficientHeadExponent b a)}
/-- The genuine monomial ideal generated by the displayed initial heads. -/
def finiteReesInitialIdeal (k : Type*) [CommRing k]
    (E : Finset (FiniteTuple n)) : Ideal (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  Ideal.span ((fun c => MvPolynomial.monomial c (1 : k)) '' finiteReesInitialHeads E)
/-- The ordinary definition of a Gröbner basis: the generators lie in the
ideal and their leading terms span its actual initial ideal. -/
def IsGroebnerBasis {σ k : Type*} [CommSemiring k] (m : MonomialOrder σ)
    (G : Set (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)
variable {k : Type v} [CommRing k] [Nontrivial k]
/-- Proposition2.2: the order is constructed, not assumed, and every actual
relation is monic. Both the polynomial kernel and initial ideal are literal. -/
theorem proposition22 (hE : finiteLatticeClosed n E) :
    ∃ m : MonomialOrder.{u,u} (FiniteReesVariable.{u} E),
      IsGroebnerBasis m (FiniteReesRelations.{u} (k := k) hE)
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom) ∧
      (∀ f ∈ FiniteReesRelations.{u} (k := k) hE, m.Monic f) ∧
      RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom =
        Ideal.span (FiniteReesRelations.{u} (k := k) hE) ∧
      Ideal.span (m.leadingTerm ''
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom : Set _)) =
          finiteReesInitialIdeal k E := by
  exact FourPapers.Sublattice.proposition22 hE
end PalomarSublattice

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open scoped BigOperators
open Classical MvPolynomial
namespace PalomarSublattice.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [CommRing K]

/-- Literal coefficient Koszul coordinates in exterior degree p. -/
abbrev Coordinates (I : Ideal (MvPolynomial V K)) (p : ℕ) := Set.powersetCard V p →₀ I

/-- The ordinary deletion sign: minus one to the number of exterior
coordinates before i. The source proves equality with its shuffle sign. -/
def eraseSign (i : V) (s : Finset V) : ℤˣ :=
  (-1 : ℤˣ) ^ (s.filter (fun j => j < i)).card

/-- Deleting one incident coordinate has the required exterior cardinality.
This supporting statement must be selected in the eventual Comparator config. -/
theorem eraseIndex_card {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : (s.val.erase j.val).card = p := by
  simp [Finset.card_erase_of_mem j.property, s.property]

/-- The exterior index obtained by deleting an incident coordinate. -/
def eraseIndex {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : Set.powersetCard V p :=
  ⟨s.val.erase j.val, eraseIndex_card s j⟩

/-- The genuine signed polynomial Koszul differential: delete an exterior
coordinate and multiply its ideal coefficient by that polynomial variable. -/
def differential (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    Coordinates I (p + 1) →ₗ[K] Coordinates I p :=
  (Finsupp.lsum (MvPolynomial V K) (fun s : Set.powersetCard V (p + 1) =>
    ∑ j : {j // j ∈ s.val},
      (Finsupp.lsingle (eraseIndex s j)).comp
        (LinearMap.lsmul (MvPolynomial V K) I
          (X j.val * (((eraseSign j.val s.val : ℤˣ) : ℤ) : MvPolynomial V K))))).restrictScalars K

/-- The outgoing map at homological degree zero is exactly zero. -/
def previous (I : Ideal (MvPolynomial V K)) :
    ∀ p : ℕ, Coordinates I p →ₗ[K] Coordinates I p.pred
  | 0 => 0
  | p + 1 => differential I p

/-- Read an actual polynomial ideal coefficient at one exterior coordinate. -/
def coefficientAt (I : Ideal (MvPolynomial V K)) (p : ℕ)
    (s : Set.powersetCard V p) : Coordinates I p →ₗ[K] MvPolynomial V K :=
  (I.subtype.restrictScalars K).comp (Finsupp.lapply s)

/-- Total integer degree q means polynomial coefficient degree q-p at every
exterior p-subset. Negative degrees vanish by the actual polynomial grading;
no numerical zero convention occurs in this definition. -/
def piece (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  ⨅ s : Set.powersetCard V p,
    (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℤ)) (q - (p : ℤ))).comap
      (coefficientAt I p s)

/-- The genuine cycles of the total-degree-q polynomial Koszul component. -/
def cycles (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (Coordinates I p) :=
  LinearMap.ker (previous I p) ⊓ piece I q p

/-- The canonical additive group of the actual cycle submodule. This explicit
instance keeps the quotient on the same canonical ring/module structures. -/
instance cyclesAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (cycles I q p) :=
  Submodule.addCommGroup (R := K) (M := Coordinates I p) (cycles I q p)

/-- Actual boundaries, mapped from the preceding homogeneous component and
viewed in its cycles. The planned proof establishes differential squared zero. -/
def boundaries (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Submodule K (cycles I q p) :=
  (Submodule.map (differential I p) (piece I q (p + 1))).comap (cycles I q p).subtype

/-- The actual homogeneous polynomial Koszul homology quotient. -/
abbrev Homology (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :=
  (cycles I q p) ⧸ boundaries I q p

/-- The canonical additive group on the actual homogeneous homology quotient. -/
instance homologyAddCommGroup (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    AddCommGroup (Homology I q p) :=
  Submodule.Quotient.addCommGroup (R := K) (M := cycles I q p) (boundaries I q p)

/-- The canonical coefficient module on the actual homogeneous homology quotient. -/
instance homologyModule (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ) :
    Module K (Homology I q p) :=
  Submodule.Quotient.module (R := K) (M := cycles I q p) (boundaries I q p)

end PalomarSublattice.Koszul
namespace PalomarSublattice.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [Field K]

/-- The dimension of the actual homogeneous Koszul homology vector space. -/
def betti (I : Ideal (MvPolynomial V K)) (p : ℕ) (q : ℤ) : ℕ :=
  Module.finrank K (Homology I q p)
end PalomarSublattice.Koszul

namespace PalomarSublattice.Koszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [Field K]

private theorem integerWeight_degree (a : V →₀ ℕ) :
    Finsupp.weight (fun _ : V => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_eq_sum, Finsupp.degree, Finsupp.sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp only [Finsupp.notMem_support_iff.mp hj, Nat.cast_zero]

private theorem mem_piece_iff (I : Ideal (MvPolynomial V K)) (q : ℤ) (p : ℕ)
    (x : Coordinates I p) :
    x ∈ piece I q p ↔
      ∀ s : Set.powersetCard V p, ∀ a : V →₀ ℕ,
        (x s).val.coeff a ≠ 0 → (a.degree : ℤ) + (p : ℤ) = q := by
  simp only [piece, Submodule.mem_iInf, Submodule.mem_comap,
    MvPolynomial.mem_weightedHomogeneousSubmodule]
  change (∀ s : Set.powersetCard V p,
    (x s).val.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (q - (p : ℤ))) ↔ _
  simp only [MvPolynomial.IsWeightedHomogeneous, integerWeight_degree]
  constructor
  · intro h s a ha
    have hh := h s ha
    omega
  · intro h s a ha
    have hh := h s a ha
    omega

private theorem piece_negative (I : Ideal (MvPolynomial V K)) {q : ℤ}
    (hq : q < 0) (p : ℕ) : piece I q p = ⊥ := by
  apply le_antisymm
  · intro x hx
    have he : x = 0 := by
      apply Finsupp.ext
      intro s
      apply Subtype.ext
      apply MvPolynomial.ext
      intro a
      change (x s).val.coeff a = 0
      by_contra hn
      have hd := (mem_piece_iff I q p x).mp hx s a hn
      have ha : (0 : ℤ) ≤ (a.degree : ℤ) := Int.natCast_nonneg _
      have hp : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg _
      omega
    simpa [he]
  · exact bot_le

private theorem eraseSign_eq_source (i : V) (s : Finset V) :
    eraseSign i s = TauCeti.ExteriorAlgebra.basisEraseSign i s :=
  (TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt i s).symm

private theorem eraseIndex_eq_source {p : ℕ} (s : Set.powersetCard V (p + 1))
    (j : {j // j ∈ s.val}) : eraseIndex s j = CommAlg.Koszul.eraseIndex s j := by
  apply Subtype.ext
  rfl

private theorem differential_eq_source (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    differential I p = FourPapers.Sublattice.actualIdealCoordinateDifferential I p := by
  apply Finsupp.lhom_ext
  intro s
  intro m
  change differential I p (Finsupp.single s m) = _
  rw [FourPapers.Sublattice.actualIdealCoordinateDifferential,
    LinearMap.restrictScalars_apply, CommAlg.Koszul.coordinateDifferential_single]
  simp only [differential, LinearMap.restrictScalars_apply, Finsupp.lsum_single,
    LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    LinearMap.lsmul_apply, eraseIndex_eq_source, eraseSign_eq_source]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul,mul_smul,Units.smul_def,Int.cast_smul_eq_zsmul]

private theorem previous_eq_source (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    previous I p = FourPapers.Sublattice.actualIdealPreviousDifferential I p := by
  cases p with
  | zero => rfl
  | succ p => exact differential_eq_source I p

private theorem piece_nat_eq (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : piece P.ideal (q : ℤ) p = actualIdealOrdinaryPiece P q p := by
  ext x
  rw [actualIdealOrdinaryPiece_mem_iff P hJ q p x, CommAlg.Grading.mem_piece,
    mem_piece_iff]
  constructor
  · intro h a ha
    have hc : (x a.1).val.coeff a.2.val ≠ 0 := by
      simpa only [idealCoordinatesToAmbient_repr] using ha
    have hd := h a.1 a.2.val hc
    simp only [FourPapers.Sublattice.quotientDegree, map_add, degree_faceExponent, Set.powersetCard.card_eq]
    exact_mod_cast hd
  · intro h s a ha
    have hc : (FourPapers.Sublattice.quotientCoefficientBasis (k := K) (∅ : Family V) p).repr
        (idealCoordinatesToAmbient P.ideal p x) ⟨s, ⟨a, emptyFamily_allowed a⟩⟩ ≠ 0 := by
      simpa only [idealCoordinatesToAmbient_repr] using ha
    have hd := h ⟨s, ⟨a, emptyFamily_allowed a⟩⟩ hc
    simp only [FourPapers.Sublattice.quotientDegree, map_add, degree_faceExponent, Set.powersetCard.card_eq] at hd
    exact_mod_cast hd

section OrdinarySourceStructures
local instance (priority := 2100) sourcePieceGroup
    (P : FourPapers.Sublattice.QuotientGroebnerData V K) (q p : ℕ) :
    AddCommGroup (actualIdealOrdinaryPiece P q p) :=
  Submodule.addCommGroup (R := K) (M := Set.powersetCard V p →₀ P.ideal) _
local instance (priority := 2100) sourcePieceModule
    (P : FourPapers.Sublattice.QuotientGroebnerData V K) (q p : ℕ) :
    Module K (actualIdealOrdinaryPiece P q p) :=
  Submodule.module (R := K) (M := Set.powersetCard V p →₀ P.ideal) _
local instance (priority := 2100) sourceKernelGroup
    (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : AddCommGroup (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) :=
  Submodule.addCommGroup (R := K) (M := actualIdealOrdinaryPiece P q p) _
local instance (priority := 2100) sourceKernelModule
    (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : Module K (LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)) :=
  Submodule.module (R := K) (M := actualIdealOrdinaryPiece P q p) _

private def cyclesEquiv (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : cycles P.ideal (q : ℤ) p ≃ₗ[K]
      LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p) where
  toFun x := ⟨⟨x.val, (piece_nat_eq P hJ q p).le x.property.2⟩, by
    apply Subtype.ext
    rw [actualIdealOrdinaryPrevious_val, ZeroMemClass.coe_zero]
    change actualIdealPreviousDifferential P.ideal p x.val = 0
    rw [← previous_eq_source]
    exact x.property.1⟩
  invFun x := ⟨x.val.val, ⟨by
    change previous P.ideal p x.val.val = 0
    rw [previous_eq_source]
    have hx := congrArg Subtype.val x.property
    rw [actualIdealOrdinaryPrevious_val, ZeroMemClass.coe_zero] at hx
    exact hx,
    (piece_nat_eq P hJ q p).ge x.val.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem boundaries_map (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) :
    (boundaries P.ideal (q : ℤ) p).map (cyclesEquiv P hJ q p).toLinearMap =
      LinearMap.range (FourPapers.FilteredHomology.boundaryMap
        (actualIdealOrdinaryDifferential P hJ q p)
        (actualIdealOrdinaryPrevious P hJ q p)
        (actualIdealOrdinaryDifferential_comp P hJ q p)) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x.val ∈ Submodule.map (differential P.ideal p)
      (piece P.ideal (q : ℤ) (p + 1)) at hx
    rcases hx with ⟨z, hz, hzx⟩
    refine ⟨⟨z, (piece_nat_eq P hJ q (p + 1)).le hz⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [BridgeAPI.boundaryMap_val, actualIdealOrdinaryDifferential_val, cyclesEquiv]
    change actualIdealCoordinateDifferential P.ideal p z = x.val
    rw [← differential_eq_source]
    exact hzx
  · rintro y ⟨z, rfl⟩
    let b := FourPapers.FilteredHomology.boundaryMap
      (actualIdealOrdinaryDifferential P hJ q p)
      (actualIdealOrdinaryPrevious P hJ q p)
      (actualIdealOrdinaryDifferential_comp P hJ q p) z
    refine ⟨(cyclesEquiv P hJ q p).symm b, ?_, by simp [b]⟩
    change ((cyclesEquiv P hJ q p).symm b).val ∈
      Submodule.map (differential P.ideal p) (piece P.ideal (q : ℤ) (p + 1))
    refine ⟨z.val, (piece_nat_eq P hJ q (p + 1)).ge z.property, ?_⟩
    simp only [cyclesEquiv, BridgeAPI.boundaryMap_val, actualIdealOrdinaryDifferential_val]
    change differential P.ideal p z.val = actualIdealCoordinateDifferential P.ideal p z.val
    rw [differential_eq_source]

private def homologyEquiv (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (q p : ℕ) : Homology P.ideal (q : ℤ) p ≃ₗ[K] actualIdealOrdinaryHomology P hJ q p :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv P hJ q p) (boundaries_map P hJ q p)

end OrdinarySourceStructures

private theorem betti_negative (I : Ideal (MvPolynomial V K)) {q : ℤ}
    (hq : q < 0) (p : ℕ) : betti I p q = 0 := by
  have hc : cycles I q p = ⊥ := by simp [cycles, piece_negative I hq p]
  haveI : Subsingleton (cycles I q p) := by rw [hc]; infer_instance
  unfold betti
  exact Module.finrank_zero_of_subsingleton

/-- The literal graded Koszul dimension agrees with the source's genuine
integer-graded derived Tor, via its proved homogeneous inclusion isomorphism. -/
theorem betti_eq_derivedTor (P : FourPapers.Sublattice.QuotientGroebnerData V K)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (p : ℕ) (q : ℤ) :
    betti P.ideal p q = ordinaryIntegerIdealBettiNumber P hJ p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, ordinaryIntegerIdealBettiNumber_nat,
      ordinaryIdealBettiNumber_eq_finrank]
    exact (homologyEquiv P hJ q.toNat p).finrank_eq
  · have hq' : q < 0 := lt_of_not_ge hq
    rw [betti_negative P.ideal hq', ordinaryIntegerIdealBettiNumber_negative P hJ p q hq']

end PalomarSublattice.Koszul

namespace PalomarSublattice
open Classical MvPolynomial
universe u
variable {N : ℕ} {K : Type u} [Field K]
/-- The original finite-variable orientation, used only for exterior signs. -/
noncomputable instance (priority := 2000) finiteVariableLinearOrder {d : ℕ} (n : Fin d → ℕ) :
    LinearOrder (FiniteVariable.{u} n) :=
  LinearOrder.lift' (Fintype.equivFin (FiniteVariable.{u} n)) (Fintype.equivFin _).injective
/-- The paper's original two rows on the specified vertex labels. -/
abbrev GraphRows (N : ℕ) : Fin 2 → ℕ := fun _ => N
/-- The actual exponent of x_i y_j. -/
def graphPairExponent (i j : Fin N) : FiniteVariable.{u} (GraphRows N) →₀ ℕ :=
  Finsupp.single ⟨0, ULift.up i⟩ 1 + Finsupp.single ⟨1, ULift.up j⟩ 1
/-- The actual edge binomial x_i y_j - x_j y_i. -/
def graphBinomial (i j : Fin N) : MvPolynomial (FiniteVariable.{u} (GraphRows N)) K :=
  monomial (graphPairExponent i j) 1 - monomial (graphPairExponent j i) 1
/-- Every edge binomial for the original labels, counted once with i<j. -/
def graphBinomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = graphBinomial i j}
/-- The literal binomial edge ideal. -/
def graphBinomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  Ideal.span (graphBinomialGenerators G)
/-- The edge monomials x_i y_j with i<j in the identical original labels. -/
def graphMonomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = monomial (graphPairExponent i j) 1}
/-- The literal initial edge-monomial ideal for the specified closed labeling. -/
def graphMonomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) K) :=
  Ideal.span (graphMonomialGenerators G)
/-- The specified labeling is closed: both lower and upper neighbors of each
vertex form cliques. This is not a hypothesis about some relabeling. -/
def ClosedLabeling (G : SimpleGraph (Fin N)) : Prop :=
  (∀ {a b c}, a < b → a < c → b ≠ c → G.Adj a b → G.Adj a c → G.Adj b c) ∧
  (∀ {a b c}, a < c → b < c → a ≠ b → G.Adj a c → G.Adj b c → G.Adj a b)

/-- Theorem1.1: every field, every positive power, every homological degree,
and every integer ordinary degree; no connectivity assumption or relabeling. -/
theorem closed_graph_betti_preservation (G : SimpleGraph (Fin N)) (hG : ClosedLabeling G)
    (s : ℕ) (hs : 0 < s) (p : ℕ) (q : ℤ) :
    Koszul.betti ((graphBinomialIdeal (K := K) G) ^ s) p q =
      Koszul.betti ((graphMonomialIdeal (K := K) G) ^ s) p q := by
  have hB : graphBinomialIdeal (K := K) G =
      FourPapers.Sublattice.graphBinomialIdeal (k := K) G := rfl
  have hM : graphMonomialIdeal (K := K) G =
      FourPapers.Sublattice.graphMonomialIdeal (K := K) G :=
    (FourPapers.Sublattice.graphMonomialIdeal_eq_span (K := K) G).symm
  rw [hB, hM, ← FourPapers.Sublattice.graphMonomialPowerData_ideal G s]
  change Koszul.betti (FourPapers.Sublattice.graphBinomialPowerData (K := K) G s).ideal p q =
    Koszul.betti (FourPapers.Sublattice.graphMonomialPowerData (K := K) G s).ideal p q
  rw [Koszul.betti_eq_derivedTor _ (FourPapers.Sublattice.graphBinomialPower_homogeneous G s),
    Koszul.betti_eq_derivedTor _ (FourPapers.Sublattice.monomialIdeal_ordinary_homogeneous _)]
  exact FourPapers.Sublattice.theorem11_integer_bettiEquality G hG s hs p q
end PalomarSublattice

namespace PalomarSublattice.Rees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]
/-- The actual image of the finite Rees polynomial presentation in S[t]. -/
def Image (E : Finset (FiniteTuple n)) (k : Type u) [Field k] :=
  (finiteReesPresentationMap.{u} E k).range
/-- The literal ordinary exterior algebra of the row-variable coordinate space. -/
abbrev Wedge := ExteriorAlgebra k (FiniteVariable.{u} n → k)
/-- The actual ordinary Koszul algebra with its genuine Rees-image coefficients. -/
abbrev TensorAlgebra := Image E k ⊗[k] Wedge (n := n) (k := k)
instance (priority := 2000) tensorRing : Ring (TensorAlgebra (E := E) (k := k)) := Algebra.TensorProduct.instRing
instance (priority := 2000) tensorAlgebra : Algebra k (TensorAlgebra (E := E) (k := k)) := Algebra.TensorProduct.instAlgebra
/-- Every base polynomial variable belongs to the displayed presentation image. -/
theorem base_mem (v : FiniteVariable.{u} n) :
    X (some v) ∈ Image E k := by
  change X (some v) ∈ FourPapers.Sublattice.finiteReesImage E k
  rw [← FourPapers.Sublattice.finiteReesBaseVariable_val (k := k) (E := E) v]
  exact (FourPapers.Sublattice.finiteReesBaseVariable (k := k) E v).property

/-- The actual base variable, as an element of the Rees image. -/
def baseVariable (v : FiniteVariable.{u} n) : Image E k := ⟨X (some v), base_mem v⟩
/-- Ordinary exterior contraction by the v-th coordinate functional. -/
def contraction (v : FiniteVariable.{u} n) : Wedge (n := n) (k := k) →ₗ[k] Wedge (n := n) (k := k) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (FiniteVariable.{u} n → k)))
    ((Pi.basisFun k (FiniteVariable.{u} n)).coord v)
/-- The literal Koszul differential: variable multiplication tensor contraction. -/
def differential : Module.End k (TensorAlgebra (E := E) (k := k)) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k (baseVariable (E := E) v)) (contraction v)
theorem sourceClosed (hE : finiteLatticeClosed n E) :
    FourPapers.Sublattice.finiteLatticeClosed n E := by
  exact hE

private theorem baseVariable_eq_source (v : FiniteVariable.{u} n) :
    baseVariable (E := E) (k := k) v = FourPapers.Sublattice.finiteReesBaseVariable E v := by
  apply Subtype.ext
  exact (FourPapers.Sublattice.finiteReesBaseVariable_val (k := k) (E := E) v).symm

private theorem differential_eq_source :
    differential (E := E) (k := k) = FourPapers.Sublattice.reesKoszulTensorDifferential := by
  simp only [differential, FourPapers.Sublattice.reesKoszulTensorDifferential,
    baseVariable_eq_source]
  rfl

private theorem differential_eq_DGA (hE : finiteLatticeClosed n E) :
    differential (E := E) (k := k) = (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).d :=
  differential_eq_source.trans (FourPapers.Sublattice.reesKoszulTensorDGA_d (k := k) (sourceClosed hE)).symm

/-- The literal Koszul differential kills the unit. -/
theorem d_one (hE : finiteLatticeClosed n E) : differential (E := E) (k := k) 1 = 0 := by
  rw [differential_eq_DGA hE]
  exact (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).map_one

/-- Products of actual Koszul cycles are actual Koszul cycles. -/
theorem cycles_mul (hE : finiteLatticeClosed n E) (x y : TensorAlgebra (E := E) (k := k))
    (hx : differential x = 0) (hy : differential y = 0) : differential (x * y) = 0 := by
  let D : FourPapers.ParityDifferential k (TensorAlgebra (E := E) (k := k)) := FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)
  have hxD : D.d x = 0 := by rw [← differential_eq_DGA hE]; exact hx
  have hyD : D.d y = 0 := by rw [← differential_eq_DGA hE]; exact hy
  rw [differential_eq_DGA hE, D.leibniz, hxD, hyD]
  simp

/-- The actual cycles subalgebra of the literal ordinary Koszul differential. -/
def Cycles (hE : finiteLatticeClosed n E) : Subalgebra k (TensorAlgebra (E := E) (k := k)) :=
  (LinearMap.ker differential).toSubalgebra (d_one hE) (cycles_mul hE)
/-- The canonical noncommutative cycle ring, explicitly selected. -/
instance (priority := 2000) cyclesRing (hE : finiteLatticeClosed n E) : Ring (Cycles (k := k) hE) :=
  Subalgebra.toRing (Cycles (k := k) hE)
/-- The canonical scalar action on actual cycles, explicitly selected. -/
instance (priority := 2000) cyclesAlgebra (hE : finiteLatticeClosed n E) : Algebra k (Cycles (k := k) hE) :=
  Subalgebra.algebra (Cycles (k := k) hE)
/-- Zero is an actual Koszul boundary. -/
theorem boundary_zero (hE : finiteLatticeClosed n E) :
    (0 : Cycles (k := k) hE).val ∈ LinearMap.range differential := by exact ⟨0, map_zero _⟩
/-- Sums of actual boundaries are actual boundaries. -/
theorem boundary_add (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) (hy : y.val ∈ LinearMap.range differential) :
    (x + y).val ∈ LinearMap.range differential := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by simpa only [map_add, ha, hb, Subalgebra.coe_add]⟩
/-- Negatives of actual boundaries are actual boundaries. -/
theorem boundary_neg (hE : finiteLatticeClosed n E) {x : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) :
    (-x).val ∈ LinearMap.range differential := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨-a, by simpa only [map_neg, ha, Subalgebra.coe_neg]⟩
/-- Left multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_left (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hy : y.val ∈ LinearMap.range differential) :
    (x * y).val ∈ LinearMap.range differential := by
  let D : FourPapers.ParityDifferential k (TensorAlgebra (E := E) (k := k)) := FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)
  obtain ⟨b, hb⟩ := hy
  have hxD : D.d x.val = 0 := by rw [← differential_eq_DGA hE]; exact x.property
  have hbD : D.d b = y.val := by rw [← differential_eq_DGA hE]; exact hb
  refine ⟨D.parity x.val * b, ?_⟩
  rw [differential_eq_DGA hE, D.leibniz, D.parity_cycle hxD, D.parity_square, hbD]
  simp

/-- Right multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_right (hE : finiteLatticeClosed n E) {x y : Cycles (k := k) hE}
    (hx : x.val ∈ LinearMap.range differential) :
    (x * y).val ∈ LinearMap.range differential := by
  let D : FourPapers.ParityDifferential k (TensorAlgebra (E := E) (k := k)) := FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)
  obtain ⟨a, ha⟩ := hx
  have hyD : D.d y.val = 0 := by rw [← differential_eq_DGA hE]; exact y.property
  have haD : D.d a = x.val := by rw [← differential_eq_DGA hE]; exact ha
  refine ⟨a * y.val, ?_⟩
  rw [differential_eq_DGA hE, D.leibniz, hyD, haD]
  simp

/-- The genuine two-sided ideal of Koszul boundaries in actual cycles. -/
def Boundaries (hE : finiteLatticeClosed n E) : TwoSidedIdeal (Cycles (k := k) hE) :=
  TwoSidedIdeal.mk' {z | z.val ∈ LinearMap.range differential}
    (boundary_zero hE) (boundary_add hE) (boundary_neg hE)
    (boundary_left hE) (boundary_right hE)
/-- The actual homology algebra, cycles modulo actual boundaries. -/
abbrev Homology (hE : finiteLatticeClosed n E) :=
  _root_.Quotient (Submodule.quotientRel (R := Cycles (k := k) hE) (M := Cycles (k := k) hE)
    (Boundaries (k := k) hE).asIdeal)
instance (priority := 2000) homologyRing (hE : finiteLatticeClosed n E) : Ring (Homology (k := k) hE) :=
  Ideal.Quotient.ring (Boundaries (k := k) hE).asIdeal
instance (priority := 2000) homologyAlgebra (hE : finiteLatticeClosed n E) : Algebra k (Homology (k := k) hE) :=
  Ideal.Quotient.algebra k (A := Cycles (k := k) hE) (I := (Boundaries (k := k) hE).asIdeal)
/-- The actual projection from cycles to their homology classes. -/
def classMap (hE : finiteLatticeClosed n E) : Cycles (k := k) hE →ₐ[k] Homology (k := k) hE :=
  Ideal.Quotient.mkₐ k (Boundaries (k := k) hE).asIdeal
/-- All exponent vectors actually occurring in the image monomial algebra. -/
def ExponentMonoid := AddMonoidHom.mrange (finiteReesExponentMap.{u} E)
/-- Every genuine image-monoid monomial belongs to the presentation image. -/
theorem monomial_mem (a : ExponentMonoid (E := E)) :
    monomial a.val (1 : k) ∈ Image E k := by
  change monomial a.val (1 : k) ∈ FourPapers.Sublattice.finiteReesImage E k
  rw [← FourPapers.Sublattice.finiteReesImageBasis_val E k a]
  exact (FourPapers.Sublattice.finiteReesImageBasis E k a).property

/-- The literal image monomial represented by that exponent. -/
def coefficientMonomial (a : ExponentMonoid (E := E)) : Image E k :=
  ⟨monomial a.val 1, monomial_mem a⟩
/-- The actual standard exterior wedge indexed by a coordinate subset. -/
def wedgeBasis : Module.Basis (Finset (FiniteVariable.{u} n)) k (Wedge (n := n) (k := k)) :=
  (Pi.basisFun k (FiniteVariable.{u} n)).ExteriorAlgebra
/-- Rees degree one in the actual tensor algebra: the auxiliary exponent is
exactly one, and every exterior wedge is allowed. -/
def DegreeOnePiece : Submodule k (TensorAlgebra (E := E) (k := k)) :=
  Submodule.span k {z | ∃ a : ExponentMonoid (E := E), a.val none = 1 ∧
    ∃ F : Finset (FiniteVariable.{u} n), z = coefficientMonomial a ⊗ₜ[k] wedgeBasis F}
/-- Actual homology classes admitting an actual Rees-degree-one cycle representative. -/
def FirstClasses (hE : finiteLatticeClosed n E) : Set (Homology (k := k) hE) :=
  {z | ∃ x : Cycles (k := k) hE, x.val ∈ DegreeOnePiece ∧ classMap (k := k) hE x = z}
end PalomarSublattice.Rees

namespace PalomarSublattice.Rees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]
section ReesTransportStructures
variable (hE : finiteLatticeClosed n E)
local instance (priority := 2100) sourceCyclesRing :
    Ring (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).cycles :=
  Subalgebra.toRing _
local instance (priority := 2100) sourceCyclesAlgebra :
    Algebra k (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).cycles :=
  Subalgebra.algebra _
local instance (priority := 2100) sourceHomologyRing :
    Ring (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).Homology :=
  Ideal.Quotient.ring
    (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).boundaries.asIdeal
local instance (priority := 2100) sourceHomologyAlgebra :
    Algebra k (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).Homology :=
  Ideal.Quotient.algebra k
    (A := (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).cycles)
    (I := (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).boundaries.asIdeal)

private def cyclesEquiv :
    Cycles (k := k) hE ≃ₐ[k] (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).cycles where
  toFun x := ⟨x.val, by
    change (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).d x.val = 0
    rw [← differential_eq_DGA hE]
    exact x.property⟩
  invFun x := ⟨x.val, by
    change differential x.val = 0
    rw [differential_eq_DGA hE]
    exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  commutes' c := Subtype.ext rfl

private theorem mem_boundaries (x : Cycles (k := k) hE) :
    x ∈ Boundaries hE ↔ x.val ∈ LinearMap.range differential :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

private def homologyEquiv :
    Homology (k := k) hE ≃ₐ[k] FourPapers.Sublattice.ReesKoszulHomology (k := k) (sourceClosed hE) :=
  Ideal.quotientEquivAlg (Boundaries hE).asIdeal
    (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).boundaries.asIdeal
    (cyclesEquiv hE)
    (@NoncommBridgeAPI.map_asIdeal_of_mem_iff
      (Cycles (k := k) hE)
      (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).cycles
      (cyclesRing hE) (sourceCyclesRing hE)
      (cyclesEquiv hE).toRingEquiv (Boundaries hE)
      (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).boundaries
      (by
        intro x
        rw [mem_boundaries,FourPapers.ParityDifferential.mem_boundaries]
        change x.val ∈ LinearMap.range differential ↔ x.val ∈ LinearMap.range
          (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).d
        rw [← differential_eq_DGA hE])).symm

private theorem classMap_transport (x : Cycles (k := k) hE) :
    homologyEquiv hE (classMap hE x) =
      (FourPapers.Sublattice.reesKoszulTensorDGA (k := k) (sourceClosed hE)).classMap (cyclesEquiv hE x) := rfl

private theorem coefficientMonomial_eq_source (a : ExponentMonoid (E := E)) :
    coefficientMonomial (k := k) a = FourPapers.Sublattice.finiteReesImageBasis E k a := by
  apply Subtype.ext
  exact (FourPapers.Sublattice.finiteReesImageBasis_val E k a).symm

private theorem degreeOnePiece_eq_source : DegreeOnePiece (E := E) (k := k) =
    FourPapers.Sublattice.actualReesDegreePiece (E := E) (k := k) 1 := by
  unfold DegreeOnePiece FourPapers.Sublattice.actualReesDegreePiece
  apply congrArg (Submodule.span k)
  ext z
  constructor
  · rintro ⟨a, ha, F, rfl⟩
    refine ⟨(a, F), ha, ?_⟩
    simp only [FourPapers.Sublattice.reesTensorBasis, Module.Basis.tensorProduct_apply,
      coefficientMonomial_eq_source]
    rfl
  · rintro ⟨⟨a, F⟩, ha, rfl⟩
    refine ⟨a, ha, F, ?_⟩
    simp only [FourPapers.Sublattice.reesTensorBasis, Module.Basis.tensorProduct_apply,
      coefficientMonomial_eq_source]
    rfl

private theorem firstClasses_transport :
    homologyEquiv hE '' FirstClasses (k := k) hE =
      FourPapers.Sublattice.actualFirstReesClasses (k := k) (sourceClosed hE) := by
  ext z
  constructor
  · rintro ⟨x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨cyclesEquiv hE c, ?_, (classMap_transport hE c).symm⟩
    change c.val ∈ FourPapers.Sublattice.actualReesDegreePiece 1
    rw [← degreeOnePiece_eq_source]
    exact hc
  · rintro ⟨c, hc, rfl⟩
    let x := (cyclesEquiv (k := k) hE).symm c
    refine ⟨classMap hE x, ⟨x, ?_, rfl⟩, ?_⟩
    · change c.val ∈ DegreeOnePiece
      rw [degreeOnePiece_eq_source]
      exact hc
    · rw [classMap_transport]
      simp only [x, AlgEquiv.apply_symm_apply]

end ReesTransportStructures

theorem generated_in_degree_one (hE : finiteLatticeClosed n E) :
    Algebra.adjoin k (FirstClasses (k := k) hE) = ⊤ := by
  let S := Algebra.adjoin k (FirstClasses (k := k) hE)
  let e := homologyEquiv (k := k) hE
  have h : Algebra.adjoin k (FourPapers.Sublattice.actualFirstReesClasses (k := k) (sourceClosed hE)) ≤
      S.comap e.symm.toAlgHom := by
    apply Algebra.adjoin_le
    intro z hz
    have hz' : z ∈ e '' FirstClasses (k := k) hE := by
      rw [firstClasses_transport]
      exact hz
    obtain ⟨x, hx, rfl⟩ := hz'
    change e.symm (e x) ∈ S
    rw [e.symm_apply_apply]
    change x ∈ Algebra.adjoin k (FirstClasses (k := k) hE)
    exact Algebra.subset_adjoin hx
  rw [FourPapers.Sublattice.reesKoszulHomology_generated_in_degree_one (sourceClosed hE)] at h
  apply top_unique
  intro z _
  have hz := h (show e z ∈ (⊤ : Subalgebra k _) from trivial)
  change e.symm (e z) ∈ S at hz
  simpa only [e.symm_apply_apply] using hz
end PalomarSublattice.Rees

/- Independent signed fine polynomial Koszul model draft; unelaborated.
   All coefficient modules below are actual ideals or actual polynomial quotients. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
/-- The actual signed fine degree of one polynomial variable. -/
def variableDegree (v : V) : V →₀ ℤ := Finsupp.single v 1
/-- The signed fine degree carried by an exterior wedge. -/
def exteriorDegree (s : Finset V) : V →₀ ℤ := ∑ v ∈ s, variableDegree v
/-- The literal signed fine homogeneous polynomial submodule. -/
def polynomialPiece (a : V →₀ ℤ) : Submodule k (MvPolynomial V k) :=
  weightedHomogeneousSubmodule k variableDegree a
/-- The actual ideal's homogeneous coefficient submodule, as a submodule of that ideal. -/
def idealCoefficientPiece (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) : Submodule k I :=
  (polynomialPiece a).comap (I.subtype.restrictScalars k)
/-- The actual polynomial quotient's homogeneous coefficient submodule, obtained
by the literal quotient map on homogeneous polynomials. -/
def quotientCoefficientPiece (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) :
    Submodule k (MvPolynomial V k ⧸ I) :=
  (polynomialPiece a).map (Ideal.Quotient.mkₐ k I).toLinearMap
section Coefficients
variable {M : Type u} [AddCommGroup M] [Module (MvPolynomial V k) M]
  [Module k M] [IsScalarTower k (MvPolynomial V k) M]
/-- Actual coefficient Koszul chains in exterior degree p. -/
abbrev Coordinates (M : Type u) [AddCommGroup M] (p : ℕ) := Set.powersetCard V p →₀ M
/-- The ordinary signed variable-multiplication differential on actual coefficient chains. -/
def differential (p : ℕ) : Coordinates (V := V) M (p + 1) →ₗ[k] Coordinates (V := V) M p :=
  (Finsupp.lsum (MvPolynomial V k) (fun s : Set.powersetCard V (p + 1) =>
    ∑ j : {j // j ∈ s.val},
      (Finsupp.lsingle (Koszul.eraseIndex s j)).comp
        (LinearMap.lsmul (MvPolynomial V k) M
          (X j.val * (((Koszul.eraseSign j.val s.val : ℤˣ) : ℤ) : MvPolynomial V k))))).restrictScalars k
/-- Outgoing degree-zero differential is exactly zero. -/
def previous : ∀ p : ℕ, Coordinates (V := V) M p →ₗ[k] Coordinates (V := V) M p.pred
  | 0 => 0
  | p + 1 => differential p
/-- Signed fine degree alpha: each actual coefficient has degree alpha minus
its exterior-wedge degree, including negative coordinates without a zero convention. -/
def piece (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (Coordinates (V := V) M p) :=
  ⨅ s : Set.powersetCard V p, (C (a - exteriorDegree s.val)).comap (Finsupp.lapply s)
/-- Genuine signed-fine cycles in the actual coefficient Koszul chains. -/
def cycles (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (Coordinates (V := V) M p) :=
  LinearMap.ker (previous (k := k) (M := M) p) ⊓ piece C a p
/-- Canonical additive group of the actual signed-fine cycle submodule. -/
instance cyclesAddCommGroup (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    AddCommGroup (cycles C a p) :=
  Submodule.addCommGroup (R := k) (M := Coordinates (V := V) M p) (cycles C a p)
/-- Boundaries coming from the actual preceding signed-fine component. -/
def boundaries (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :
    Submodule k (cycles C a p) :=
  (Submodule.map (differential (k := k) (M := M) p) (piece C a (p + 1))).comap
    (cycles C a p).subtype
/-- Actual signed-fine Koszul homology as the literal cycle/boundary quotient. -/
abbrev Homology (C : (V →₀ ℤ) → Submodule k M) (a : V →₀ ℤ) (p : ℕ) :=
  (cycles C a p) ⧸ boundaries C a p
/-- Canonical additive group on the literal signed-fine cycle/boundary quotient. -/
instance homologyAddCommGroup (C : (V →₀ ℤ) → Submodule k M)
    (a : V →₀ ℤ) (p : ℕ) : AddCommGroup (Homology C a p) :=
  Submodule.Quotient.addCommGroup (R := k) (M := cycles C a p) (boundaries C a p)
/-- Canonical coefficient module on that same signed-fine homology quotient. -/
instance homologyModule (C : (V →₀ ℤ) → Submodule k M)
    (a : V →₀ ℤ) (p : ℕ) : Module k (Homology C a p) :=
  Submodule.Quotient.module (R := k) (M := cycles C a p) (boundaries C a p)
end Coefficients
end PalomarSublattice.FineKoszul
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Dimension of actual ideal-coefficient signed-fine Koszul homology. -/
def idealBetti (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) (p : ℕ) : ℕ :=
  Module.finrank k (Homology (idealCoefficientPiece I) a p)
/-- Dimension of actual quotient-coefficient signed-fine Koszul homology. -/
def quotientBetti (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) (p : ℕ) : ℕ :=
  Module.finrank k (Homology (quotientCoefficientPiece I) a p)
end PalomarSublattice.FineKoszul
namespace PalomarSublattice
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ)
/-- The actual row monomial selecting one variable from every row. -/
def rowMonomial {k : Type u} [Field k] (a : FiniteTuple n) :
    MvPolynomial (FiniteVariable.{u} n) k := ∏ r, X ⟨r, ULift.up (a r)⟩
/-- The literal sublattice ideal generated by the row monomials. -/
def sublatticeIdeal {k : Type u} [Field k] (E : Finset (FiniteTuple n)) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  Ideal.span (rowMonomial n '' (E : Set (FiniteTuple n)))
/-- The manuscript's exact lexicographic predecessor relation. -/
def lexBefore (b a : FiniteTuple n) : Prop :=
  ∃ r, b r < a r ∧ ∀ s < r, b s = a s
/-- Exactly the tuples before the displayed generator, with the original labels. -/
def lexPrefix (E : Finset (FiniteTuple n)) (a : FiniteTuple n) : Finset (FiniteTuple n) :=
  E.filter (fun b => lexBefore n b a)
/-- The genuine predecessor colon in the actual polynomial ring. -/
def predecessorColon {k : Type u} [Field k] (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  (sublatticeIdeal n (lexPrefix n E a)).colon {rowMonomial n a}
/-- Monotone multichains, allowing repetitions, of exactly the displayed length. -/
def Multichain (E : Finset (FiniteTuple n)) (m : ℕ) :=
  {w : Fin m → E // Monotone (fun s => (w s).val)}
/-- Every such multichain belongs to the actual finite product of the finite tuple set. -/
theorem multichain_finite (E : Finset (FiniteTuple n)) (m : ℕ) : Finite (Multichain n E m) :=
  Finite.of_injective (fun w : Multichain n E m => w.val) Subtype.val_injective
noncomputable instance (priority := 2000) multichainFintype (E : Finset (FiniteTuple n)) (m : ℕ) :
    Fintype (Multichain n E m) := @Fintype.ofFinite _ (multichain_finite n E m)
/-- The exact sum of generator exponents along the full multichain. -/
def chainShift {E : Finset (FiniteTuple n)} {m : ℕ} (w : Multichain n E m) :=
  ∑ s, finiteRowExponent n (w.val s).val
/-- Ordinary coordinatewise inclusion of natural exponents into signed fine degrees. -/
def integerExponent {V : Type u} (a : V →₀ ℕ) : V →₀ ℤ := a.mapRange Int.ofNat (by rfl)
/-- The actual sum of all predecessor colons along the multichain. -/
def chainCoefficientIdeal {k : Type u} [Field k] {E : Finset (FiniteTuple n)} {m : ℕ}
    (w : Multichain n E m) : Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  ⨆ s : Fin m, predecessorColon n E (w.val s).val
end PalomarSublattice

/- Source bridge work for the actual signed-fine polynomial model.
This fragment is unelaborated and is not added to the frozen335line diagnostic. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem variableWeight_eq_integerExponent (b : V →₀ ℕ) :
    Finsupp.weight (variableDegree (V := V)) b = FourPapers.Sublattice.integerExponent b := by
  ext v
  simp [Finsupp.weight_eq_sum, variableDegree, Finsupp.sum, Finsupp.sum_apply,
    Finsupp.single_apply, FourPapers.Sublattice.integerExponent]

private theorem integerExponent_add (a b : V →₀ ℕ) :
    FourPapers.Sublattice.integerExponent (a + b) =
      FourPapers.Sublattice.integerExponent a + FourPapers.Sublattice.integerExponent b := by
  ext v
  simp [FourPapers.Sublattice.integerExponent]

private theorem exteriorDegree_eq_integerExponent (s : Finset V) :
    exteriorDegree s = FourPapers.Sublattice.integerExponent (CommAlg.Koszul.faceExponent s) := by
  ext v
  simp [exteriorDegree, variableDegree, CommAlg.Koszul.faceExponent,
    FourPapers.Sublattice.integerExponent, Finsupp.single_apply]

/-- The signed polynomial grading is literally the regraded monomial basis
piece, rather than a combinatorial nonvanishing predicate. -/
private theorem polynomialPiece_eq_basisPiece (a : V →₀ ℤ) :
    polynomialPiece (k := k) a = CommAlg.Grading.Piece
      (MvPolynomial.basisMonomials V k) FourPapers.Sublattice.integerExponent a := by
  ext f
  rw [CommAlg.Grading.mem_piece]
  change f.IsWeightedHomogeneous variableDegree a ↔ _
  simp only [MvPolynomial.IsWeightedHomogeneous, variableWeight_eq_integerExponent]
  rfl

private theorem monomialBasis_repr_coefficient (B : Family V)
    (x : monomialIdeal k B) (b : {b : Exponent V // Contains B b}) :
    (monomialBasis (k := k) B).repr x b = x.val.coeff b.val := by
  let L : monomialIdeal k B →ₗ[k] k :=
    (MvPolynomial.lcoeff k b.val).comp ((monomialIdeal k B).subtype.restrictScalars k)
  have hL : (monomialBasis (k := k) B).coord b = L := by
    apply (monomialBasis (k := k) B).ext
    intro c
    simp [L, monomialBasis_val, MvPolynomial.coeff_monomial,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Subtype.ext_iff]
  exact LinearMap.congr_fun hL x

private theorem monomialCoefficientBasis_repr_coefficient (B : Family V) (p : ℕ)
    (x : Coordinates (V := V) (monomialIdeal k B) p) (t : MonomialIndex B p) :
    (monomialCoefficientBasis (k := k) B p).repr x t = (x t.1).val.coeff t.2.val := by
  rw [monomialCoefficientBasis, Finsupp.basis_repr]
  exact monomialBasis_repr_coefficient B (x t.1) t.2

private theorem mem_idealPiece_iff (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ)
    (p : ℕ) (x : Coordinates (V := V) I p) :
    x ∈ piece (idealCoefficientPiece I) a p ↔
      ∀ s : Set.powersetCard V p, ∀ b : V →₀ ℕ,
        (x s).val.coeff b ≠ 0 →
          FourPapers.Sublattice.integerExponent b + exteriorDegree s.val = a := by
  simp only [piece, Submodule.mem_iInf, Submodule.mem_comap,
    idealCoefficientPiece, polynomialPiece, MvPolynomial.mem_weightedHomogeneousSubmodule,
    MvPolynomial.IsWeightedHomogeneous, variableWeight_eq_integerExponent]
  constructor
  · intro h s b hb
    exact (eq_sub_iff_add_eq).mp (h s hb)
  · intro h s b hb
    exact (eq_sub_iff_add_eq).mpr (h s b hb)

private theorem idealPiece_nat_eq (B : Family V) (a : Exponent V) (p : ℕ) :
    piece (idealCoefficientPiece (monomialIdeal k B)) (FourPapers.Sublattice.integerExponent a) p =
      homogeneousPiece (k := k) B a p := by
  ext x
  rw [mem_idealPiece_iff, homogeneousPiece, CommAlg.Grading.mem_piece]
  constructor
  · intro h t ht
    have hd := h t.1 t.2.val ((monomialCoefficientBasis_repr_coefficient B p x t) ▸ ht)
    rw [exteriorDegree_eq_integerExponent] at hd
    rw [← integerExponent_add] at hd
    exact FourPapers.Sublattice.integerExponent_injective hd
  · intro h s b hb
    have hcontains : Contains B b := by
      exact (CommAlg.Polymatroid.mem_monomialIdeal_iff B (x s).val).mp (x s).property
        b (MvPolynomial.mem_support_iff.mpr hb)
    have hc : (monomialCoefficientBasis (k := k) B p).repr x ⟨s,⟨b,hcontains⟩⟩ ≠ 0 := by
      rwa [monomialCoefficientBasis_repr_coefficient]
    have hd := congrArg FourPapers.Sublattice.integerExponent (h ⟨s,⟨b,hcontains⟩⟩ hc)
    simpa only [monomialDegree, integerExponent_add, exteriorDegree_eq_integerExponent] using hd

/-- Negative signed coordinates make the actual ideal chain piece zero. -/
private theorem idealPiece_negative (I : Ideal (MvPolynomial V k))
    (a : V →₀ ℤ) (p : ℕ) {v : V} (ha : a v < 0) :
    piece (idealCoefficientPiece I) a p = ⊥ := by
  apply le_antisymm
  · intro x hx
    have he : x = 0 := by
      apply Finsupp.ext
      intro s
      apply Subtype.ext
      apply MvPolynomial.ext
      intro b
      change (x s).val.coeff b = 0
      by_contra hb
      have hd := congrArg (fun c : V →₀ ℤ => c v) ((mem_idealPiece_iff I a p x).mp hx s b hb)
      have hb0 := FourPapers.Sublattice.integerExponent_nonneg b v
      have hs0 := FourPapers.Sublattice.integerExponent_nonneg (CommAlg.Koszul.faceExponent s.val) v
      rw [exteriorDegree_eq_integerExponent] at hd
      simp only [Finsupp.add_apply] at hd
      omega
    simpa [he]
  · exact bot_le

end PalomarSublattice.FineKoszul

namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Changing equal defining ideals preserves the actual quotient, its scalar
structure and the class of every polynomial. -/
private def quotientCoefficientEquiv (B : Family V) :
    (MvPolynomial V k ⧸ monomialIdeal k B) ≃ₐ[k] CoefficientQuotient (k := k) B :=
  Ideal.quotientEquivAlgOfEq k (forbiddenIdeal_eq_monomialIdeal B).symm

private theorem polynomialPiece_eq_monomialSpan (a : V →₀ ℤ) :
    polynomialPiece (k := k) a = Submodule.span k
      ((fun b : V →₀ ℕ => MvPolynomial.monomial b (1 : k)) ''
        {b | FourPapers.Sublattice.integerExponent b = a}) := by
  rw [polynomialPiece_eq_basisPiece, CommAlg.Grading.Piece]
  rfl

/-- The actual quotient's signed homogeneous coefficient image agrees with
its ordinary allowed-monomial basis grading, via the canonical quotient map. -/
private theorem quotientCoefficientPiece_map (B : Family V) (a : V →₀ ℤ) :
    (quotientCoefficientPiece (monomialIdeal k B) a).map
      (quotientCoefficientEquiv B).toLinearMap =
    CommAlg.Grading.Piece (quotientMonomialBasis (k := k) B)
      (fun b => FourPapers.Sublattice.integerExponent b.val) a := by
  rw [quotientCoefficientPiece, polynomialPiece_eq_monomialSpan, ← Submodule.map_comp,
    Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    change (quotientCoefficientEquiv B)
      (Ideal.Quotient.mk _ (MvPolynomial.monomial b (1 : k))) ∈ _
    rw [quotientCoefficientEquiv, Ideal.quotientEquivAlgOfEq_mk]
    change quotientMonomial (k := k) B b ∈ _
    by_cases hallowed : QuotientAllowed B b
    · rw [← quotientMonomialBasis_apply B ⟨b,hallowed⟩]
      have hmem := CommAlg.Grading.basis_mem_piece
        (quotientMonomialBasis (k := k) B)
        (fun b => FourPapers.Sublattice.integerExponent b.val) ⟨b,hallowed⟩
      rw [show FourPapers.Sublattice.integerExponent b = a from hb] at hmem
      exact hmem
    · rw [quotientMonomial_zero B b hallowed]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro y ⟨b, hb, rfl⟩
    change quotientMonomialBasis (k := k) B b ∈ _
    rw [quotientMonomialBasis_apply]
    apply Submodule.subset_span
    refine ⟨MvPolynomial.monomial b.val 1, ⟨b.val,hb,rfl⟩, ?_⟩
    exact Ideal.quotientEquivAlgOfEq_mk k
      (forbiddenIdeal_eq_monomialIdeal (k := k) B).symm (MvPolynomial.monomial b.val (1 : k))

end PalomarSublattice.FineKoszul

/- Additional genuine-homology bridge draft; unelaborated and not in the
frozen338line diagnostic. Depends on fine-betti-bridge-front.lean. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open CategoryTheory FourPapers.Sublattice FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem idealDifferential_eq_source (B : Family V) (p : ℕ) :
    differential (k := k) (M := monomialIdeal k B) p =
      CommAlg.Koszul.monomialDifferential (k := k) B p := by
  apply Finsupp.lhom_ext
  intro s
  intro m
  change differential (k := k) (M := monomialIdeal k B) p (Finsupp.single s m) = _
  rw [CommAlg.Koszul.monomialDifferential, LinearMap.restrictScalars_apply,
    CommAlg.Koszul.coordinateDifferential_single]
  simp only [differential, LinearMap.restrictScalars_apply, Finsupp.lsum_single,
    LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.lsmul_apply,
    PalomarSublattice.Koszul.eraseIndex_eq_source, PalomarSublattice.Koszul.eraseSign_eq_source]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul,mul_smul,Units.smul_def,Int.cast_smul_eq_zsmul]

private def idealSourcePrevious (B : Family V) (a : Exponent V) :
    ∀ p : ℕ, homogeneousPiece (k := k) B a p →ₗ[k] homogeneousPiece (k := k) B a p.pred
  | 0 => 0
  | p + 1 => homogeneousDifferential (k := k) B a p

private theorem idealSourcePrevious_comp (B : Family V) (a : Exponent V) (p : ℕ) :
    idealSourcePrevious (k := k) B a p ∘ₗ homogeneousDifferential (k := k) B a p = 0 := by
  cases p with
  | zero => simp [idealSourcePrevious]
  | succ p => exact homogeneousDifferential_comp B a p

private def idealSourceShortComplexIso (B : Family V) (a : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B a).sc' (p + 1) p p.pred ≅
      linearShortComplex (homogeneousDifferential (k := k) B a p)
        (idealSourcePrevious (k := k) B a p) (idealSourcePrevious_comp (k := k) B a p) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [linearShortComplex, homogeneousComplex, ChainComplex.of_d])
    (by cases p <;> simp [linearShortComplex, homogeneousComplex,
      idealSourcePrevious, ChainComplex.of_d, ChainComplex.of_d_ne])

private def idealSourceHomologyIso (B : Family V) (a : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B a).homology p ≅
      ModuleCat.of k (FourPapers.FilteredHomology.Homology
        (homogeneousDifferential (k := k) B a p) (idealSourcePrevious (k := k) B a p)
        (idealSourcePrevious_comp (k := k) B a p)) :=
  ((homogeneousComplex (k := k) B a).homologyIsoSc' (p + 1) p p.pred
    (by simp) (by cases p <;> simp)) ≪≫
    ShortComplex.homologyMapIso (idealSourceShortComplexIso (k := k) B a p) ≪≫
      categoricalHomologyIso (homogeneousDifferential (k := k) B a p)
        (idealSourcePrevious (k := k) B a p) (idealSourcePrevious_comp (k := k) B a p)

private theorem idealPrevious_val (B : Family V) (a : Exponent V) (p : ℕ)
    (x : homogeneousPiece (k := k) B a p) :
    (idealSourcePrevious (k := k) B a p x).val = previous (k := k) (M := monomialIdeal k B) p x.val := by
  cases p with
  | zero => rfl
  | succ p =>
    change monomialDifferential (k := k) B p x.val = _
    change monomialDifferential (k := k) B p x.val =
      differential (k := k) (M := monomialIdeal k B) p x.val
    exact LinearMap.congr_fun (idealDifferential_eq_source (k := k) B p).symm x.val

private def idealCyclesEquiv (B : Family V) (a : Exponent V) (p : ℕ) :
    cycles (idealCoefficientPiece (monomialIdeal k B)) (FourPapers.Sublattice.integerExponent a) p ≃ₗ[k]
      LinearMap.ker (idealSourcePrevious (k := k) B a p) where
  toFun x := ⟨⟨x.val,(idealPiece_nat_eq B a p).le x.property.2⟩,by
    apply Subtype.ext
    rw [idealPrevious_val]
    exact x.property.1⟩
  invFun x := ⟨x.val.val,⟨by
    change previous (k := k) (M := monomialIdeal k B) p x.val.val = 0
    rw [← idealPrevious_val B a p x.val]
    exact congrArg Subtype.val x.property,
    (idealPiece_nat_eq B a p).ge x.val.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem idealBoundaries_map (B : Family V) (a : Exponent V) (p : ℕ) :
    (boundaries (idealCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p).map (idealCyclesEquiv B a p).toLinearMap =
      LinearMap.range (FourPapers.FilteredHomology.boundaryMap
        (homogeneousDifferential (k := k) B a p) (idealSourcePrevious (k := k) B a p)
        (idealSourcePrevious_comp (k := k) B a p)) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    rcases hx with ⟨z,hz,hzx⟩
    refine ⟨⟨z,(idealPiece_nat_eq B a (p + 1)).le hz⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change monomialDifferential (k := k) B p z = x.val
    rw [← idealDifferential_eq_source]
    exact hzx
  · rintro y ⟨z,rfl⟩
    let b := FourPapers.FilteredHomology.boundaryMap
      (homogeneousDifferential (k := k) B a p) (idealSourcePrevious (k := k) B a p)
      (idealSourcePrevious_comp (k := k) B a p) z
    refine ⟨(idealCyclesEquiv B a p).symm b,?_,by simp [b]⟩
    refine ⟨z.val,(idealPiece_nat_eq B a (p + 1)).ge z.property,?_⟩
    change differential (k := k) (M := monomialIdeal k B) p z.val =
      monomialDifferential B p z.val
    rw [idealDifferential_eq_source]

private def idealHomologyEquiv (B : Family V) (a : Exponent V) (p : ℕ) :
    Homology (idealCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p ≃ₗ[k]
    FourPapers.FilteredHomology.Homology (homogeneousDifferential (k := k) B a p)
      (idealSourcePrevious (k := k) B a p) (idealSourcePrevious_comp (k := k) B a p) :=
  Submodule.Quotient.equiv _ _ (idealCyclesEquiv B a p) (idealBoundaries_map B a p)

private theorem idealBetti_nat_eq_derivedTor (B : Family V) (a : Exponent V) (p : ℕ) :
    idealBetti (monomialIdeal k B) (FourPapers.Sublattice.integerExponent a) p =
      CommAlg.Koszul.bettiNumber (k := k) B a p := by
  exact ((idealHomologyEquiv B a p).trans
    ((idealSourceHomologyIso (k := k) B a p).symm ≪≫ gradedTorIso (k := k) B a p).toLinearEquiv).finrank_eq

end PalomarSublattice.FineKoszul

/- The actual quotient coefficient/chain grading bridge; unelaborated.
Depends on the preceding fine-betti bridge fragments. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem quotientCoefficientPiece_mem_iff (B : Family V) (a : V →₀ ℤ)
    (x : MvPolynomial V k ⧸ monomialIdeal k B) :
    x ∈ quotientCoefficientPiece (monomialIdeal k B) a ↔
      ∀ b : {b : Exponent V // QuotientAllowed B b},
        (quotientMonomialBasis (k := k) B).repr (quotientCoefficientEquiv B x) b ≠ 0 →
          FourPapers.Sublattice.integerExponent b.val = a := by
  have image_iff : x ∈ quotientCoefficientPiece (monomialIdeal k B) a ↔
      quotientCoefficientEquiv B x ∈
        (quotientCoefficientPiece (monomialIdeal k B) a).map
          (quotientCoefficientEquiv B).toLinearMap := by
    constructor
    · intro hx
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact (quotientCoefficientEquiv B).injective he ▸ hy
  rw [image_iff, quotientCoefficientPiece_map, CommAlg.Grading.mem_piece]

/-- Coordinatewise application of the canonical equality-of-ideals quotient
isomorphism, with no change of exterior labels or coefficient values. -/
private def quotientChainsEquiv (B : Family V) (p : ℕ) :
    Coordinates (V := V) (MvPolynomial V k ⧸ monomialIdeal k B) p ≃ₗ[k]
      (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) :=
  Finsupp.mapRange.linearEquiv (quotientCoefficientEquiv B).toLinearEquiv

private theorem quotientChainsEquiv_zero (B : Family V) (p : ℕ) :
    quotientChainsEquiv (k := k) B p 0 = 0 :=
  LinearEquiv.map_zero (quotientChainsEquiv (k := k) B p)

private theorem quotientChainsEquiv_sum (B : Family V) (p : ℕ) {α : Type*}
    (t : Finset α)
    (f : α → Coordinates (V := V) (MvPolynomial V k ⧸ monomialIdeal k B) p) :
    quotientChainsEquiv (k := k) B p (∑ a ∈ t, f a) =
      ∑ a ∈ t, quotientChainsEquiv (k := k) B p (f a) :=
  map_sum (quotientChainsEquiv (k := k) B p).toLinearMap f t

private theorem quotientChains_repr (B : Family V) (p : ℕ)
    (x : Coordinates (V := V) (MvPolynomial V k ⧸ monomialIdeal k B) p)
    (t : QuotientIndex B p) :
    (quotientCoefficientBasis (k := k) B p).repr (quotientChainsEquiv B p x) t =
      (quotientMonomialBasis (k := k) B).repr (quotientCoefficientEquiv B (x t.1)) t.2 := by
  rw [quotientCoefficientBasis, Finsupp.basis_repr]
  rfl

/-- The literal signed homogeneous coefficient-image condition, summed over
actual exterior coordinates, maps onto exactly the source's genuine natural
fine-degree Koszul piece. -/
private theorem quotientPiece_nat_map (B : Family V) (a : Exponent V) (p : ℕ) :
    (piece (quotientCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p).map (quotientChainsEquiv B p).toLinearMap =
        FourPapers.Sublattice.quotientPiece (k := k) B a p := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    rw [FourPapers.Sublattice.quotientPiece, CommAlg.Grading.mem_piece]
    intro t ht
    have hs : x t.1 ∈ quotientCoefficientPiece (monomialIdeal k B)
        (FourPapers.Sublattice.integerExponent a - exteriorDegree t.1.val) :=
      (Submodule.mem_iInf _).mp hx t.1
    have hc : (quotientMonomialBasis (k := k) B).repr
        (quotientCoefficientEquiv B (x t.1)) t.2 ≠ 0 := by
      exact (quotientChains_repr B p x t) ▸ ht
    have hd := (quotientCoefficientPiece_mem_iff B _ _).mp hs t.2 hc
    have he := (eq_sub_iff_add_eq).mp hd
    rw [exteriorDegree_eq_integerExponent, ← integerExponent_add] at he
    exact FourPapers.Sublattice.integerExponent_injective he
  · intro y hy
    obtain ⟨x,rfl⟩ := (quotientChainsEquiv B p).surjective y
    refine ⟨x,?_,rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro s
    apply (quotientCoefficientPiece_mem_iff B _ _).mpr
    intro b hb
    have hc : (quotientCoefficientBasis (k := k) B p).repr
        (quotientChainsEquiv B p x) ⟨s,b⟩ ≠ 0 := by
      exact (quotientChains_repr B p x ⟨s,b⟩).symm ▸ hb
    have hd := (CommAlg.Grading.mem_piece _ _ _ _).mp hy ⟨s,b⟩ hc
    apply (eq_sub_iff_add_eq).mpr
    have he := congrArg FourPapers.Sublattice.integerExponent hd
    simpa only [FourPapers.Sublattice.quotientDegree, integerExponent_add,
      exteriorDegree_eq_integerExponent] using he

end PalomarSublattice.FineKoszul

/- Actual quotient-coefficient variable-action and Koszul differential transport.
Unelaborated source work; not included in the frozen363 Challenge. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open CategoryTheory FourPapers.Sublattice FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The equality-of-defining-ideals quotient equivalence preserves the actual
polynomial action, not only the restricted coefficient-field action. -/
private theorem quotientCoefficientEquiv_smul (B : Family V) (f : MvPolynomial V k)
    (x : MvPolynomial V k ⧸ monomialIdeal k B) :
    quotientCoefficientEquiv B (f • x) = f • quotientCoefficientEquiv B x := by
  change quotientCoefficientEquiv B (Ideal.Quotient.mk _ f * x) =
    Ideal.Quotient.mk _ f * quotientCoefficientEquiv B x
  simp only [map_mul, quotientCoefficientEquiv, Ideal.quotientEquivAlgOfEq_mk]

private theorem quotientChainsEquiv_single (B : Family V) (p : ℕ)
    (s : Set.powersetCard V p) (x : MvPolynomial V k ⧸ monomialIdeal k B) :
    quotientChainsEquiv B p (Finsupp.single s x) =
      Finsupp.single s (quotientCoefficientEquiv B x) := by
  change Finsupp.mapRange (quotientCoefficientEquiv B) (map_zero _)
    (Finsupp.single s x) = _
  exact Finsupp.mapRange_single

/-- Equality of the literal signed variable-deletion differential with the
actual source Koszul differential, through the coefficient quotient equivalence. -/
private theorem quotientDifferential_comm (B : Family V) (p : ℕ) :
    (quotientChainsEquiv (k := k) B p).toLinearMap ∘ₗ
      differential (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p =
    FourPapers.Sublattice.quotientDifferential (k := k) B p ∘ₗ
      (quotientChainsEquiv (k := k) B (p + 1)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro s
  intro x
  change quotientChainsEquiv (k := k) B p
      (differential (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
        (Finsupp.single s x)) =
    FourPapers.Sublattice.quotientDifferential (k := k) B p
      (quotientChainsEquiv (k := k) B (p + 1) (Finsupp.single s x))
  rw [quotientChainsEquiv_single]
  change _ = coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)) p
      (Finsupp.single s (quotientCoefficientEquiv B x))
  rw [coordinateDifferential_single]
  simp only [differential, LinearMap.restrictScalars_apply, Finsupp.lsum_single,
    LinearMap.sum_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    LinearMap.lsmul_apply, quotientChainsEquiv_sum, quotientChainsEquiv_single,
    quotientCoefficientEquiv_smul, PalomarSublattice.Koszul.eraseIndex_eq_source,
    PalomarSublattice.Koszul.eraseSign_eq_source]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact BridgeAPI.signed_unit_action
    (R := MvPolynomial V k) (X := CoefficientQuotient (k := k) B)
    (X j.val) (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val)
    (quotientCoefficientEquiv (k := k) B x)

private def quotientSourcePrevious (B : Family V) (a : Exponent V) :
    ∀ p : ℕ, quotientPiece (k := k) B a p →ₗ[k] quotientPiece (k := k) B a p.pred
  | 0 => 0
  | p + 1 => quotientHomogeneousDifferential (k := k) B a p

private theorem quotientSourcePrevious_comp (B : Family V) (a : Exponent V) (p : ℕ) :
    quotientSourcePrevious (k := k) B a p ∘ₗ quotientHomogeneousDifferential (k := k) B a p = 0 := by
  cases p with
  | zero => simp [quotientSourcePrevious]
  | succ p => exact quotientHomogeneousDifferential_comp B a p

private theorem quotientPrevious_comm (B : Family V) (p : ℕ)
    (x : Coordinates (V := V) (MvPolynomial V k ⧸ monomialIdeal k B) p) :
    quotientChainsEquiv (k := k) B p.pred (previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p x) =
      FourPapers.Sublattice.quotientPreviousDifferential (k := k) B p
        (quotientChainsEquiv (k := k) B p x) := by
  cases p with
  | zero => simp only [previous, FourPapers.Sublattice.quotientPreviousDifferential,
      LinearMap.zero_apply, quotientChainsEquiv_zero]
  | succ p =>
    change quotientChainsEquiv (k := k) B p
      (differential (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p x) =
        FourPapers.Sublattice.quotientDifferential (k := k) B p
          (quotientChainsEquiv (k := k) B (p+1) x)
    have h := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p) x
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe] using h

end PalomarSublattice.FineKoszul

/- Actual quotient Koszul homology transport; unelaborated source work.
Requires the coefficient, chain grading, and differential bridge fragments. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open CategoryTheory FourPapers.Sublattice FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private def quotientHomogeneousPieceEquiv (B : Family V) (a : Exponent V) (p : ℕ) :
    piece (quotientCoefficientPiece (monomialIdeal k B))
        (FourPapers.Sublattice.integerExponent a) p ≃ₗ[k]
      quotientPiece (k := k) B a p :=
  ((quotientChainsEquiv (k := k) B p).submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (quotientPiece_nat_map B a p))

private theorem quotientHomogeneousPieceEquiv_val (B : Family V) (a : Exponent V) (p : ℕ)
    (x : piece (quotientCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p) :
    (quotientHomogeneousPieceEquiv (k := k) B a p x).val = quotientChainsEquiv (k := k) B p x.val := by
  rfl

private theorem quotientPrevious_val (B : Family V) (a : Exponent V) (p : ℕ)
    (x : quotientPiece (k := k) B a p) :
    (quotientSourcePrevious (k := k) B a p x).val =
      quotientChainsEquiv (k := k) B p.pred (previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
        ((quotientChainsEquiv (k := k) B p).symm x.val)) := by
  cases p with
  | zero => simp only [quotientSourcePrevious, previous, LinearMap.zero_apply,
      ZeroMemClass.coe_zero, quotientChainsEquiv_zero]
  | succ p =>
    have h := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p)
      ((quotientChainsEquiv (k := k) B (p + 1)).symm x.val)
    change FourPapers.Sublattice.quotientDifferential (k := k) B p x.val =
      quotientChainsEquiv (k := k) B p
        (differential (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
          ((quotientChainsEquiv (k := k) B (p+1)).symm x.val))
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using h.symm

private def quotientCyclesEquiv (B : Family V) (a : Exponent V) (p : ℕ) :
    cycles (quotientCoefficientPiece (monomialIdeal k B))
        (FourPapers.Sublattice.integerExponent a) p ≃ₗ[k]
      LinearMap.ker (quotientSourcePrevious (k := k) B a p) where
  toFun x := ⟨quotientHomogeneousPieceEquiv (k := k) B a p ⟨x.val,x.property.2⟩,by
    apply Subtype.ext
    rw [quotientPrevious_val, quotientHomogeneousPieceEquiv_val,
      LinearEquiv.symm_apply_apply, x.property.1, quotientChainsEquiv_zero]
    rfl⟩
  invFun x := ⟨(quotientHomogeneousPieceEquiv (k := k) B a p).symm x.val |>.val,by
    refine ⟨?_,((quotientHomogeneousPieceEquiv (k := k) B a p).symm x.val).property⟩
    change previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p ((quotientHomogeneousPieceEquiv (k := k) B a p).symm x.val).val = 0
    apply (quotientChainsEquiv (k := k) B p.pred).injective
    have hx := congrArg Subtype.val x.property
    rw [quotientPrevious_val] at hx
    simpa only [quotientHomogeneousPieceEquiv, LinearEquiv.trans_symm,
      LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.submoduleMap_symm_apply, ZeroMemClass.coe_zero,
      quotientChainsEquiv_zero] using hx⟩
  left_inv x := by
    apply Subtype.ext
    change ((quotientHomogeneousPieceEquiv (k := k) B a p).symm
      (quotientHomogeneousPieceEquiv (k := k) B a p ⟨x.val,x.property.2⟩)).val = x.val
    exact NoncommBridgeAPI.submoduleEquiv_symm_apply_apply_val (K := k)
      _ _ (quotientHomogeneousPieceEquiv (k := k) B a p) ⟨x.val,x.property.2⟩
  right_inv x := by
    apply Subtype.ext
    exact (quotientHomogeneousPieceEquiv (k := k) B a p).apply_symm_apply x.val
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [quotientHomogeneousPieceEquiv_val, Submodule.coe_add] using
      (quotientChainsEquiv (k := k) B p).map_add x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [quotientHomogeneousPieceEquiv_val, Submodule.coe_smul,
      RingHom.id_apply] using
      (quotientChainsEquiv (k := k) B p).map_smul r x.val

private theorem quotientCyclesEquiv_val (B : Family V) (a : Exponent V) (p : ℕ)
    (x : cycles (quotientCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p) :
    (quotientCyclesEquiv (k := k) B a p x).val.val = quotientChainsEquiv (k := k) B p x.val := by
  rfl

private theorem quotientBoundaries_map (B : Family V) (a : Exponent V) (p : ℕ) :
    (boundaries (quotientCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p).map (quotientCyclesEquiv (k := k) B a p).toLinearMap =
      LinearMap.range (FourPapers.FilteredHomology.boundaryMap
        (quotientHomogeneousDifferential (k := k) B a p) (quotientSourcePrevious (k := k) B a p)
        (quotientSourcePrevious_comp (k := k) B a p)) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    rcases hx with ⟨z,hz,hzx⟩
    refine ⟨quotientHomogeneousPieceEquiv (k := k) B a (p + 1) ⟨z,hz⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change FourPapers.Sublattice.quotientDifferential (k := k) B p
      (quotientChainsEquiv (k := k) B (p + 1) z) = quotientChainsEquiv (k := k) B p x.val
    have he := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p) z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at he
    rw [← he]
    exact congrArg (quotientChainsEquiv (k := k) B p) hzx
  · rintro y ⟨z,rfl⟩
    let b := FourPapers.FilteredHomology.boundaryMap
      (quotientHomogeneousDifferential (k := k) B a p) (quotientSourcePrevious (k := k) B a p)
      (quotientSourcePrevious_comp (k := k) B a p) z
    refine ⟨(quotientCyclesEquiv (k := k) B a p).symm b,?_,by simp [b]⟩
    let t := (quotientHomogeneousPieceEquiv (k := k) B a (p + 1)).symm z
    refine ⟨t.val,t.property,?_⟩
    apply (quotientChainsEquiv (k := k) B p).injective
    have he := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p) t.val
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at he
    rw [he]
    have ht : quotientChainsEquiv (k := k) B (p + 1) t.val = z.val := by
      exact congrArg Subtype.val ((quotientHomogeneousPieceEquiv (k := k) B a (p + 1)).apply_symm_apply z)
    rw [ht]
    have hb := congrArg (fun x => x.val.val)
      ((quotientCyclesEquiv (k := k) B a p).apply_symm_apply b)
    exact hb.symm

private def quotientSourceShortComplexIso (B : Family V) (a : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B a).sc' (p + 1) p p.pred ≅
      linearShortComplex (quotientHomogeneousDifferential (k := k) B a p)
        (quotientSourcePrevious (k := k) B a p) (quotientSourcePrevious_comp (k := k) B a p) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [linearShortComplex, quotientHomogeneousComplex, ChainComplex.of_d])
    (by cases p <;> simp [linearShortComplex, quotientHomogeneousComplex,
      quotientSourcePrevious, ChainComplex.of_d, ChainComplex.of_d_ne])

private def quotientSourceHomologyIso (B : Family V) (a : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B a).homology p ≅
      ModuleCat.of k (FourPapers.FilteredHomology.Homology
        (quotientHomogeneousDifferential (k := k) B a p) (quotientSourcePrevious (k := k) B a p)
        (quotientSourcePrevious_comp (k := k) B a p)) :=
  ((quotientHomogeneousComplex (k := k) B a).homologyIsoSc' (p + 1) p p.pred
    (by simp) (by cases p <;> simp)) ≪≫
    ShortComplex.homologyMapIso (quotientSourceShortComplexIso (k := k) B a p) ≪≫
      categoricalHomologyIso (quotientHomogeneousDifferential (k := k) B a p)
        (quotientSourcePrevious (k := k) B a p) (quotientSourcePrevious_comp (k := k) B a p)

private def quotientHomologyEquiv (B : Family V) (a : Exponent V) (p : ℕ) :
    Homology (quotientCoefficientPiece (monomialIdeal k B))
      (FourPapers.Sublattice.integerExponent a) p ≃ₗ[k]
    FourPapers.FilteredHomology.Homology (quotientHomogeneousDifferential (k := k) B a p)
      (quotientSourcePrevious (k := k) B a p) (quotientSourcePrevious_comp (k := k) B a p) :=
  Submodule.Quotient.equiv _ _ (quotientCyclesEquiv (k := k) B a p) (quotientBoundaries_map (k := k) B a p)

private theorem quotientBetti_nat_eq_derivedTor (B : Family V) (a : Exponent V) (p : ℕ) :
    quotientBetti (monomialIdeal k B) (FourPapers.Sublattice.integerExponent a) p =
      FourPapers.Sublattice.quotientBettiNumber (k := k) B a p := by
  exact ((quotientHomologyEquiv (k := k) B a p).trans
    ((quotientSourceHomologyIso (k := k) B a p).symm ≪≫ quotientGradedTorIso (k := k) B a p).toLinearEquiv).finrank_eq

end PalomarSublattice.FineKoszul

/- Actual signed-negative chain vanishing, unelaborated source work. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem polynomialPiece_negative (a : V →₀ ℤ) {v : V} (ha : a v < 0) :
    polynomialPiece (k := k) a = ⊥ := by
  apply le_antisymm
  · intro f hf
    have he : f = 0 := by
      ext b
      by_contra hb
      have hd : FourPapers.Sublattice.integerExponent b = a := by
        change f.IsWeightedHomogeneous variableDegree a at hf
        simpa only [variableWeight_eq_integerExponent] using hf hb
      have hn := FourPapers.Sublattice.integerExponent_nonneg b v
      rw [hd] at hn
      omega
    simpa [he]
  · exact bot_le

private theorem quotientPiece_negative (I : Ideal (MvPolynomial V k))
    (a : V →₀ ℤ) (p : ℕ) {v : V} (ha : a v < 0) :
    piece (quotientCoefficientPiece I) a p = ⊥ := by
  apply le_antisymm
  · intro x hx
    have he : x = 0 := by
      apply Finsupp.ext
      intro s
      change x s = 0
      have hs : x s ∈ quotientCoefficientPiece I (a - exteriorDegree s.val) :=
        ((Submodule.mem_iInf _).mp hx s)
      have hneg : (a - exteriorDegree s.val) v < 0 := by
        have hn := FourPapers.Sublattice.integerExponent_nonneg
          (CommAlg.Koszul.faceExponent s.val) v
        rw [← exteriorDegree_eq_integerExponent] at hn
        simp only [Finsupp.sub_apply]
        omega
      simpa only [quotientCoefficientPiece, polynomialPiece_negative _ hneg,
        Submodule.map_bot, Submodule.mem_bot] using hs
    simpa [he]
  · exact bot_le

private theorem idealBetti_negative (I : Ideal (MvPolynomial V k))
    (a : V →₀ ℤ) (p : ℕ) {v : V} (ha : a v < 0) : idealBetti I a p = 0 := by
  have hc : cycles (idealCoefficientPiece I) a p = ⊥ := by
    simp [cycles, idealPiece_negative I a p ha]
  haveI : Subsingleton (cycles (idealCoefficientPiece I) a p) := by rw [hc]; infer_instance
  unfold idealBetti
  exact Module.finrank_zero_of_subsingleton

private theorem quotientBetti_negative (I : Ideal (MvPolynomial V k))
    (a : V →₀ ℤ) (p : ℕ) {v : V} (ha : a v < 0) : quotientBetti I a p = 0 := by
  have hc : cycles (quotientCoefficientPiece I) a p = ⊥ := by
    simp [cycles, quotientPiece_negative I a p ha]
  haveI : Subsingleton (cycles (quotientCoefficientPiece I) a p) := by rw [hc]; infer_instance
  unfold quotientBetti
  exact Module.finrank_zero_of_subsingleton

/-- Every signed ideal degree is transported to genuine integer-regraded
Tor; negative degrees vanish because the actual polynomial chain piece is zero. -/
private theorem idealBetti_eq_integerDerivedTor (B : Family V) (a : V →₀ ℤ) (p : ℕ) :
    idealBetti (monomialIdeal k B) a p =
      FourPapers.Sublattice.integerBettiNumber (k := k) B a p := by
  by_cases ha : ∀ v, 0 ≤ a v
  · obtain ⟨b,rfl⟩ := (FourPapers.Sublattice.integerExponent_exists_iff a).mpr ha
    rw [FourPapers.Sublattice.integerBettiNumber_nat]
    exact idealBetti_nat_eq_derivedTor B b p
  · obtain ⟨v,hv⟩ := not_forall.mp ha
    have hneg : a v < 0 := lt_of_not_ge hv
    rw [idealBetti_negative _ a p hneg,
      FourPapers.Sublattice.integerBettiNumber_negative B a p hneg]

end PalomarSublattice.FineKoszul

/- Completion draft for Theorem1.2's signed-fine Betti formula.
Unelaborated; not part of the frozen363 main/Rees candidate. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem quotientBetti_eq_integerDerivedTor (B : Family V) (a : V →₀ ℤ) (p : ℕ) :
    quotientBetti (monomialIdeal k B) a p =
      FourPapers.Sublattice.quotientIntegerBettiNumber (k := k) B a p := by
  by_cases ha : ∀ v, 0 ≤ a v
  · obtain ⟨b,rfl⟩ := (FourPapers.Sublattice.integerExponent_exists_iff a).mpr ha
    rw [FourPapers.Sublattice.quotientIntegerBettiNumber_nat]
    exact quotientBetti_nat_eq_derivedTor B b p
  · obtain ⟨v,hv⟩ := not_forall.mp ha
    have hneg : a v < 0 := lt_of_not_ge hv
    rw [quotientBetti_negative _ a p hneg,
      FourPapers.Sublattice.quotientIntegerBettiNumber_negative B a p hneg]
end PalomarSublattice.FineKoszul

namespace PalomarSublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]

private theorem sublatticeIdeal_eq_source (E : Finset (FiniteTuple n)) :
    sublatticeIdeal n (k := k) E = FourPapers.Sublattice.finiteSublatticeIdeal n E := by
  rfl

private theorem powerFamily_ideal (E : Finset (FiniteTuple n)) (m : ℕ) :
    monomialIdeal k (FourPapers.Sublattice.exponentPowerFamily
      (FourPapers.Sublattice.finiteRowFamily n E) m) =
        (sublatticeIdeal n (k := k) E) ^ m := by
  rw [sublatticeIdeal_eq_source]
  exact FourPapers.Sublattice.finitePowerFamily_ideal n E m

private def multichainEquiv (E : Finset (FiniteTuple n)) (m : ℕ) :
    FourPapers.Sublattice.FiniteMultichain n E m ≃ Multichain n E m :=
  Equiv.refl _

private theorem chainCoefficientIdeal_eq_source {E : Finset (FiniteTuple n)} {m : ℕ}
    (w : FourPapers.Sublattice.FiniteMultichain n E m) :
    monomialIdeal k (FourPapers.Sublattice.finiteChainCoefficientFamily n w) =
      chainCoefficientIdeal n (k := k) (multichainEquiv n E m w) := by
  rw [FourPapers.Sublattice.finiteChainCoefficientFamily_ideal]
  rfl

end PalomarSublattice

namespace PalomarSublattice
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ)
/-- The signed fine Betti formula of Theorem1.2: actual ideal powers on the
left and actual polynomial quotients by the summed predecessor colons on the
right. Every field, positive power, homological degree and signed degree occurs. -/
theorem all_powers_signed_fine_betti {k : Type u} [Field k] {E : Finset (FiniteTuple n)}
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (p : ℕ)
    (a : FiniteVariable.{u} n →₀ ℤ) :
    FineKoszul.idealBetti ((sublatticeIdeal n (k := k) E) ^ m) a p =
      ∑ w : Multichain n E m,
        FineKoszul.quotientBetti (chainCoefficientIdeal n (k := k) w)
          (a - integerExponent (chainShift n w)) p := by
  rw [← powerFamily_ideal n E m, FineKoszul.idealBetti_eq_integerDerivedTor]
  rw [FourPapers.Sublattice.allPowersIntegerBettiFormula hE k m hm p a]
  apply Fintype.sum_equiv (multichainEquiv n E m)
  intro w
  rw [← FineKoszul.quotientBetti_eq_integerDerivedTor,
    chainCoefficientIdeal_eq_source]
  rfl
end PalomarSublattice

/- Additional Theorem4.3 ideal-identity and Betti-propagation interfaces.
The full homology-generation clause is stated separately below. -/
namespace PalomarSublattice
open Classical MvPolynomial
universe u
/-- The actual polynomial ideal generated by the leading terms of every element. -/
def initialIdeal {V k : Type*} [CommRing k]
    (o : MonomialOrder V) (J : Ideal (MvPolynomial V k)) : Ideal (MvPolynomial V k) :=
  Ideal.span (o.leadingTerm '' (J : Set (MvPolynomial V k)))
/-- The actual contraction of J^s from each localization at a minimal prime. -/
def symbolicPower {R : Type*} [CommRing R] (J : Ideal R) (s : ℕ) : Ideal R :=
  ⨅ P : J.minimalPrimes, by
    letI : P.val.IsPrime := P.property.isPrime
    exact ((J ^ s).map (algebraMap R (Localization.AtPrime P.val))).comap
      (algebraMap R (Localization.AtPrime P.val))
/-- The same minimal-prime construction using each prime's ordinary power. -/
def radicalSymbolicPower {R : Type*} [CommRing R] (J : Ideal R) (s : ℕ) : Ideal R :=
  ⨅ P : J.minimalPrimes, by
    letI : P.val.IsPrime := P.property.isPrime
    exact ((P.val ^ s).map (algebraMap R (Localization.AtPrime P.val))).comap
      (algebraMap R (Localization.AtPrime P.val))
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
end PalomarSublattice
/- Actual general-ideal derived-Tor bridge for Theorem4.3; unelaborated.
Requires the completed main candidate's literal ordinary Koszul bridge. -/
namespace PalomarSublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]

theorem transfer_ideal_bridge (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : FourPapers.initialIdeal o J = FourPapers.Sublattice.finiteSublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ)))) (s p : ℕ) (q : ℤ) :
    Koszul.betti (J ^ s) p q = FourPapers.Sublattice.sublatticeIntegerPowerBettiNumber
      n o J E hE hinit hJ s p q :=
  Koszul.betti_eq_derivedTor
    (FourPapers.Sublattice.sublatticePowerQuotientData n o J E hE hinit s)
    (FourPapers.Sublattice.homogeneousIdealPower n J hJ s) p q

theorem transfer_monomial_bridge (o : MonomialOrder (FiniteVariable.{u} n))
    (E : Finset (FiniteTuple n)) (s p : ℕ) (q : ℤ) :
    Koszul.betti ((sublatticeIdeal n (k := k) E) ^ s) p q =
      FourPapers.Sublattice.integerMonomialTorBettiNumber (K := k) o
        (FourPapers.Sublattice.exponentPowerFamily (FourPapers.Sublattice.finiteRowFamily n E) s)
        p q := by
  rw [← powerFamily_ideal n E s]
  exact Koszul.betti_eq_derivedTor
    (FourPapers.Sublattice.canonicalQuotientGroebnerData o
      (CommAlg.Polymatroid.monomialIdeal k (FourPapers.Sublattice.exponentPowerFamily
        (FourPapers.Sublattice.finiteRowFamily n E) s)))
    (FourPapers.Sublattice.monomialIdeal_isOrdinaryHomogeneous
      (FourPapers.Sublattice.exponentPowerFamily
        (FourPapers.Sublattice.finiteRowFamily n E) s)) p q

end PalomarSublattice
namespace PalomarSublattice
open Classical MvPolynomial
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
/-- Theorem4.3, all four ideal identities: no first-power Betti or homogeneous
hypothesis is required for these equalities. This is the ideal-identity part only. -/
theorem sublattice_initial_ideal_identities (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E) (s : ℕ) :
    symbolicPower J s = J ^ s ∧ radicalSymbolicPower J s = J ^ s ∧
      initialIdeal o (symbolicPower J s) = (sublatticeIdeal n E) ^ s ∧
      initialIdeal o (J ^ s) = (sublatticeIdeal n E) ^ s := by
  exact FourPapers.Sublattice.finite_theorem43_ideal_identities n o J E hE hinit s

/-- Theorem4.3, Betti propagation: the exact first-power equality for every
ordinary integer degree implies the equality in every power. The separate
Rees-homology-generation assertion of that theorem is not assumed or encoded here. -/
theorem sublattice_first_power_propagation (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q, Koszul.betti J p q = Koszul.betti (sublatticeIdeal n (k := k) E) p q)
    (s p : ℕ) (q : ℤ) :
    Koszul.betti (J ^ s) p q = Koszul.betti ((sublatticeIdeal n (k := k) E) ^ s) p q := by
  have hβsource := (FourPapers.Sublattice.sublattice_first_power_integer_iff
    n o J E hE hinit hJ).mp (fun p q => by
      rw [← transfer_ideal_bridge n o J E hE hinit hJ 1 p q,
        ← transfer_monomial_bridge n o E 1 p q, pow_one, pow_one]
      exact hβ p q)
  rw [transfer_ideal_bridge n o J E hE hinit hJ s p q,
    transfer_monomial_bridge n o E s p q]
  exact FourPapers.Sublattice.theorem43_integer_betti n o J E hE hinit hJ hβsource s p q

end PalomarSublattice

/- Independent general-ideal Rees model for the homology clause of Theorem4.3.
Unelaborated source work; does not alter the frozen complete-main494 candidate. -/
namespace PalomarSublattice.GeneralRees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
/-- The canonical actual Rees subalgebra of S[t]: its s-th polynomial
coefficient belongs to J^s, with the actual polynomial multiplication. -/
abbrev Coefficients (J : Ideal (MvPolynomial V k)) := (reesAlgebra J).restrictScalars k
/-- The ordinary exterior algebra on the polynomial-variable coordinate space. -/
abbrev Wedge := ExteriorAlgebra k (V → k)
/-- The actual tensor Koszul algebra of the genuine general-ideal Rees algebra. -/
abbrev Total (J : Ideal (MvPolynomial V k)) := Coefficients J ⊗[k] Wedge (V := V) (k := k)
instance (priority := 2000) totalRing (J : Ideal (MvPolynomial V k)) : Ring (Total J) :=
  Algebra.TensorProduct.instRing
instance (priority := 2000) totalAlgebra (J : Ideal (MvPolynomial V k)) : Algebra k (Total J) :=
  Algebra.TensorProduct.instAlgebra
variable (J : Ideal (MvPolynomial V k))
/-- Every actual base variable occurs in auxiliary degree zero of R(J). -/
theorem base_mem (v : V) : Polynomial.C (X v) ∈ (reesAlgebra J).restrictScalars k := by
  change Polynomial.C (X v) ∈ reesAlgebra J
  rw [mem_reesAlgebra_iff]
  intro s
  by_cases hs : s = 0
  · subst s; simp
  · simp [Polynomial.coeff_C, hs]
/-- The genuine polynomial variable in the actual Rees subalgebra. -/
def baseVariable (v : V) : Coefficients J := ⟨Polynomial.C (X v), base_mem J v⟩
/-- Ordinary exterior contraction by the actual v-th coordinate functional. -/
def contraction (v : V) : Wedge (V := V) (k := k) →ₗ[k] Wedge (V := V) (k := k) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (V → k)))
    ((Pi.basisFun k V).coord v)
/-- The actual Koszul differential: multiplication by each base variable
combined with ordinary exterior contraction. Auxiliary degree is preserved. -/
def differential : Module.End k (Total J) :=
  ∑ v : V, TensorProduct.map (LinearMap.mulLeft k (baseVariable J v)) (contraction v)
end PalomarSublattice.GeneralRees
/- Genuine general-ideal tensor differential; unelaborated proof-source fragment.
Insert after the literal differential and before its supporting propositions. -/
namespace PalomarSublattice.GeneralRees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  (J : Ideal (MvPolynomial V k))
/-- This uses the retained actual tensor/exterior differential, with our actual
canonical Rees coefficients. No homology-generation property is a field. -/
def literalDGA : FourPapers.ParityDifferential k (Total J) :=
  FourPapers.TensorExteriorKoszul.parityDifferential (baseVariable J)

theorem differential_eq_literalDGA : differential J = (literalDGA J).d := by
  apply TensorProduct.ext'
  intro a z
  simp only [differential, LinearMap.sum_apply, TensorProduct.map_tmul,
    LinearMap.mulLeft_apply]
  change _ = FourPapers.TensorExteriorKoszul.differential (baseVariable J) (a ⊗ₜ[k] z)
  rw [FourPapers.TensorExteriorKoszul.differential_tmul]
  apply Finset.sum_congr rfl
  intro v hv
  rfl

theorem differential_tmul (a : Coefficients J) (z : Wedge (V := V) (k := k)) :
    differential J (a ⊗ₜ[k] z) =
      ∑ v : V, (baseVariable J v * a) ⊗ₜ[k] contraction v z := by
  simp [differential, TensorProduct.map_tmul]
end PalomarSublattice.GeneralRees
namespace PalomarSublattice.GeneralRees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  (J : Ideal (MvPolynomial V k))
/-- The literal Koszul differential kills the algebra unit. -/
theorem d_one : differential J 1 = 0 := by
  rw [differential_eq_literalDGA]
  exact (literalDGA J).map_one
/-- Products of actual Koszul cycles remain actual cycles. -/
theorem cycles_mul (x y : Total J) (hx : differential J x = 0)
    (hy : differential J y = 0) : differential J (x * y) = 0 := by
  rw [differential_eq_literalDGA] at hx hy ⊢
  rw [(literalDGA J).leibniz, hx, hy, zero_mul, mul_zero, zero_add]
/-- The actual cycles subalgebra, not an abstract homology certificate. -/
def Cycles : Subalgebra k (Total J) :=
  (LinearMap.ker (differential J)).toSubalgebra (d_one J) (cycles_mul J)
instance (priority := 2000) cyclesRing : Ring (Cycles J) := Subalgebra.toRing (Cycles J)
instance (priority := 2000) cyclesAlgebra : Algebra k (Cycles J) := Subalgebra.algebra (Cycles J)
/-- Zero is the differential of zero. -/
theorem boundary_zero : (0 : Cycles J).val ∈ LinearMap.range (differential J) := by
  exact ⟨0,map_zero _⟩
/-- Sums of genuine boundaries are boundaries. -/
theorem boundary_add {x y : Cycles J}
    (hx : x.val ∈ LinearMap.range (differential J))
    (hy : y.val ∈ LinearMap.range (differential J)) :
    (x+y).val ∈ LinearMap.range (differential J) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  exact ⟨a+b,by simpa only [map_add,ha,hb,Subalgebra.coe_add]⟩
/-- Negatives of genuine boundaries are boundaries. -/
theorem boundary_neg {x : Cycles J} (hx : x.val ∈ LinearMap.range (differential J)) :
    (-x).val ∈ LinearMap.range (differential J) := by
  obtain ⟨a,ha⟩ := hx
  exact ⟨-a,by simpa only [map_neg,ha,Subalgebra.coe_neg]⟩
/-- Left multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_left {x y : Cycles J}
    (hy : y.val ∈ LinearMap.range (differential J)) :
    (x*y).val ∈ LinearMap.range (differential J) := by
  obtain ⟨a,ha⟩ := hy
  have hx : (literalDGA J).d x.val = 0 := by
    rw [← differential_eq_literalDGA]; exact x.property
  have hb : (literalDGA J).d a = y.val := by
    rw [← differential_eq_literalDGA]; exact ha
  refine ⟨(literalDGA J).parity x.val * a,?_⟩
  rw [differential_eq_literalDGA, (literalDGA J).leibniz,
    (literalDGA J).parity_cycle hx, (literalDGA J).parity_square, hb]
  simp
/-- Right multiplication by an actual cycle preserves actual boundaries. -/
theorem boundary_right {x y : Cycles J}
    (hx : x.val ∈ LinearMap.range (differential J)) :
    (x*y).val ∈ LinearMap.range (differential J) := by
  obtain ⟨a,ha⟩ := hx
  have hy : (literalDGA J).d y.val = 0 := by
    rw [← differential_eq_literalDGA]; exact y.property
  have hb : (literalDGA J).d a = x.val := by
    rw [← differential_eq_literalDGA]; exact ha
  refine ⟨a * y.val,?_⟩
  rw [differential_eq_literalDGA, (literalDGA J).leibniz, hy, hb]
  simp
/-- The genuine two-sided ideal of actual boundaries in actual cycles. -/
def Boundaries : TwoSidedIdeal (Cycles J) :=
  TwoSidedIdeal.mk' {z | z.val ∈ LinearMap.range (differential J)}
    (boundary_zero J) (boundary_add J) (boundary_neg J) (boundary_left J) (boundary_right J)
/-- The actual homology algebra: actual cycles modulo actual boundaries. -/
abbrev Homology :=
  _root_.Quotient (Submodule.quotientRel (R := Cycles J) (M := Cycles J) (Boundaries J).asIdeal)
instance (priority := 2000) homologyRing : Ring (Homology J) :=
  Ideal.Quotient.ring (Boundaries J).asIdeal
instance (priority := 2000) homologyAlgebra : Algebra k (Homology J) :=
  Ideal.Quotient.algebra k (A := Cycles J) (I := (Boundaries J).asIdeal)
/-- Projection of an actual cycle onto its genuine homology class. -/
def classMap : Cycles J →ₐ[k] Homology J := Ideal.Quotient.mkₐ k (Boundaries J).asIdeal
/-- Every coefficient f in J yields the actual degree-one term f t in R(J). -/
theorem oneCoefficient_mem (f : (J ^ 1).restrictScalars k) :
    Polynomial.monomial 1 f.val ∈ (reesAlgebra J).restrictScalars k := by
  change Polynomial.monomial 1 f.val ∈ reesAlgebra J
  exact reesAlgebra.monomial_mem.mpr f.property
/-- Actual inclusion of the auxiliary-degree-one coefficient module. -/
def oneCoefficient : (J ^ 1).restrictScalars k →ₗ[k] Coefficients J :=
  (((Polynomial.monomial 1 : MvPolynomial V k →ₗ[MvPolynomial V k]
      Polynomial (MvPolynomial V k)).restrictScalars k).comp
    ((J ^ 1).restrictScalars k).subtype).codRestrict
      ((reesAlgebra J).restrictScalars k).toSubmodule (oneCoefficient_mem J)
/-- The genuine auxiliary-degree-one tensor component: every f t tensor every
exterior vector, and all their linear combinations. No Groebner basis is assumed. -/
def DegreeOnePiece : Submodule k (Total J) :=
  LinearMap.range (TensorProduct.map (oneCoefficient J)
    (LinearMap.id : Wedge (V := V) (k := k) →ₗ[k] _))
/-- All actual classes admitting an auxiliary-degree-one cycle representative. -/
def FirstClasses : Set (Homology J) :=
  {z | ∃ x : Cycles J, x.val ∈ DegreeOnePiece J ∧ classMap J x = z}
end PalomarSublattice.GeneralRees
/- Genuine canonical-Rees coefficient and homology transport. Unelaborated.
Requires the general-ideal model, its literalDGA front and transfer Betti bridge. -/
namespace PalomarSublattice.GeneralRees
open Classical MvPolynomial
open scoped TensorProduct
universe u
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  (J : Ideal (MvPolynomial V k))
/-- The retained coefficient-list construction is genuinely isomorphic to
Mathlib's actual Rees subalgebra, by the unchanged polynomial coefficients. -/
def coefficientEquiv : Coefficients J ≃ₐ[k] FourPapers.Sublattice.coefficientRees J :=
  (FourPapers.Sublattice.coefficientReesPolynomialEquiv J).symm

theorem coefficientEquiv_base (v : V) :
    coefficientEquiv J (baseVariable J v) = FourPapers.Sublattice.idealReesBaseVariable J v := by
  apply Subtype.ext
  rfl

/-- The actual coefficient equivalence tensored with the identity on the
whole genuine exterior algebra; no finite sample or homology quotient is used. -/
def tensorEquiv : Total J ≃ₐ[k] FourPapers.Sublattice.IdealReesKoszul J :=
  Algebra.TensorProduct.congr (coefficientEquiv J) AlgEquiv.refl

theorem tensorEquiv_tmul (a : Coefficients J) (z : Wedge (V := V) (k := k)) :
    tensorEquiv J (a ⊗ₜ[k] z) = coefficientEquiv J a ⊗ₜ[k] z := rfl

theorem tensorEquiv_d (x : Total J) :
    tensorEquiv J (differential J x) =
      (FourPapers.Sublattice.idealReesKoszulDGA J).d (tensorEquiv J x) := by
  have he : (tensorEquiv J).toLinearMap.comp (differential J) =
      (FourPapers.Sublattice.idealReesKoszulDGA J).d.comp (tensorEquiv J).toLinearMap := by
    apply TensorProduct.ext'
    intro a z
    change tensorEquiv J (differential J (a ⊗ₜ[k] z)) =
      (FourPapers.Sublattice.idealReesKoszulDGA J).d (tensorEquiv J (a ⊗ₜ[k] z))
    rw [differential_tmul, map_sum, tensorEquiv_tmul]
    change _ = FourPapers.TensorExteriorKoszul.differential
      (FourPapers.Sublattice.idealReesBaseVariable J) (coefficientEquiv J a ⊗ₜ[k] z)
    rw [FourPapers.TensorExteriorKoszul.differential_tmul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [tensorEquiv_tmul, map_mul, coefficientEquiv_base]
    rfl
  exact LinearMap.congr_fun he x

def cyclesEquiv : Cycles J ≃ₐ[k] (FourPapers.Sublattice.idealReesKoszulDGA J).cycles where
  toFun x := ⟨tensorEquiv J x.val, by
    change (FourPapers.Sublattice.idealReesKoszulDGA J).d (tensorEquiv J x.val) = 0
    rw [← tensorEquiv_d, show differential J x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨(tensorEquiv J).symm y.val, by
    change differential J ((tensorEquiv J).symm y.val) = 0
    apply (tensorEquiv J).injective
    rw [tensorEquiv_d, AlgEquiv.apply_symm_apply,
      show (FourPapers.Sublattice.idealReesKoszulDGA J).d y.val = 0 from y.property, map_zero]⟩
  left_inv x := Subtype.ext ((tensorEquiv J).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((tensorEquiv J).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (tensorEquiv J) x.val y.val)
  map_mul' x y := Subtype.ext (map_mul (tensorEquiv J) x.val y.val)
  commutes' c := Subtype.ext ((tensorEquiv J).commutes c)

theorem cyclesEquiv_symm_val
    (y : (FourPapers.Sublattice.idealReesKoszulDGA J).cycles) :
    ((cyclesEquiv J).symm y).val = (tensorEquiv J).symm y.val := rfl

theorem mem_boundaries (x : Cycles J) :
    x ∈ Boundaries J ↔ x.val ∈ LinearMap.range (differential J) :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

theorem cyclesEquiv_map_boundaries :
    Ideal.map (cyclesEquiv J).toRingEquiv.toRingHom (Boundaries J).asIdeal =
      (FourPapers.Sublattice.idealReesKoszulDGA J).boundaries.asIdeal := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective (cyclesEquiv J).toRingEquiv.toRingHom
    (cyclesEquiv J).surjective]
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [TwoSidedIdeal.mem_asIdeal, FourPapers.ParityDifferential.mem_boundaries]
    obtain ⟨a,ha⟩ := (mem_boundaries J x).mp (TwoSidedIdeal.mem_asIdeal.mp hx)
    refine ⟨tensorEquiv J a,?_⟩
    change (FourPapers.Sublattice.idealReesKoszulDGA J).d (tensorEquiv J a) = tensorEquiv J x.val
    rw [← tensorEquiv_d,ha]
  · intro hy
    refine ⟨(cyclesEquiv J).symm y,?_,(cyclesEquiv J).apply_symm_apply y⟩
    apply TwoSidedIdeal.mem_asIdeal.mpr
    apply (mem_boundaries J _).mpr
    obtain ⟨a,ha⟩ := (FourPapers.ParityDifferential.mem_boundaries _ y).mp
      (TwoSidedIdeal.mem_asIdeal.mp hy)
    refine ⟨(tensorEquiv J).symm a,?_⟩
    apply (tensorEquiv J).injective
    rw [tensorEquiv_d]
    rw [cyclesEquiv_symm_val]
    simpa only [AlgEquiv.apply_symm_apply] using ha

/-- Genuine algebra isomorphism between actual cycle/boundary quotients. -/
def homologyEquiv : Homology J ≃ₐ[k] (FourPapers.Sublattice.idealReesKoszulDGA J).Homology :=
  Ideal.quotientEquivAlg (Boundaries J).asIdeal
    (FourPapers.Sublattice.idealReesKoszulDGA J).boundaries.asIdeal
    (cyclesEquiv J) (cyclesEquiv_map_boundaries J).symm

theorem classMap_transport (x : Cycles J) :
    homologyEquiv J (classMap J x) =
      (FourPapers.Sublattice.idealReesKoszulDGA J).classMap (cyclesEquiv J x) := rfl

theorem oneCoefficient_transport (f : (J ^ 1).restrictScalars k) :
    coefficientEquiv J (oneCoefficient J f) = FourPapers.Sublattice.idealReesSingle J 1 f := by
  apply Subtype.ext
  rfl

theorem degreeOne_inclusion_transport
    (x : (J ^ 1).restrictScalars k ⊗[k] Wedge (V := V) (k := k)) :
    tensorEquiv J (TensorProduct.map (oneCoefficient J) LinearMap.id x) =
      FourPapers.Sublattice.powerKoszulInclusion J 1 x := by
  have he : (tensorEquiv J).toLinearMap.comp
      (TensorProduct.map (oneCoefficient J) LinearMap.id) =
      FourPapers.Sublattice.powerKoszulInclusion J 1 := by
    apply TensorProduct.ext'
    intro a z
    change tensorEquiv J (oneCoefficient J a ⊗ₜ[k] z) =
      FourPapers.Sublattice.idealReesSingle J 1 a ⊗ₜ[k] z
    rw [tensorEquiv_tmul, oneCoefficient_transport]
  exact LinearMap.congr_fun he x

variable (o : MonomialOrder V) (G : ℕ → Set (MvPolynomial V k))
  (hG : ∀ s, o.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (o.leadingCoeff g))
/-- The source's Groebner-coordinate auxiliary piece is proved equal to the
literal degree-one inclusion range. Thus the selected cycle class set has
exact auxiliary degree one, independent of the chosen Groebner coordinates. -/
theorem degreeOne_mem_iff (x : Total J) :
    x ∈ DegreeOnePiece J ↔ tensorEquiv J x ∈
      FourPapers.Sublattice.WeightedRees.auxiliaryPiece o J G hG hu 1 := by
  rw [FourPapers.Sublattice.auxiliaryPiece_eq_range]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    rw [← degreeOne_inclusion_transport,ha]
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    apply (tensorEquiv J).injective
    rw [degreeOne_inclusion_transport,ha]

theorem firstClasses_transport :
    homologyEquiv J '' FirstClasses J =
      FourPapers.IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses
        (FourPapers.Sublattice.idealReesKoszulDGA J)
        (FourPapers.Sublattice.WeightedRees.auxiliaryPiece o J G hG hu 1) := by
  ext z
  constructor
  · rintro ⟨x,⟨c,hc,rfl⟩,rfl⟩
    refine ⟨cyclesEquiv J c,(degreeOne_mem_iff J o G hG hu c.val).mp hc,
      (classMap_transport J c).symm⟩
  · rintro ⟨c,hc,rfl⟩
    let x := (cyclesEquiv J).symm c
    refine ⟨classMap J x,⟨x,?_,rfl⟩,?_⟩
    · apply (degreeOne_mem_iff J o G hG hu x.val).mpr
      change (cyclesEquiv J x).val ∈ _
      simpa only [x,AlgEquiv.apply_symm_apply] using hc
    · rw [classMap_transport]
      simp only [x,AlgEquiv.apply_symm_apply]
end PalomarSublattice.GeneralRees

namespace PalomarSublattice
open Classical MvPolynomial
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
/-- The Rees-homology assertion of Theorem4.3 for an arbitrary homogeneous
ideal with sublattice initial ideal and exact first-power ordinary Betti equality.
The conclusion concerns its actual canonical Rees algebra and literal Koszul
cycles, boundaries and auxiliary-degree-one classes. -/
theorem sublattice_deformation_rees_generation (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q, Koszul.betti J p q = Koszul.betti (sublatticeIdeal n (k := k) E) p q) :
    Algebra.adjoin k (GeneralRees.FirstClasses J) = ⊤ := by
  have hβsource := (FourPapers.Sublattice.sublattice_first_power_integer_iff
    n o J E hE hinit hJ).mp (fun p q => by
      rw [← transfer_ideal_bridge n o J E hE hinit hJ 1 p q,
        ← transfer_monomial_bridge n o E 1 p q, pow_one, pow_one]
      exact hβ p q)
  let G := FourPapers.Sublattice.canonicalPowerGenerators n J
  let hG := FourPapers.Sublattice.canonicalPowerGroebner n o J
  let hu := FourPapers.Sublattice.canonicalPowerUnitLeading n o J
  let S := Algebra.adjoin k (GeneralRees.FirstClasses J)
  let e := GeneralRees.homologyEquiv J
  have h : Algebra.adjoin k
      (FourPapers.IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses
        (FourPapers.Sublattice.idealReesKoszulDGA J)
        (FourPapers.Sublattice.WeightedRees.auxiliaryPiece o J G hG hu 1)) ≤
      S.comap e.symm.toAlgHom := by
    apply Algebra.adjoin_le
    intro z hz
    have hz' : z ∈ e '' GeneralRees.FirstClasses J := by
      rw [GeneralRees.firstClasses_transport J o G hG hu]
      exact hz
    obtain ⟨x,hx,rfl⟩ := hz'
    change e.symm (e x) ∈ S
    rw [e.symm_apply_apply]
    change x ∈ Algebra.adjoin k (GeneralRees.FirstClasses J)
    exact Algebra.subset_adjoin hx
  rw [FourPapers.Sublattice.theorem43_rees_homology_generation
    n o J E hE hinit hJ hβsource] at h
  apply top_unique
  intro z _
  have hz := h (show e z ∈ (⊤ : Subalgebra k _) from trivial)
  change e.symm (e z) ∈ S at hz
  simpa only [e.symm_apply_apply] using hz

end PalomarSublattice

/- Literal arbitrary additive grading for the final finer-grading clause of
Theorem4.3; unelaborated, separate from frozen complete-main494. -/
namespace PalomarSublattice.RefinedKoszul
open Classical MvPolynomial
universe u v
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  {Γ : Type v} [AddCommMonoid Γ]
/-- A refining grading compares actual monomial labels. It does not require a
homomorphism on unused labels of the grading monoid, or cancellation in Γ. -/
def RefinesOrdinaryDegree (ω : V → Γ) : Prop :=
  ∀ a b : V →₀ ℕ, Finsupp.weight ω a = Finsupp.weight ω b → a.degree = b.degree
/-- The actual weight of the exterior coordinates in a Koszul wedge. -/
def exteriorWeight (ω : V → Γ) (s : Finset V) : Γ := ∑ j ∈ s, ω j
/-- The actual γ-component consists of chains whose every polynomial monomial,
combined with its exterior wedge, has exactly label γ. Kernels of coefficient
maps express this without subtraction, cancellation or a sampled support. -/
def piece (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    Submodule k (Koszul.Coordinates I p) :=
  ⨅ s : Set.powersetCard V p,
    ⨅ a : {a : V →₀ ℕ // Finsupp.weight ω a + exteriorWeight ω s.val ≠ γ},
      LinearMap.ker ((MvPolynomial.lcoeff k a.val).comp (Koszul.coefficientAt I p s))
/-- Actual homogeneous cycles, with the ordinary signed Koszul differential. -/
def cycles (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    Submodule k (Koszul.Coordinates I p) :=
  LinearMap.ker (Koszul.previous I p) ⊓ piece ω I γ p
instance cyclesAddCommGroup (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    AddCommGroup (cycles ω I γ p) :=
  Submodule.addCommGroup (R := k) (M := Koszul.Coordinates I p) (cycles ω I γ p)
/-- Boundaries of actual preceding γ-homogeneous chains, within actual cycles. -/
def boundaries (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    Submodule k (cycles ω I γ p) :=
  (Submodule.map (Koszul.differential I p) (piece ω I γ (p+1))).comap
    (cycles ω I γ p).subtype
/-- The actual γ-homogeneous Koszul homology quotient. -/
abbrev Homology (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :=
  _root_.Quotient (Submodule.quotientRel (R := k) (M := cycles ω I γ p)
    (boundaries ω I γ p))
instance homologyAddCommGroup (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    AddCommGroup (Homology ω I γ p) :=
  Submodule.Quotient.addCommGroup (R := k) (M := cycles ω I γ p) (boundaries ω I γ p)
instance homologyModule (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    Module k (Homology ω I γ p) :=
  Submodule.Quotient.module (R := k) (M := cycles ω I γ p) (boundaries ω I γ p)
/-- The dimension of the actual homogeneous chain-homology component. The
Solution must identify it with the genuine source derived-Tor component. -/
def betti (ω : V → Γ) (I : Ideal (MvPolynomial V k)) (p : ℕ) (γ : Γ) : ℕ :=
  Module.finrank k (Homology ω I γ p)
end PalomarSublattice.RefinedKoszul

/- Actual arbitrary-additive-grading component comparison; unelaborated.
No group completion, cancellation or refinement homomorphism is assumed. -/
namespace PalomarSublattice.RefinedKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u v
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
  {Γ : Type v} [AddCommMonoid Γ] (ω : V → Γ)

theorem mem_piece_iff (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ)
    (x : Koszul.Coordinates I p) :
    x ∈ piece ω I γ p ↔ ∀ s : Set.powersetCard V p, ∀ a : V →₀ ℕ,
      (x s).val.coeff a ≠ 0 → Finsupp.weight ω a + exteriorWeight ω s.val = γ := by
  simp only [piece, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ s : Set.powersetCard V p,
    ∀ a : {a : V →₀ ℕ // Finsupp.weight ω a + exteriorWeight ω s.val ≠ γ},
      (x s).val.coeff a.val = 0) ↔ _
  constructor
  · intro h s a ha
    by_contra hne
    exact ha (h s ⟨a,hne⟩)
  · intro h s a
    by_contra hne
    exact a.property (h s a.val hne)

theorem combined_weight (a : V →₀ ℕ) (s : Finset V) :
    Finsupp.weight ω (a + CommAlg.Koszul.faceExponent s) =
      Finsupp.weight ω a + exteriorWeight ω s := by
  rw [map_add]
  congr 1
  simp only [CommAlg.Koszul.faceExponent, map_sum, Finsupp.weight_single,
    one_smul, exteriorWeight]

theorem piece_eq_source_polynomial (I : Ideal (MvPolynomial V k)) (γ : Γ) (p : ℕ) :
    piece ω I γ p = FourPapers.Sublattice.polynomialWeightedCoordinatePiece ω I γ p := by
  ext x
  rw [FourPapers.Sublattice.polynomialWeightedCoordinatePiece, Submodule.mem_comap,
    CommAlg.Grading.mem_piece, mem_piece_iff]
  constructor
  · intro h a ha
    have hc : (x a.1).val.coeff a.2.val ≠ 0 := by
      simpa only [FourPapers.Sublattice.idealCoordinatesToAmbient_repr] using ha
    simpa only [FourPapers.Sublattice.quotientDegree, combined_weight] using
      h a.1 a.2.val hc
  · intro h s a ha
    have hc : (FourPapers.Sublattice.quotientCoefficientBasis
        (k := k) (∅ : Family V) p).repr
        (FourPapers.Sublattice.idealCoordinatesToAmbient I p x)
        ⟨s,⟨a,emptyFamily_allowed a⟩⟩ ≠ 0 := by
      simpa only [FourPapers.Sublattice.idealCoordinatesToAmbient_repr] using ha
    have hd := h ⟨s,⟨a,emptyFamily_allowed a⟩⟩ hc
    simpa only [FourPapers.Sublattice.quotientDegree, combined_weight] using hd

theorem piece_eq_source (P : FourPapers.Sublattice.QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k ω)) (γ : Γ) (p : ℕ) :
    piece ω P.ideal γ p = FourPapers.Sublattice.finerIdealPiece P ω γ p := by
  rw [piece_eq_source_polynomial,FourPapers.Sublattice.finerIdealPiece_eq_polynomial P ω hJ]
end PalomarSublattice.RefinedKoszul

/- Actual finer cycle/boundary quotients and the genuine derived-Tor grading.
Unelaborated; depends on the literal polynomial model and piece bridge. -/
namespace PalomarSublattice.RefinedKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice FourPapers.FilteredHomology
universe u v
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
  {Γ : Type v} [AddCommMonoid Γ] (ω : V → Γ)

def cyclesEquiv (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k ω)) (γ : Γ) (p : ℕ) :
    cycles ω P.ideal γ p ≃ₗ[k] LinearMap.ker (finerIdealPrevious P ω hJ γ p) where
  toFun x := ⟨⟨x.val,(piece_eq_source ω P hJ γ p).le x.property.2⟩,by
    apply Subtype.ext
    rw [finerIdealPrevious_val]
    rw [← Koszul.previous_eq_source]
    exact x.property.1⟩
  invFun x := ⟨x.val.val,⟨by
    change Koszul.previous P.ideal p x.val.val = 0
    rw [Koszul.previous_eq_source]
    have hx := congrArg Subtype.val x.property
    rw [finerIdealPrevious_val, ZeroMemClass.coe_zero] at hx
    exact hx,
    (piece_eq_source ω P hJ γ p).ge x.val.property⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; apply Subtype.ext; rfl

theorem boundaries_map (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k ω)) (γ : Γ) (p : ℕ) :
    (boundaries ω P.ideal γ p).map (cyclesEquiv ω P hJ γ p).toLinearMap =
      LinearMap.range (FourPapers.FilteredHomology.boundaryMap
        (finerIdealDifferential P ω hJ γ p) (finerIdealPrevious P ω hJ γ p)
        (finerIdealDifferential_comp P ω hJ γ p)) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    change x.val ∈ Submodule.map (Koszul.differential P.ideal p)
      (piece ω P.ideal γ (p+1)) at hx
    rcases hx with ⟨z,hz,hzx⟩
    refine ⟨⟨z,(piece_eq_source ω P hJ γ (p+1)).le hz⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [BridgeAPI.boundaryMap_val, finerIdealDifferential_val, cyclesEquiv]
    change actualIdealCoordinateDifferential P.ideal p z = x.val
    rw [← Koszul.differential_eq_source]
    exact hzx
  · rintro y ⟨z,rfl⟩
    let b := FourPapers.FilteredHomology.boundaryMap
      (finerIdealDifferential P ω hJ γ p) (finerIdealPrevious P ω hJ γ p)
      (finerIdealDifferential_comp P ω hJ γ p) z
    refine ⟨(cyclesEquiv ω P hJ γ p).symm b,?_,by simp [b]⟩
    change ((cyclesEquiv ω P hJ γ p).symm b).val ∈
      Submodule.map (Koszul.differential P.ideal p) (piece ω P.ideal γ (p+1))
    refine ⟨z.val,(piece_eq_source ω P hJ γ (p+1)).ge z.property,?_⟩
    simp only [cyclesEquiv, BridgeAPI.boundaryMap_val, finerIdealDifferential_val]
    change Koszul.differential P.ideal p z.val = actualIdealCoordinateDifferential P.ideal p z.val
    rw [Koszul.differential_eq_source]

/-- The literal refined homology isomorphism is induced by actual identity
maps on the original ideal-valued polynomial Koszul chains. -/
def homologyEquiv (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k ω)) (γ : Γ) (p : ℕ) :
    Homology ω P.ideal γ p ≃ₗ[k] finerIdealHomology P ω hJ γ p :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv ω P hJ γ p) (boundaries_map ω P hJ γ p)

/-- The actual homogeneous chain quotient agrees with the actual γ-component
of genuine derived Tor through its retained injective homology inclusion. -/
theorem betti_eq_derivedTor (P : QuotientGroebnerData V k)
    (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k ω)) (p : ℕ) (γ : Γ) :
    betti ω P.ideal p γ = finerIdealBettiNumber P ω hJ p γ := by
  rw [betti,finerIdealBettiNumber,← (finerIdealGradedTorEquiv P ω hJ γ p).finrank_eq]
  exact (homologyEquiv ω P hJ γ p).finrank_eq

/-- The initial component agrees with the actual monomial ideal's literal
Koszul quotient. The retained canonical bridge is induced on all chains by
the monomial coefficient equivalence and preserves every weighted label. -/
theorem initial_betti_eq (P : QuotientGroebnerData V k) (p : ℕ) (γ : Γ) :
    betti ω (monomialIdeal k P.family) p γ = initialFinerBettiNumber P ω p γ := by
  rw [initialFinerBettiNumber_eq_canonical]
  exact betti_eq_derivedTor ω
    (canonicalQuotientGroebnerData P.order (monomialIdeal k P.family))
    (monomialIdeal_weighted_homogeneous P.family ω) p γ
end PalomarSublattice.RefinedKoszul

namespace PalomarSublattice
open Classical MvPolynomial
universe u v
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
/-- Theorem4.3, every finer additive grading respected by J and refining the
ordinary monomial degree. Γ need not be a group or cancellative, and no map
on its unused labels is assumed. The first-power hypothesis is ordinary Betti
equality only; finer equality in every power is the conclusion. -/
theorem sublattice_first_power_finer_propagation
    (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    {Γ : Type v} [AddCommMonoid Γ] (ω : FiniteVariable.{u} n → Γ)
    (href : RefinedKoszul.RefinesOrdinaryDegree ω)
    (hJω : J.IsHomogeneous (weightedHomogeneousSubmodule k ω))
    (hβ : ∀ p q, Koszul.betti J p q = Koszul.betti (sublatticeIdeal n (k := k) E) p q)
    (s p : ℕ) (γ : Γ) :
    RefinedKoszul.betti ω (J ^ s) p γ =
      RefinedKoszul.betti ω ((sublatticeIdeal n (k := k) E) ^ s) p γ := by
  have hβsource := (FourPapers.Sublattice.sublattice_first_power_integer_iff
    n o J E hE hinit hJ).mp (fun p q => by
      rw [← transfer_ideal_bridge n o J E hE hinit hJ 1 p q,
        ← transfer_monomial_bridge n o E 1 p q,pow_one,pow_one]
      exact hβ p q)
  let P := FourPapers.Sublattice.sublatticePowerQuotientData n o J E hE hinit s
  have hmono : CommAlg.Polymatroid.monomialIdeal k P.family = (sublatticeIdeal n (k := k) E) ^ s := by
    exact (powerFamily_ideal n E s)
  change RefinedKoszul.betti ω P.ideal p γ =
    RefinedKoszul.betti ω ((sublatticeIdeal n (k := k) E)^s) p γ
  rw [RefinedKoszul.betti_eq_derivedTor ω P
    (FourPapers.Sublattice.homogeneousIdealPowerWeighted n J ω hJω s),
    ← hmono,RefinedKoszul.initial_betti_eq ω P]
  exact FourPapers.Sublattice.theorem43_finer_betti_of_refines n o J E hE hinit hJ ω hJω
    href hβsource s p γ

end PalomarSublattice

/- Literal ordinary integer strands for actual quotient coefficients. This
fragment extends the existing canonical-only Challenge; no derived-Tor value
is defined by a summation formula. -/
namespace PalomarSublattice.OrdinaryQuotientKoszul
open Classical MvPolynomial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The image of the genuine polynomial homogeneous component in the actual
quotient. Integer weights include negative strands with their actual zero
polynomial component. -/
def coefficientPiece (I : Ideal (MvPolynomial V k)) (q : ℤ) :
    Submodule k (MvPolynomial V k ⧸ I) :=
  (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℤ)) q).map
    (Ideal.Quotient.mkₐ k I).toLinearMap
/-- Exterior degree p contributes p to ordinary internal degree. Each actual
quotient coefficient has polynomial degree q-p. -/
def piece (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    Submodule k (FineKoszul.Coordinates (V := V) (MvPolynomial V k ⧸ I) p) :=
  ⨅ s : Set.powersetCard V p,
    (coefficientPiece I (q - (p : ℤ))).comap (Finsupp.lapply s)
/-- Genuine cycles of the signed variable-multiplication Koszul differential
inside the actual ordinary integer strand. -/
def cycles (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    Submodule k (FineKoszul.Coordinates (V := V) (MvPolynomial V k ⧸ I) p) :=
  LinearMap.ker (FineKoszul.previous (k := k) p) ⊓ piece I q p
instance cyclesAddCommGroup (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    AddCommGroup (cycles I q p) :=
  Submodule.addCommGroup (R := k)
    (M := FineKoszul.Coordinates (V := V) (MvPolynomial V k ⧸ I) p) (cycles I q p)
/-- The actual preceding homogeneous component mapped by the Koszul
 differential, viewed inside its cycle submodule. -/
def boundaries (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    Submodule k (cycles I q p) :=
  (Submodule.map (FineKoszul.differential (k := k) p) (piece I q (p+1))).comap
    (cycles I q p).subtype
/-- Literal homogeneous Koszul homology: actual cycles modulo actual boundaries. -/
abbrev Homology (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :=
  _root_.Quotient (Submodule.quotientRel (R := k) (M := cycles I q p) (boundaries I q p))
instance homologyAddCommGroup (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    AddCommGroup (Homology I q p) :=
  Submodule.Quotient.addCommGroup (R := k) (M := cycles I q p) (boundaries I q p)
instance homologyModule (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    Module k (Homology I q p) :=
  Submodule.Quotient.module (R := k) (M := cycles I q p) (boundaries I q p)
/-- The dimension of the genuine ordinary integer Koszul homology strand. -/
def betti (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) : ℕ :=
  Module.finrank k ((cycles I q p) ⧸ boundaries I q p)
end PalomarSublattice.OrdinaryQuotientKoszul

/- Actual chain-level bridge for the ordinary quotient strands. Draft only;
requires the literal prefix and the existing full Solution's FineKoszul helpers. -/
namespace PalomarSublattice.FineKoszul
open Classical MvPolynomial CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
private theorem ordinaryPolynomialPiece_eq_monomialSpan (q : ℤ) :
    weightedHomogeneousSubmodule k (fun _ : V => (1 : ℤ)) q =
      Submodule.span k ((fun b : V →₀ ℕ => MvPolynomial.monomial b (1 : k)) ''
        {b | (b.degree : ℤ) = q}) := by
  have h : weightedHomogeneousSubmodule k (fun _ : V => (1 : ℤ)) q =
      Grading.Piece (MvPolynomial.basisMonomials V k) (fun b => (b.degree : ℤ)) q := by
    ext f
    rw [Grading.mem_piece]
    change f.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) q ↔ _
    simp only [MvPolynomial.IsWeightedHomogeneous, Koszul.integerWeight_degree]
    rfl
  rw [h,Grading.Piece]
  rfl
private theorem ordinaryCoefficientPiece_map (B : Family V) (q : ℤ) :
    (OrdinaryQuotientKoszul.coefficientPiece (monomialIdeal k B) q).map
      (quotientCoefficientEquiv (k := k) B).toLinearMap =
    Grading.Piece (quotientMonomialBasis (k := k) B)
      (fun b => (b.val.degree : ℤ)) q := by
  rw [OrdinaryQuotientKoszul.coefficientPiece, ordinaryPolynomialPiece_eq_monomialSpan,
    ← Submodule.map_comp,Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x,⟨b,hb,rfl⟩,rfl⟩
    change quotientCoefficientEquiv (k := k) B
      (Ideal.Quotient.mk _ (MvPolynomial.monomial b (1 : k))) ∈ _
    rw [quotientCoefficientEquiv,Ideal.quotientEquivAlgOfEq_mk]
    change quotientMonomial (k := k) B b ∈ _
    by_cases hallowed : QuotientAllowed B b
    · rw [← quotientMonomialBasis_apply B ⟨b,hallowed⟩]
      have hmem := Grading.basis_mem_piece (quotientMonomialBasis (k := k) B)
        (fun b => (b.val.degree : ℤ)) ⟨b,hallowed⟩
      rw [show (b.degree : ℤ)=q from hb] at hmem
      exact hmem
    · rw [quotientMonomial_zero B b hallowed]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro y ⟨b,hb,rfl⟩
    rw [quotientMonomialBasis_apply]
    apply Submodule.subset_span
    refine ⟨MvPolynomial.monomial b.val 1,⟨b.val,hb,rfl⟩,?_⟩
    exact Ideal.quotientEquivAlgOfEq_mk k
      (forbiddenIdeal_eq_monomialIdeal (k := k) B).symm
      (MvPolynomial.monomial b.val (1 : k))
private theorem ordinaryCoefficientPiece_mem_iff (B : Family V) (q : ℤ)
    (x : MvPolynomial V k ⧸ monomialIdeal k B) :
    x ∈ OrdinaryQuotientKoszul.coefficientPiece (monomialIdeal k B) q ↔
      ∀ b : {b : Exponent V // QuotientAllowed B b},
        (quotientMonomialBasis (k := k) B).repr (quotientCoefficientEquiv (k := k) B x) b ≠ 0 →
          (b.val.degree : ℤ)=q := by
  have hi : x ∈ OrdinaryQuotientKoszul.coefficientPiece (monomialIdeal k B) q ↔
      quotientCoefficientEquiv (k := k) B x ∈
        (OrdinaryQuotientKoszul.coefficientPiece (monomialIdeal k B) q).map
          (quotientCoefficientEquiv (k := k) B).toLinearMap := by
    constructor
    · intro hx; exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact (quotientCoefficientEquiv (k := k) B).injective he ▸ hy
  rw [hi,ordinaryCoefficientPiece_map,Grading.mem_piece]
private theorem quotientTotalDegree (B : Family V) (p : ℕ) (t : QuotientIndex B p) :
    ((quotientDegree t).degree : ℤ)=(t.2.val.degree : ℤ)+(p : ℤ) := by
  simp only [quotientDegree,map_add,degree_faceExponent,Set.powersetCard.card_eq,Nat.cast_add]
private theorem ordinaryPiece_map (B : Family V) (q : ℤ) (p : ℕ) :
    (OrdinaryQuotientKoszul.piece (monomialIdeal k B) q p).map
      (quotientChainsEquiv (k := k) B p).toLinearMap =
        integerOrdinaryQuotientPiece (k := k) B q p := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    rw [integerOrdinaryQuotientPiece_eq,Grading.mem_piece]
    intro t ht
    have hs := (Submodule.mem_iInf _).mp hx t.1
    have hc : (quotientMonomialBasis (k := k) B).repr
        (quotientCoefficientEquiv (k := k) B (x t.1)) t.2 ≠ 0 :=
      (quotientChains_repr (k := k) B p x t) ▸ ht
    have hd := (ordinaryCoefficientPiece_mem_iff B _ _).mp hs t.2 hc
    rw [quotientTotalDegree]
    exact (eq_sub_iff_add_eq).mp hd
  · intro y hy
    obtain ⟨x,rfl⟩ := (quotientChainsEquiv (k := k) B p).surjective y
    refine ⟨x,?_,rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro s
    apply (ordinaryCoefficientPiece_mem_iff B _ _).mpr
    intro b hb
    have hc : (quotientCoefficientBasis (k := k) B p).repr
        (quotientChainsEquiv (k := k) B p x) ⟨s,b⟩ ≠ 0 :=
      (quotientChains_repr (k := k) B p x ⟨s,b⟩).symm ▸ hb
    rw [integerOrdinaryQuotientPiece_eq] at hy
    have hd := (Grading.mem_piece _ _ _ _).mp hy ⟨s,b⟩ hc
    rw [quotientTotalDegree] at hd
    change (b.val.degree : ℤ) + (p : ℤ) = q at hd
    exact (eq_sub_iff_add_eq).mpr hd
private def ordinaryPieceEquiv (B : Family V) (q : ℤ) (p : ℕ) :
    OrdinaryQuotientKoszul.piece (monomialIdeal k B) q p ≃ₗ[k]
      integerOrdinaryQuotientPiece (k := k) B q p :=
  ((quotientChainsEquiv (k := k) B p).submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (ordinaryPiece_map B q p))
private theorem ordinaryPieceEquiv_val (B : Family V) (q : ℤ) (p : ℕ)
    (x : OrdinaryQuotientKoszul.piece (monomialIdeal k B) q p) :
    (ordinaryPieceEquiv B q p x).val=quotientChainsEquiv (k := k) B p x.val := rfl
private theorem ordinaryPrevious_val (B : Family V) (q : ℤ) (p : ℕ)
    (x : integerOrdinaryQuotientPiece (k := k) B q p) :
    (integerOrdinaryQuotientPrevious (k := k) B q p x).val =
      quotientChainsEquiv (k := k) B p.pred
        (previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
          ((quotientChainsEquiv (k := k) B p).symm x.val)) := by
  cases p with
  | zero => simp only [integerOrdinaryQuotientPrevious,previous,
      LinearMap.zero_apply,ZeroMemClass.coe_zero,quotientChainsEquiv_zero]
  | succ p =>
    change FourPapers.Sublattice.quotientDifferential (k := k) B p x.val =
      quotientChainsEquiv (k := k) B p
        (differential (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
          ((quotientChainsEquiv (k := k) B (p+1)).symm x.val))
    have h := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p)
      ((quotientChainsEquiv (k := k) B (p+1)).symm x.val)
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using h.symm
/-- Fix the canonical source kernel structures explicitly. The actual
integer quotient differential and its kernel remain unchanged. -/
local instance (priority := 2100) ordinarySourceKernelGroup (B : Family V) (q : ℤ) (p : ℕ) :
    AddCommGroup (LinearMap.ker (integerOrdinaryQuotientPrevious (k := k) B q p)) :=
  Submodule.addCommGroup (R := k)
    (M := integerOrdinaryQuotientPiece (k := k) B q p) _
local instance (priority := 2100) ordinarySourceKernelModule (B : Family V) (q : ℤ) (p : ℕ) :
    Module k (LinearMap.ker (integerOrdinaryQuotientPrevious (k := k) B q p)) :=
  Submodule.module (R := k)
    (M := integerOrdinaryQuotientPiece (k := k) B q p) _
private def ordinaryCyclesEquiv (B : Family V) (q : ℤ) (p : ℕ) :
    OrdinaryQuotientKoszul.cycles (monomialIdeal k B) q p ≃ₗ[k]
      LinearMap.ker (integerOrdinaryQuotientPrevious (k := k) B q p) where
  toFun x := ⟨ordinaryPieceEquiv B q p ⟨x.val,x.property.2⟩,by
    apply Subtype.ext
    rw [ordinaryPrevious_val,ordinaryPieceEquiv_val,LinearEquiv.symm_apply_apply,
      show previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p x.val=0 from x.property.1,
      quotientChainsEquiv_zero]
    rfl⟩
  invFun x := ⟨(ordinaryPieceEquiv B q p).symm x.val |>.val,by
    refine ⟨?_,((ordinaryPieceEquiv B q p).symm x.val).property⟩
    change previous (k := k) (M := MvPolynomial V k ⧸ monomialIdeal k B) p
      ((ordinaryPieceEquiv B q p).symm x.val).val=0
    apply (quotientChainsEquiv (k := k) B p.pred).injective
    have hx := congrArg Subtype.val x.property
    rw [ordinaryPrevious_val] at hx
    simpa only [ordinaryPieceEquiv,LinearEquiv.trans_symm,LinearEquiv.trans_apply,
      LinearEquiv.ofEq_symm,LinearEquiv.coe_ofEq_apply,LinearEquiv.submoduleMap_symm_apply,
      ZeroMemClass.coe_zero,quotientChainsEquiv_zero] using hx⟩
  left_inv x := by
    apply Subtype.ext
    change ((ordinaryPieceEquiv B q p).symm
      (ordinaryPieceEquiv B q p ⟨x.val,x.property.2⟩)).val = x.val
    exact NoncommBridgeAPI.submoduleEquiv_symm_apply_apply_val (K := k)
      _ _ (ordinaryPieceEquiv B q p) ⟨x.val,x.property.2⟩
  right_inv x := by
    apply Subtype.ext
    exact (ordinaryPieceEquiv B q p).apply_symm_apply x.val
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [ordinaryPieceEquiv_val,Submodule.coe_add] using
      (quotientChainsEquiv (k := k) B p).map_add x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [ordinaryPieceEquiv_val,Submodule.coe_smul,RingHom.id_apply] using
      (quotientChainsEquiv (k := k) B p).map_smul r x.val
private theorem ordinaryCyclesEquiv_val (B : Family V) (q : ℤ) (p : ℕ)
    (x : OrdinaryQuotientKoszul.cycles (monomialIdeal k B) q p) :
    (ordinaryCyclesEquiv B q p x).val.val = quotientChainsEquiv (k := k) B p x.val := rfl
private theorem ordinaryDifferential_val (B : Family V) (q : ℤ) (p : ℕ)
    (x : integerOrdinaryQuotientPiece (k := k) B q (p+1)) :
    (integerOrdinaryQuotientDifferential (k := k) B q p x).val =
      FourPapers.Sublattice.quotientDifferential (k := k) B p x.val := rfl
private def ordinaryHomologyEquiv (B : Family V) (q : ℤ) (p : ℕ) :
    OrdinaryQuotientKoszul.Homology (monomialIdeal k B) q p ≃ₗ[k]
      integerOrdinaryQuotientHomology (k := k) B q p :=
  Submodule.Quotient.equiv _ _ (ordinaryCyclesEquiv B q p) (by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      simp only [OrdinaryQuotientKoszul.boundaries,Submodule.mem_comap] at hx
      rcases hx with ⟨z,hz,hzx⟩
      refine ⟨ordinaryPieceEquiv B q (p+1) ⟨z,hz⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simp only [BridgeAPI.boundaryMap_val,ordinaryDifferential_val,
        ordinaryPieceEquiv_val,ordinaryCyclesEquiv_val]
      have he := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p) z
      simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at he
      rw [← he]
      exact congrArg (quotientChainsEquiv (k := k) B p) hzx
    · rintro y ⟨z,rfl⟩
      let b : LinearMap.ker (integerOrdinaryQuotientPrevious (k := k) B q p) :=
        ⟨integerOrdinaryQuotientDifferential (k := k) B q p z, by
          simpa only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.zero_apply] using
            LinearMap.congr_fun
              (integerOrdinaryQuotientDifferential_comp (k := k) B q p) z⟩
      refine ⟨(ordinaryCyclesEquiv B q p).symm b,?_,
        (ordinaryCyclesEquiv B q p).apply_symm_apply b⟩
      simp only [OrdinaryQuotientKoszul.boundaries,Submodule.mem_comap]
      let t := (ordinaryPieceEquiv B q (p+1)).symm z
      refine ⟨t.val,t.property,?_⟩
      apply (quotientChainsEquiv (k := k) B p).injective
      have he := LinearMap.congr_fun (quotientDifferential_comm (k := k) B p) t.val
      simp only [LinearMap.comp_apply,LinearEquiv.coe_coe] at he
      rw [he]
      have ht : quotientChainsEquiv (k := k) B (p+1) t.val=z.val :=
        congrArg (fun x : integerOrdinaryQuotientPiece (k := k) B q (p+1) => x.val)
          ((ordinaryPieceEquiv B q (p+1)).apply_symm_apply z)
      rw [ht]
      have hb := congrArg
        (fun x : LinearMap.ker (integerOrdinaryQuotientPrevious (k := k) B q p) => x.val.val)
        ((ordinaryCyclesEquiv B q p).apply_symm_apply b)
      have hb' : quotientChainsEquiv (k := k) B p
          ((ordinaryCyclesEquiv B q p).symm b).val =
            FourPapers.Sublattice.quotientDifferential (k := k) B p z.val := by
        simpa only [ordinaryCyclesEquiv_val,b,BridgeAPI.boundaryMap_val,
          ordinaryDifferential_val] using hb
      exact hb'.symm)
theorem ordinaryQuotientBetti_eq_source (B : Family V) (q : ℤ) (p : ℕ) :
    OrdinaryQuotientKoszul.betti (monomialIdeal k B) q p =
      integerOrdinaryQuotientBettiNumber (K := k) B q p :=
  (ordinaryHomologyEquiv B q p).finrank_eq
end PalomarSublattice.FineKoszul

/- Literal Corollaries5.1 and5.2. Every normalized degree is integer-valued;
the coefficient quotients are actual sums of the displayed predecessor colons. -/
namespace PalomarSublattice
open Classical MvPolynomial
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
/-- Exactly the nonempty chains of distinct tuples in E. The strict ordering
is inherited from the original coordinatewise partial order. -/
def StrictSupport (E : Finset (FiniteTuple n)) :=
  {s : Finset E // s.Nonempty ∧ IsChain (· < ·) (s : Set E)}
/-- Literal finite enumeration with an explicit canonical classical decision,
so source-specific Fintype aliases cannot enter the independent data body. -/
def strictSupportFinset (E : Finset (FiniteTuple n)) : Finset (Finset E) :=
  @Finset.filter (Finset E) (fun s => s.Nonempty ∧ IsChain (· < ·) (s : Set E))
    (Classical.decPred _) Finset.univ
/-- Exact enumeration law; this supporting proposition must be selected for
comparison when the candidate is assembled. -/
theorem strictSupportFinset_mem (E : Finset (FiniteTuple n)) (s : Finset E) :
    s ∈ strictSupportFinset n E ↔ s.Nonempty ∧ IsChain (· < ·) (s : Set E) := by
  classical
  simp [strictSupportFinset]
noncomputable instance strictSupportFintype (E : Finset (FiniteTuple n)) :
    Fintype (StrictSupport n E) :=
  Fintype.subtype (strictSupportFinset n E) (strictSupportFinset_mem n E)
/-- The genuine sum of predecessor-colon ideals over a strict support. -/
def supportCoefficientIdeal {E : Finset (FiniteTuple n)} (s : StrictSupport n E) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  ⨆ a : s.val, predecessorColon n E a.val.val
/-- Printed nonnegative integer coefficient, grouped by strict-support
cardinality r. Every summand is an actual homogeneous quotient homology dimension. -/
def bettiBinomialCoefficient (E : Finset (FiniteTuple n)) (q : ℤ) (p r : ℕ) : ℕ :=
  ∑ s ∈ Finset.univ.filter (fun s : StrictSupport n E => s.val.card = r),
    OrdinaryQuotientKoszul.betti (supportCoefficientIdeal n (k := k) s) q p
end PalomarSublattice

/- Exact predecessor-colon sums and source endpoint transport. Unelaborated
source work, separate from every running full28 package. -/
namespace PalomarSublattice
open Classical MvPolynomial CommAlg.Polymatroid
open FourPapers.Sublattice FourPapers.MultichainCounting
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
private def supportEquiv (E : Finset (FiniteTuple n)) :
    FourPapers.MultichainCounting.StrictSupport E ≃ StrictSupport n E := Equiv.refl _
private theorem supportCoefficientIdeal_eq_source {E : Finset (FiniteTuple n)}
    (s : FourPapers.MultichainCounting.StrictSupport E) :
    monomialIdeal k (FourPapers.Sublattice.strictSupportCoefficientFamily s) =
      supportCoefficientIdeal n (k := k) (supportEquiv n E s) := by
  change monomialIdeal k (s.val.biUnion fun a => finitePredecessorFamily n E a.val) =
    ⨆ a : s.val, finitePredecessorColon n (k := k) E a.val.val
  simp_rw [finitePredecessorColon_eq]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨a,ha,rfl⟩
    obtain ⟨b,hb,ha⟩ := Finset.mem_biUnion.mp ha
    exact (le_iSup (fun b : s.val => monomialIdeal k
      (finitePredecessorFamily n E b.val.val)) ⟨b,hb⟩) (Ideal.subset_span ⟨a,ha,rfl⟩)
  · apply iSup_le
    intro b
    apply Ideal.span_mono
    apply Set.image_mono
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨b.val,b.property,ha⟩
private theorem bettiBinomialCoefficient_eq_source (E : Finset (FiniteTuple n))
    (q : ℤ) (p r : ℕ) :
    bettiBinomialCoefficient n (k := k) E q p r =
      FourPapers.Sublattice.integerBettiBinomialCoefficient (K := k) (E := E) q p r := by
  unfold bettiBinomialCoefficient FourPapers.Sublattice.integerBettiBinomialCoefficient
  simp only [Finset.sum_filter]
  apply Fintype.sum_equiv (supportEquiv n E).symm
  intro s
  have hval : ((supportEquiv n E).symm s).val = s.val := rfl
  rw [hval]
  split_ifs with hc
  · rw [FourPapers.Sublattice.integerStrictSupportBettiCoefficient,
      ← FineKoszul.ordinaryQuotientBetti_eq_source,
      supportCoefficientIdeal_eq_source]
    rw [(supportEquiv n E).apply_symm_apply s]
  · rfl
/-- Corollary5.1 through actual integer ordinary ideal Tor and actual
integer ordinary quotient Koszul homology, preserving every q in Z. -/
theorem corollary51_integer {E : Finset (FiniteTuple n)} (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (q : ℤ) :
    Koszul.betti ((sublatticeIdeal n (k := k) E)^m) p ((m*d : ℕ)+q) =
      ∑ s : StrictSupport n E, (m-1).choose (s.val.card-1) *
        OrdinaryQuotientKoszul.betti (supportCoefficientIdeal n (k := k) s) q p := by
  let o : MonomialOrder (FiniteVariable.{u} n) :=
    @MonomialOrder.degLex (FiniteVariable.{u} n) (finiteVariableLinearOrder n)
      (@Finite.to_wellFoundedGT (FiniteVariable.{u} n) (inferInstance)
        (finiteVariableLinearOrder n).toPreorder)
  rw [transfer_monomial_bridge n o E m p ((m*d : ℕ)+q)]
  rw [FourPapers.Sublattice.corollary51_integer o hE m hm p q]
  apply Fintype.sum_equiv (supportEquiv n E)
  intro s
  rw [← FineKoszul.ordinaryQuotientBetti_eq_source,
    supportCoefficientIdeal_eq_source]
  rfl
/-- The printed grouped coefficient expansion, with actual coefficient
quotients and every integer normalized degree. The polynomial, difference,
projective-dimension and depth clauses of Corollary5.2 follow below. -/
theorem corollary52_integer_grouped_expansion {E : Finset (FiniteTuple n)}
    (hE : finiteLatticeClosed n E) (q : ℤ) (p m : ℕ) (hm : 0 < m) :
    Koszul.betti ((sublatticeIdeal n (k := k) E)^m) p ((m*d : ℕ)+q) =
      ∑ r ∈ Finset.Icc 1 E.card,
        bettiBinomialCoefficient n (k := k) E q p r * (m-1).choose (r-1) := by
  let o : MonomialOrder (FiniteVariable.{u} n) :=
    @MonomialOrder.degLex (FiniteVariable.{u} n) (finiteVariableLinearOrder n)
      (@Finite.to_wellFoundedGT (FiniteVariable.{u} n) (inferInstance)
        (finiteVariableLinearOrder n).toPreorder)
  rw [transfer_monomial_bridge n o E m p ((m*d : ℕ)+q)]
  simp_rw [bettiBinomialCoefficient_eq_source]
  exact FourPapers.Sublattice.corollary52_integer_grouped_expansion o hE q p m hm
end PalomarSublattice

/- Remaining literal clauses of Corollaries5.1 and5.2. These preserve the full
original integer, categorical dimension and Ext-depth assertions. -/
namespace PalomarSublattice
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
/-- The actual rational binomial polynomial, including its factorial normalization. -/
def bettiBinomialPolynomial (r : ℕ) : Polynomial ℚ :=
  Polynomial.C ((r.factorial : ℚ)⁻¹) * descPochhammer ℚ r
/-- The printed rational polynomial, with actual quotient-Betti coefficients;
its argument is the positive power m, so the grouped basis is binom(m-1,r-1). -/
def normalizedBettiPolynomial (E : Finset (FiniteTuple n)) (q : ℤ) (p : ℕ) : Polynomial ℚ :=
  (∑ r ∈ Finset.Icc 1 E.card,
    Polynomial.C (bettiBinomialCoefficient n (k := k) E q p r : ℚ) *
      bettiBinomialPolynomial (r-1)).comp (Polynomial.X-Polynomial.C 1)
/-- Every sequence value is the actual Betti number of an actual ideal power.
The t+1 index makes all forward differences range over positive powers. -/
def normalizedBettiSequence (I : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (q : ℤ) (p t : ℕ) : ℤ :=
  (Koszul.betti (I^(t+1)) p (((t+1)*d : ℕ)+q) : ℤ)
/-- Genuine categorical projective dimension of the actual ideal power. -/
def powerProjectiveDimension (I : Ideal (MvPolynomial (FiniteVariable.{u} n) k)) (m : ℕ) :
    WithBot ℕ∞ := projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k) ↥(I^m))
/-- Actual Mathlib Ext-defined depth of the actual quotient at the homogeneous
maximal ideal; the zero quotient has its canonical infinite-depth value. -/
def quotientPowerDepth (I : Ideal (MvPolynomial (FiniteVariable.{u} n) k)) (m : ℕ) : ℕ∞ :=
  (MvPolynomial.idealOfVars (FiniteVariable.{u} n) k).depth
    (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      (MvPolynomial (FiniteVariable.{u} n) k ⧸ I^m))
end PalomarSublattice

/- Actual complete Corollary5.2 and general-J transfer proof drafts. These
use paper_results.numerical_transfer and its original proved statements. -/
namespace PalomarSublattice
open Classical MvPolynomial CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]
private theorem normalizedBettiPolynomial_eq_source (E : Finset (FiniteTuple n))
    (q : ℤ) (p : ℕ) :
    normalizedBettiPolynomial n (k := k) E q p =
      FourPapers.Sublattice.integerNormalizedBettiPolynomial (K := k) (E := E) q p := by
  rw [FourPapers.Sublattice.integerNormalizedBettiPolynomial_grouped]
  unfold normalizedBettiPolynomial
  simp_rw [bettiBinomialCoefficient_eq_source]
  rfl
private theorem normalizedBettiSequence_eq_source
    (o : MonomialOrder (FiniteVariable.{u} n)) (E : Finset (FiniteTuple n)) (q : ℤ) (p : ℕ) :
    normalizedBettiSequence n (sublatticeIdeal n (k := k) E) q p =
      fun t => (FourPapers.Sublattice.integerNormalizedBettiSequence (K := k) o
        (E := E) q p t : ℤ) := by
  funext t
  unfold normalizedBettiSequence FourPapers.Sublattice.integerNormalizedBettiSequence
  rw [transfer_monomial_bridge n o E (t+1) p]
/-- Every printed Corollary5.2 conclusion, with actual categorical dimension
and Ext depth, follows from the original retained proofs and the exact
ordinary-quotient coefficient equivalence. -/
theorem corollary52_full {E : Finset (FiniteTuple n)} (hE : finiteLatticeClosed n E) :
    (∀ q : ℤ, ∀ p m : ℕ, 0 < m →
      (normalizedBettiPolynomial n (k := k) E q p).eval (m : ℚ) =
        (Koszul.betti ((sublatticeIdeal n (k := k) E)^m) p ((m*d : ℕ)+q) : ℚ)) ∧
    (∀ q : ℤ, ∀ p j t : ℕ,
      0 ≤ ((fwdDiff (1 : ℕ))^[j]
        (normalizedBettiSequence n (sublatticeIdeal n (k := k) E) q p)) t) ∧
    (∀ m N : ℕ, 0 < m → m ≤ N →
      powerProjectiveDimension n (sublatticeIdeal n (k := k) E) m ≤
        powerProjectiveDimension n (sublatticeIdeal n (k := k) E) N) ∧
    (∀ m N : ℕ, 0 < m → m ≤ N →
      quotientPowerDepth n (sublatticeIdeal n (k := k) E) N ≤
        quotientPowerDepth n (sublatticeIdeal n (k := k) E) m) := by
  let o : MonomialOrder (FiniteVariable.{u} n) :=
    @MonomialOrder.degLex (FiniteVariable.{u} n) (finiteVariableLinearOrder n)
      (@Finite.to_wellFoundedGT (FiniteVariable.{u} n) (inferInstance)
        (finiteVariableLinearOrder n).toPreorder)
  refine ⟨?_,?_,?_,?_⟩
  · intro q p m hm
    rw [normalizedBettiPolynomial_eq_source,
      transfer_monomial_bridge n o E m p]
    exact FourPapers.Sublattice.corollary52_integer_polynomial o hE q p m hm
  · intro q p j t
    rw [normalizedBettiSequence_eq_source n o E q p]
    exact FourPapers.Sublattice.corollary52_integer_forward_differences o hE q p j t
  · intro m N hm hMN
    rw [sublatticeIdeal_eq_source n E]
    exact FourPapers.Sublattice.corollary52_projectiveDimension_monotone
      (k := k) (n := n) (E := E) hE hm hMN
  · intro m N hm hMN
    rw [sublatticeIdeal_eq_source n E]
    exact FourPapers.Sublattice.corollary52_depth_antitone
      (k := k) (n := n) (E := E) hE hm hMN
/-- Exact ordinary first-power comparison transfers all Corollary5.1/5.2
clauses to J; it is not strengthened to a graded Betti, depth, or dimension premise. -/
theorem corollaries51_52_transfer (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q, Koszul.betti J p q = Koszul.betti (sublatticeIdeal n (k := k) E) p q) :
    (∀ m : ℕ, 0 < m → ∀ p : ℕ, ∀ q : ℤ,
      Koszul.betti (J^m) p ((m*d : ℕ)+q) =
        ∑ s : StrictSupport n E, (m-1).choose (s.val.card-1) *
          OrdinaryQuotientKoszul.betti (supportCoefficientIdeal n (k := k) s) q p) ∧
    (∀ q : ℤ, ∀ p m : ℕ, 0 < m →
      Koszul.betti (J^m) p ((m*d : ℕ)+q) =
        ∑ r ∈ Finset.Icc 1 E.card,
          bettiBinomialCoefficient n (k := k) E q p r * (m-1).choose (r-1)) ∧
    (∀ q : ℤ, ∀ p m : ℕ, 0 < m →
      (normalizedBettiPolynomial n (k := k) E q p).eval (m : ℚ) =
        (Koszul.betti (J^m) p ((m*d : ℕ)+q) : ℚ)) ∧
    (∀ q : ℤ, ∀ p j t : ℕ,
      0 ≤ ((fwdDiff (1 : ℕ))^[j] (normalizedBettiSequence n J q p)) t) ∧
    (∀ m N : ℕ, 0 < m → m ≤ N →
      powerProjectiveDimension n J m ≤ powerProjectiveDimension n J N) ∧
    (∀ m N : ℕ, 0 < m → m ≤ N →
      quotientPowerDepth n J N ≤ quotientPowerDepth n J m) := by
  have hβsource := (FourPapers.Sublattice.sublattice_first_power_integer_iff
    n o J E hE hinit hJ).mp (fun p q => by
      rw [← transfer_ideal_bridge n o J E hE hinit hJ 1 p q,
        ← transfer_monomial_bridge n o E 1 p q,pow_one,pow_one]
      exact hβ p q)
  have hprop : ∀ m p q, Koszul.betti (J^m) p q =
      Koszul.betti ((sublatticeIdeal n (k := k) E)^m) p q :=
    fun m p q => sublattice_first_power_propagation n o J E hE hinit hJ hβ m p q
  have hseq : ∀ q p, normalizedBettiSequence n J q p =
      normalizedBettiSequence n (sublatticeIdeal n (k := k) E) q p := by
    intro q p
    funext t
    exact congrArg (fun z : ℕ => (z : ℤ)) (hprop (t+1) p (((t+1)*d : ℕ)+q))
  obtain ⟨hpoly,hdiff,hpd,hdepth⟩ := corollary52_full n (k := k) hE
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro m hm p q
    rw [hprop]
    exact corollary51_integer n hE m hm p q
  · intro q p m hm
    rw [hprop]
    exact corollary52_integer_grouped_expansion n hE q p m hm
  · intro q p m hm
    rw [hprop]
    exact hpoly q p m hm
  · intro q p j t
    rw [hseq]
    exact hdiff q p j t
  · intro m N hm hMN
    exact FourPapers.Sublattice.corollary52_projectiveDimension_monotone_transfer
      n o J E hE hinit hJ hβsource hm hMN
  · intro m N hm hMN
    exact FourPapers.Sublattice.corollary52_depth_antitone_transfer
      n o J E hE hinit hJ hβsource hm hMN
end PalomarSublattice

namespace PalomarSublattice.RowCovers
open Classical MvPolynomial
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
abbrev Tuple := ∀ i, Fin (n i)
abbrev Label := Σ i, Fin (n i)

/-- The indicated row variables meet every generating squarefree monomial. -/
def IsCover (E : Finset (Tuple n)) (C : Finset (Label n)) : Prop :=
  ∀ a ∈ E, ∃ i, (⟨i, a i⟩ : Label n) ∈ C

def IsMinimalCover (E : Finset (Tuple n)) (C : Finset (Label n)) : Prop :=
  IsCover n E C ∧ ∀ D, D ⊆ C → IsCover n E D → C ⊆ D

def exponent (a : Tuple n) : Label n →₀ ℕ :=
  ∑ i, Finsupp.single ⟨i, a i⟩ 1

def monomialIdeal (k : Type v) [CommSemiring k] (E : Finset (Tuple n)) :
    Ideal (MvPolynomial (Label n) k) :=
  Ideal.span ((fun a => monomial (exponent n a) (1 : k)) '' (E : Set (Tuple n)))

/-- Theorem 4.1, including the actual intersection of minimal-cover coordinate
prime powers and both minimal-prime localization conventions. -/
theorem theorem41 {k : Type v} [Field k] (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E) (s : ℕ) :
    (monomialIdeal n k E)^s = radicalSymbolicPower (monomialIdeal n k E) s ∧
    (monomialIdeal n k E)^s = symbolicPower (monomialIdeal n k E) s ∧
    (monomialIdeal n k E)^s =
      ⨅ C : {C : Finset (Label n) // IsMinimalCover n E C},
        (Ideal.span (X '' (C.val : Set (Label n)))) ^ s := by
  exact FourPapers.Sublattice.RowCutNetwork.theorem41 n E hinf hsup s
end PalomarSublattice.RowCovers

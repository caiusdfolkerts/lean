module
public import Mathlib
public import paper_results.characteristic_consequences
public import paper_results.minimum_tor_injection_core
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeCor53Core.BridgeAPI
universe u v w x
variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} {Z : Type x}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module R X] [Module R Y] [Module R Z]
theorem boundaryMap_val (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : g.comp f = 0) (z : X) :
    (FourPapers.FilteredHomology.boundaryMap f g h z).val = f z := rfl
end PalomarSublatticeCor53Core.BridgeAPI
namespace PalomarSublatticeCor53Core.Koszul
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

end PalomarSublatticeCor53Core.Koszul
namespace PalomarSublatticeCor53Core.Koszul
universe u
variable {V K : Type u} [Fintype V] [LinearOrder V] [Field K]

/-- The dimension of the actual homogeneous Koszul homology vector space. -/
def betti (I : Ideal (MvPolynomial V K)) (p : ℕ) (q : ℤ) : ℕ :=
  Module.finrank K (Homology I q p)
end PalomarSublatticeCor53Core.Koszul

namespace PalomarSublatticeCor53Core.Koszul
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

theorem piece_negative (I : Ideal (MvPolynomial V K)) {q : ℤ}
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

theorem differential_eq_source (I : Ideal (MvPolynomial V K)) (p : ℕ) :
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

theorem previous_eq_source (I : Ideal (MvPolynomial V K)) (p : ℕ) :
    previous I p = FourPapers.Sublattice.actualIdealPreviousDifferential I p := by
  cases p with
  | zero => rfl
  | succ p => exact differential_eq_source I p

theorem piece_nat_eq (P : FourPapers.Sublattice.QuotientGroebnerData V K)
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

end PalomarSublatticeCor53Core.Koszul

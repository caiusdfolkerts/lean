module
public import paper_results.part004
public import graph_foundation.part008
public import shared_results.part020
public import paper_results.part002
public import shared_results.part003
public import shared_results.part010
public import paper_results.part005
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CharacteristicPowerComparison -/
section

/-!
# Characteristic excess in every power and its first-coefficient consequence

These statements apply the actual all-power Tor decomposition to the
integer-matrix specialization theorem. Equality of an ordinary table
forces equality of each fine summand, because every characteristic excess
is nonnegative. Constant multichains then detect each predecessor colon.

The converse and the binomial expansion are developed in the subsequent
coefficient-independence and grouped-coefficient modules.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (Q K : Type u) [Field Q] [CharZero Q] [Field K]

/-- The characteristic excess is nonnegative in each genuine fine Tor
degree of every positive power. -/
theorem powerBettiNumber_charZero_le (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    bettiNumber (k:=Q) (exponentPowerFamily (finiteRowFamily n E) m) a p ≤
      bettiNumber (k:=K) (exponentPowerFamily (finiteRowFamily n E) m) a p := by
  rw [allPowerBetti_admissible hE m hm p a,allPowerBetti_admissible hE m hm p a]
  exact Finset.sum_le_sum (fun w _ => quotientBettiNumber_charZero_le Q K _ _ p)

theorem ordinaryPowerBetti_charZero_le (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k:=Q)
        (exponentPowerFamily (finiteRowFamily n E) m) q p ≤
      ordinaryMonomialBettiNumber (k:=K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum,ordinaryMonomialBettiNumber_eq_sum]
  exact Finset.sum_le_sum (fun a _ => powerBettiNumber_charZero_le Q K hE m hm a.val p)

private theorem summand_eq_of_equal_sum {I : Type*} [Fintype I]
    (f g : I → ℕ) (hle : ∀ i,f i≤g i) (hsum : ∑ i,f i=∑ i,g i) (i : I) :
    f i=g i := by
  by_contra hne
  have hlt := Finset.sum_lt_sum (s:=Finset.univ) (fun j _ => hle j)
    ⟨i,Finset.mem_univ _,by have hi:=hle i; omega⟩
  exact (ne_of_lt hlt) hsum

/-- Ordinary equality has no hidden cancellation between fine degrees:
all of their excesses have the same sign. -/
theorem fine_power_betti_eq_of_ordinary_eq (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m)
    (heq : ∀ q p,ordinaryMonomialBettiNumber (k:=Q)
        (exponentPowerFamily (finiteRowFamily n E) m) q p=
      ordinaryMonomialBettiNumber (k:=K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p)
    (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    bettiNumber (k:=Q) (exponentPowerFamily (finiteRowFamily n E) m) a p=
      bettiNumber (k:=K) (exponentPowerFamily (finiteRowFamily n E) m) a p := by
  have hs := heq a.degree p
  rw [ordinaryMonomialBettiNumber_eq_sum,ordinaryMonomialBettiNumber_eq_sum] at hs
  exact summand_eq_of_equal_sum
    (I := OrdinaryFineIndex (FiniteVariable.{u} n) a.degree)
    (fun b => bettiNumber (k := Q) (exponentPowerFamily (finiteRowFamily n E) m) b.val p)
    (fun b => bettiNumber (k := K) (exponentPowerFamily (finiteRowFamily n E) m) b.val p)
    (fun b => powerBettiNumber_charZero_le Q K hE m hm b.val p) hs
    (⟨a,rfl⟩ : OrdinaryFineIndex (FiniteVariable.{u} n) a.degree)

def constantFiniteMultichain (a : E) (m : ℕ) : FiniteMultichain n E m :=
  ⟨fun _ => a,fun _ _ _ => le_rfl⟩

theorem constantFiniteMultichain_coefficient (a : E) (m : ℕ) (hm : 0< m) :
    finiteChainCoefficientFamily.{u} n (constantFiniteMultichain a m)=
      finitePredecessorFamily n E a.val := by
  ext g
  simp only [finiteChainCoefficientFamily,Finset.mem_biUnion,Finset.mem_univ,
    true_and,constantFiniteMultichain]
  constructor
  · rintro ⟨_,hg⟩
    exact hg
  · intro hg
    exact ⟨⟨0,hm⟩,hg⟩

/-- Equality of one positive-power ordinary table forces characteristic
independence of every actual predecessor coefficient quotient, finely.
The all-field equivalence in Corollary 10.4 requires the converse as well;
this theorem states this proved direction with its exact quantifiers. -/
theorem predecessor_betti_eq_of_one_power_eq (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m)
    (heq : ∀ q p,ordinaryMonomialBettiNumber (k:=Q)
        (exponentPowerFamily (finiteRowFamily n E) m) q p=
      ordinaryMonomialBettiNumber (k:=K)
        (exponentPowerFamily (finiteRowFamily n E) m) q p)
    (a : E) (b : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    quotientBettiNumber (k:=Q) (finitePredecessorFamily n E a.val) b p=
      quotientBettiNumber (k:=K) (finitePredecessorFamily n E a.val) b p := by
  let w := constantFiniteMultichain a m
  let α := b+finiteChainShift n w
  let v : AdmissibleChain n E m α := ⟨w,by
    intro x
    simp only [α,Finsupp.add_apply]
    omega⟩
  have hs := fine_power_betti_eq_of_ordinary_eq Q K hE m hm heq α p
  rw [allPowerBetti_admissible hE m hm p α,allPowerBetti_admissible hE m hm p α] at hs
  have hv := summand_eq_of_equal_sum _ _
    (fun z => quotientBettiNumber_charZero_le Q K _ _ p) hs v
  simpa only [v,α,w,add_tsub_cancel_right,constantFiniteMultichain_coefficient a m hm] using hv

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.NaturalHomologyDecomposition -/
section

/-! # Decomposing a finite exterior complex by its actual homological degree

The differential lowers the natural basis degree by one and is zero in
degree zero. Regrading along `ℕ → ℤ` gives an honest shifted direct-sum
complex; the comparison with each natural three-term homology includes
homological degree zero.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.NaturalHomologyDecomposition
open Classical CommAlg FilteredHomology GradedHomologyDecomposition
open FourPapers.Sublattice
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Module.Basis I R M) (degree : I → ℕ)
  (D : Module.End R M) (hDD : D.comp D = 0)
  (hlower : ∀ i, D (b i) ∈ Grading.Piece b degree (degree i - 1))
  (hzero : ∀ i, degree i = 0 → D (b i) = 0)

def integerPiece (q : ℤ) : Submodule R M :=
  Grading.Piece b (fun i => (degree i : ℤ)) q

instance integerPiece_decomposition : DirectSum.Decomposition (integerPiece b degree) :=
  basisGradingDecomposition b (fun i => (degree i : ℤ))

lemma integerPiece_nat (p : ℕ) : integerPiece b degree (p : ℤ) = Grading.Piece b degree p := by
  rw [integerPiece, ← ordinaryIntegerRegrade_basisPiece, ordinaryIntegerRegrade_nat]

lemma integerPiece_negative (q : ℤ) (hq : q < 0) : integerPiece b degree q = ⊥ := by
  rw [integerPiece, ← ordinaryIntegerRegrade_basisPiece, ordinaryIntegerRegrade_negative _ q hq]

include hlower in
lemma differential_lowers (p : ℕ) (x : M) (hx : x ∈ Grading.Piece b degree (p+1)) :
    D x ∈ Grading.Piece b degree p := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change degree i = p+1 at hi
      simpa only [hi, Nat.add_sub_cancel] using hlower i
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Grading.Piece b degree p))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

include hzero in
lemma differential_zero (x : M) (hx : x ∈ Grading.Piece b degree 0) : D x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact hzero i hi
  | zero => exact map_zero D
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, add_zero]
  | smul r x hx ih => simp only [map_smul, ih, smul_zero]

include hlower hzero in
lemma differential_integerPiece (q : ℤ) (x : M) (hx : x ∈ integerPiece b degree q) :
    D x ∈ integerPiece b degree (q + (-1)) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [integerPiece_nat] at hx
    cases p with
    | zero => rw [differential_zero b degree D hzero x hx]; exact Submodule.zero_mem _
    | succ p =>
        rw [show ((p+1 : ℕ) : ℤ) + (-1) = (p : ℤ) by omega, integerPiece_nat]
        exact differential_lowers b degree D hlower p x hx
  · rw [integerPiece_negative b degree q (lt_of_not_ge hq), Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _

abbrev TotalHomology := Homology D D hDD
abbrev IntegerHomology (q : ℤ) := DegreeHomology (integerPiece b degree) D hDD q

def incoming (p : ℕ) : Grading.Piece b degree (p+1) →ₗ[R] Grading.Piece b degree p :=
  (D.domRestrict _).codRestrict _ (fun x => differential_lowers b degree D hlower p x.val x.property)

def outgoing (p : ℕ) : Grading.Piece b degree p →ₗ[R] M := D.domRestrict _

include hDD in
lemma incoming_comp (p : ℕ) : (outgoing b degree D p).comp (incoming b degree D hlower p) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hDD x.val

abbrev NaturalHomology (p : ℕ) := Homology (incoming b degree D hlower p)
  (outgoing b degree D p) (incoming_comp b degree D hDD hlower p)

def naturalPieceEquiv (p : ℕ) : Grading.Piece b degree p ≃ₗ[R] integerPiece b degree (p : ℤ) :=
  LinearEquiv.ofEq _ _ (integerPiece_nat b degree p).symm

def integerIncoming (p : ℕ) : Grading.Piece b degree (p+1) →ₗ[R] integerPiece b degree (p : ℤ) :=
  (naturalPieceEquiv b degree p).toLinearMap.comp (incoming b degree D hlower p)

include hDD in
lemma integerIncoming_comp (p : ℕ) :
    (D.domRestrict (integerPiece b degree (p : ℤ))).comp
      (integerIncoming b degree D hlower p) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hDD x.val

def naturalHomologyEquiv (p : ℕ) :
    NaturalHomology b degree D hDD hlower p ≃ₗ[R] IntegerHomology b degree D hDD (p : ℤ) := by
  let e := threeTermHomologyEquiv (R := R)
    (incoming b degree D hlower p) (outgoing b degree D p)
    (incoming_comp b degree D hDD hlower p)
    (integerIncoming b degree D hlower p) (D.domRestrict (integerPiece b degree (p : ℤ)))
    (integerIncoming_comp b degree D hDD hlower p)
    (LinearEquiv.refl R _) (naturalPieceEquiv b degree p) (LinearEquiv.refl R _)
    (fun _ => rfl) (fun _ => rfl)
  refine e.trans (degreeHomologyEquiv (integerPiece b degree) D hDD (p : ℤ)
    (integerIncoming b degree D hlower p) (integerIncoming_comp b degree D hDD hlower p)
    (fun y => ⟨y.val, rfl⟩) ?_)
  intro x hx
  rw [integerPiece_nat] at hx
  obtain ⟨y, hy, hDy⟩ := BasisHomology.homogeneous_filling b degree D hlower hzero p
    (D x) hx ⟨x, rfl⟩
  exact ⟨⟨y, hy⟩, hDy⟩

include hlower hzero in
def totalHomologyDecomposition :
    TotalHomology D hDD ≃ₗ[R] DirectSum ℤ (IntegerHomology b degree D hDD) :=
  homologyDecomposition (integerPiece b degree) D hDD
    (cycles_homogeneous _ _ (-1) (differential_integerPiece b degree D hlower hzero))
    (boundaries_homogeneous _ _ (-1) (differential_integerPiece b degree D hlower hzero))

lemma integerHomology_negative (q : ℤ) (hq : q < 0) :
    Subsingleton (IntegerHomology b degree D hDD q) := by
  have hz : ∀ x : degreeCycles (integerPiece b degree) D q, x = 0 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hx := x.property
    change x.val.val ∈ integerPiece b degree q at hx
    rw [integerPiece_negative b degree q hq, Submodule.mem_bot] at hx
    exact hx
  letI : Subsingleton (degreeCycles (integerPiece b degree) D q) :=
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  infer_instance

end FourPapers.NaturalHomologyDecomposition

#print axioms FourPapers.NaturalHomologyDecomposition.naturalHomologyEquiv

end
end
end


/- BEGIN EXACT BODY: FourPapers.Common.NaturalHomologyComparison -/
section

/-! # Comparing a natural-degree strand with a three-term complex

The comparison is proved with abstract coefficient modules first. Concrete
Koszul applications then retain the exact `NaturalHomology` source type,
avoiding repeated expansion of the underlying quotient structures.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.NaturalHomologyDecomposition
open CommAlg FilteredHomology
variable {R M I X Y Z : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- A commuting change of source and middle coordinates, followed by an
injective enlargement of the outgoing target, preserves literal homology. -/
def homologyEquivOfCoordinates
    (b : Module.Basis I R M) (degree : I → ℕ)
    (D : Module.End R M) (hDD : D.comp D = 0)
    (hlower : ∀ i, D (b i) ∈ Grading.Piece b degree (degree i-1)) (p : ℕ)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hfg : g.comp f = 0)
    (j : Z →ₗ[R] M) (hj : Function.Injective j)
    (eX : Grading.Piece b degree (p+1) ≃ₗ[R] X)
    (eY : Grading.Piece b degree p ≃ₗ[R] Y)
    (hf : ∀ x, eY (incoming b degree D hlower p x) = f (eX x))
    (hg : ∀ y, outgoing b degree D p y = j (g (eY y))) :
    NaturalHomology b degree D hDD hlower p ≃ₗ[R] Homology f g hfg :=
  (threeTermHomologyEquiv
    (incoming b degree D hlower p) (outgoing b degree D p)
    (incoming_comp b degree D hDD hlower p)
    f (j.comp g) (postcompose_comp_zero f g hfg j)
    eX eY (LinearEquiv.refl R M) hf hg).trans
      (homologyEquiv_postcompose f g hfg j hj).symm

end FourPapers.NaturalHomologyDecomposition

#print axioms FourPapers.NaturalHomologyDecomposition.homologyEquivOfCoordinates

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.SquarefreeTopOrdinaryDegree -/
section

/-! # The full squarefree degree is the only possible top ordinary degree

If every monomial generator is squarefree, every fine degree with an
exponent at least two is contracted by actual exterior creation. Hence
ordinary degree |V| has only the full squarefree homology summand. The
comparison is a module equivalence over the integers as well as a Betti
number equality over fields.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

theorem exists_gt_one_of_full_degree_ne_squarefree (α : Exponent V)
    (hdeg : α.degree=Fintype.card V) (hne : α≠faceExponent (Finset.univ : Finset V)) :
    ∃v : V,1<α v := by
  by_contra! hle
  apply hne
  ext v
  have hv : α v=1 := by
    by_contra hv
    have hvlt : α v<1 := lt_of_le_of_ne (hle v) hv
    have hh := Finset.sum_lt_sum (s := (Finset.univ : Finset V))
      (f := fun w => α w) (g := fun _ => (1:ℕ))
      (fun w _ => hle w) ⟨v,Finset.mem_univ _,hvlt⟩
    have hd : ∑w : V,α w=Fintype.card V := by simpa only [Finsupp.degree_eq_sum] using hdeg
    rw [hd] at hh
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,lt_self_iff_false] using hh
  simp only [faceExponent_apply,Finset.mem_univ,if_true,hv]

theorem squarefree_fine_homology_zero_outside (B : Family V)
    (hB : ∀b∈B,∀v,b v≤1) (α : Exponent V)
    (hα : ¬α≤faceExponent (Finset.univ : Finset V)) (p : ℕ) :
    Subsingleton ((homogeneousComplex (k := k) B α).homology p) := by
  have hn : ¬∀v,α v≤1 := by
    intro h
    apply hα
    intro v
    simpa only [faceExponent_apply,Finset.mem_univ,if_true] using h v
  obtain ⟨v,hv⟩ := not_forall.mp hn
  exact monomial_fine_homology_subsingleton_of_generator_bound B α v 1
    (fun b hb => hB b hb v) (Nat.lt_of_not_ge hv) p

theorem squarefree_full_degree_other_homology_zero (B : Family V)
    (hB : ∀b∈B,∀v,b v≤1) (α : Exponent V)
    (hdeg : α.degree=Fintype.card V) (hne : α≠faceExponent (Finset.univ : Finset V)) (p : ℕ) :
    Subsingleton ((homogeneousComplex (k := k) B α).homology p) := by
  obtain ⟨v,hv⟩ := exists_gt_one_of_full_degree_ne_squarefree α hdeg hne
  exact monomial_fine_homology_subsingleton_of_generator_bound B α v 1
    (fun b hb => hB b hb v) hv p

def onlyComponentEquiv {I : Type*} (A : I → Type u)
    [∀i,AddCommGroup (A i)] [∀i,Module k (A i)] (i₀ : I)
    (hz : ∀i,i≠i₀ → Subsingleton (A i)) : (∀i,A i) ≃ₗ[k] A i₀ :=
  LinearEquiv.ofBijective (LinearMap.proj i₀)
    ⟨by
      intro x y hxy
      funext i
      by_cases hi : i=i₀
      · subst i
        exact hxy
      · exact (hz i hi).allEq _ _,
      fun x => ⟨Pi.single i₀ x,by simp⟩⟩

def squarefreeTopOrdinaryHomologyEquiv (B : Family V) (hB : ∀b∈B,∀v,b v≤1) (p : ℕ) :
    ordinaryMonomialHomology (k := k) B (Fintype.card V) p ≃ₗ[k]
      (homogeneousComplex (k := k) B (faceExponent (Finset.univ : Finset V))).homology p := by
  let α₀ : OrdinaryFineIndex V (Fintype.card V) :=
    ⟨faceExponent Finset.univ,by simp only [degree_faceExponent,Finset.card_univ]⟩
  let A := fun α : OrdinaryFineIndex V (Fintype.card V) => monomialFineHomology (k := k) B α.val p
  have hz : ∀α,α≠α₀ → Subsingleton (A α) := by
    intro α hα
    letI := squarefree_full_degree_other_homology_zero (k := k) B hB α.val α.property
      (fun h => hα (Subtype.ext h)) p
    exact (monomialFineCategoricalHomologyEquiv B α.val p).symm.injective.subsingleton
  exact (ordinaryMonomialHomologyEquivPi B (Fintype.card V) p).trans
    ((onlyComponentEquiv (k := k) A α₀ hz).trans
      (monomialFineCategoricalHomologyEquiv B α₀.val p).symm)

def squarefreeTopOrdinaryTorEquiv [Nontrivial k]
    (B : Family V) (hB : ∀b∈B,∀v,b v≤1) (p : ℕ) :
    ordinaryMonomialHomology (k := k) B (Fintype.card V) p ≃ₗ[k]
      gradedTor (k := k) B (faceExponent (Finset.univ : Finset V)) p :=
  (squarefreeTopOrdinaryHomologyEquiv B hB p).trans
    (gradedTorIso B (faceExponent Finset.univ) p).toLinearEquiv

section Field
variable {K : Type u} [Field K]

theorem squarefreeTopOrdinaryBetti_eq (B : Family V) (hB : ∀b∈B,∀v,b v≤1) (p : ℕ) :
    ordinaryMonomialBettiNumber (k := K) B (Fintype.card V) p=
      bettiNumber (k := K) B (faceExponent (Finset.univ : Finset V)) p :=
  (squarefreeTopOrdinaryTorEquiv (k := K) B hB p).finrank_eq

/-- The same equality inside the genuine derived ordinary Tor module,
with the canonical presentation chosen only to name its graded piece. -/
theorem squarefreeTopOrdinaryDerivedBetti_eq (m : MonomialOrder V) (B : Family V)
    (hB : ∀b∈B,∀v,b v≤1)
    (hhom : (monomialIdeal K B).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (fun _ : V => (1:ℕ)))) (p : ℕ) :
    ordinaryIdealBettiNumber (canonicalQuotientGroebnerData m (monomialIdeal K B)) hhom
      p (Fintype.card V)=bettiNumber (k := K) B (faceExponent (Finset.univ : Finset V)) p := by
  rw [canonicalMonomialBettiNumber_eq]
  exact squarefreeTopOrdinaryBetti_eq B hB p

end Field
end FourPapers.Sublattice
end

end
end


end

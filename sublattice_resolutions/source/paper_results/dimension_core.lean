module
public import paper_results.part001
public import shared_results.part020
public import graph_foundation.part003
public import Mathlib.RingTheory.Depth.Basic
public import graph_foundation.part004
public import graph_foundation.part008
public import graph_foundation.part006
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.Fin.Tuple.Basic
public import paper_results.part009
public import paper_results.part002
public import paper_results.part004
public import paper_results.first_strand_occurrence

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulExtTorDuality -/
section

/-! # Genuine Ext/Tor duality and polynomial depth

The polynomial residue module is resolved by the actual Koszul complex.
The perfect exterior pairing identifies its Hom cohomology with coefficient
Koszul homology in complementary degrees. Both adjacent differentials,
their unit signs, and the degree-zero cohomological boundary are retained.
The depth consequence uses Mathlib's Ext definition of ideal depth.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.KoszulExtTorDuality
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CommAlg CommAlg.Koszul FourPapers.FilteredHomology
open FourPapers.KoszulExteriorDuality
open scoped TensorProduct
universe u
variable {k V : Type u} [CommRing k] [Nontrivial k] [Fintype V] [LinearOrder V]

abbrev S := MvPolynomial V k
abbrev Variables : V → (S (k := k) (V := V)) := MvPolynomial.X
abbrev Residue := FiniteResidue V k

/-- The existing polynomial resolution, with its chain complex transported
to the original variable-indexed exterior algebra. -/
def familyResolution : ProjectiveResolution (ModuleCat.of (S (k := k) (V := V)) (Residue (k := k) (V := V))) where
  complex := koszulComplex (Fintype.linearCombination (S (k := k) (V := V)) Variables)
  projective p := by
    change Projective (ModuleCat.of (S (k := k) (V := V))
      (Power (R := (S (k := k) (V := V))) (V := V) p))
    infer_instance
  π := finiteVariableKoszulIso.inv ≫ (finitePolynomialResolution (V := V) (k := k)).π

variable (M : ModuleCat.{u} (S (k := k) (V := V)))

abbrev C := familyCoefficientComplex (Variables (k := k) (V := V)) M

def d (p : ℕ) : (C M).X (p+1) →ₗ[(S (k := k) (V := V))] (C M).X p := ((C M).d (p+1) p).hom

theorem d_comp (p : ℕ) : (d M p).comp (d M (p+1)) = 0 := by
  exact congrArg ModuleCat.Hom.hom ((C M).d_comp_d (p+2) (p+1) p)

abbrev PositiveHomology (q : ℕ) := Homology (d M (q+1)) (d M q) (d_comp M q)

def categoricalPositiveHomologyEquiv (q : ℕ) :
    (C M).homology (q+1) ≃ₗ[(S (k := k) (V := V))] PositiveHomology M q :=
  (((C M).homologyIsoSc' (q+2) (q+1) q (by simp) (by simp)) ≪≫
    ((C M).sc' (q+2) (q+1) q).moduleCatHomologyIso).toLinearEquiv

def middleDuality (p q : ℕ) (h : q+p = Fintype.card V) :
    (C M).X q ≃ₗ[(S (k := k) (V := V))] ((familyResolution (k := k) (V := V)).complex.X p →ₗ[(S (k := k) (V := V))] M) :=
  coefficientDuality (coordinateVolume (R := (S (k := k) (V := V))) (V := V)) M p q
    (by simpa only [Module.finrank_eq_card_basis (Pi.basisFun (S (k := k) (V := V)) V)] using h)

def signedDuality (s p q : ℕ) (h : q+p = Fintype.card V) :
    (C M).X q ≃ₗ[(S (k := k) (V := V))] ((familyResolution (k := k) (V := V)).complex.X p →ₗ[(S (k := k) (V := V))] M) :=
  (middleDuality M p q h).trans (LinearEquiv.smulOfUnit ((-1 : (S (k := k) (V := V))ˣ)^s))

@[simp] theorem signedDuality_apply (s p q : ℕ) (h : q+p = Fintype.card V)
    (z : (C M).X q) :
    signedDuality M s p q h z = (-1 : (S (k := k) (V := V)))^s • middleDuality M p q h z := by
  change (↑((-1 : (S (k := k) (V := V))ˣ)^s) : (S (k := k) (V := V))) • middleDuality M p q h z = _
  simp

lemma sign_square (q : ℕ) : (-1 : (S (k := k) (V := V)))^q * (-1 : (S (k := k) (V := V)))^q = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem middleDuality_d (p q : ℕ) (h : (q+1)+p = Fintype.card V) (z : (C M).X (q+1)) :
    middleDuality M (p+1) q (by omega) (d M q z) =
      (-1 : (S (k := k) (V := V)))^q • ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M p
        (middleDuality M p (q+1) h z) := by
  have he := coefficientDuality_differential
    (coordinateVolume (R := (S (k := k) (V := V))) (V := V)) M Variables p q
    (by simpa only [Module.finrank_eq_card_basis (Pi.basisFun (S (k := k) (V := V)) V)] using h) z
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun he v
  simpa only [middleDuality, d, C, ProjectiveExtCohomology.differential,
    LinearMap.lcomp_apply', familyResolution, koszulComplex.d_eq_d,
    koszulComplex.X_eq_exteriorPower, ModuleCat.hom_ofHom,
    KoszulExteriorDuality.Power, KoszulExteriorDuality.Free,
    LinearMap.smul_apply, LinearMap.comp_apply] using! hv

theorem signedDuality_outgoing (p q : ℕ) (h : (q+1)+p = Fintype.card V)
    (z : (C M).X (q+1)) :
    signedDuality M q (p+1) q (by omega) (d M q z) =
      ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M p
        (middleDuality M p (q+1) h z) := by
  rw [signedDuality_apply, middleDuality_d, smul_smul, sign_square, one_smul]

def cyclesDuality (p q : ℕ) (h : (q+1)+p = Fintype.card V) :
    LinearMap.ker (d M q) ≃ₗ[(S (k := k) (V := V))]
      LinearMap.ker (ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M p) :=
  threeTermCyclesEquiv (d M q) (ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M p)
    (middleDuality M p (q+1) h) (signedDuality M q (p+1) q (by omega))
      (signedDuality_outgoing M p q h)

theorem cyclesDuality_boundaries (p q : ℕ) (h : (q+1)+p = Fintype.card V) :
    (LinearMap.range (boundaryMap (d M (q+1)) (d M q) (d_comp M q))).map
      (cyclesDuality M p q h).toLinearMap =
      LinearMap.range (boundaryMap (ProjectiveExtCohomology.incoming (familyResolution (k := k) (V := V)) M p)
        (ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M p)
        (ProjectiveExtCohomology.differential_comp (familyResolution (k := k) (V := V)) M p)) := by
  cases p with
  | zero =>
      letI : Module.Free (S (k := k) (V := V)) (V → S (k := k) (V := V)) :=
        Module.Free.of_basis (Pi.basisFun (S (k := k) (V := V)) V)
      letI : Module.Finite (S (k := k) (V := V)) (V → S (k := k) (V := V)) :=
        Module.Finite.of_basis (Pi.basisFun (S (k := k) (V := V)) V)
      have hlarge : Module.finrank (S (k := k) (V := V)) (V → (S (k := k) (V := V))) < q+2 := by
        rw [Module.finrank_eq_card_basis (Pi.basisFun (S (k := k) (V := V)) V)]
        omega
      letI : Subsingleton (Power (R := (S (k := k) (V := V))) (V := V) (q+2)) :=
        subsingleton_of_forall_eq 0 (exteriorPower.eq_zero_of_finrank_lt
          (R := S (k := k) (V := V)) (M := V → S (k := k) (V := V)) (q+2) hlarge)
      letI : Subsingleton ((C M).X (q+2)) := by
        change Subsingleton (Power (R := S (k := k) (V := V)) (V := V) (q+2) ⊗[S (k := k) (V := V)] M)
        infer_instance
      have hfzero : d M (q+1) = 0 := by
        ext z
        rw [Subsingleton.elim z 0, map_zero]
        rfl
      ext z
      constructor
      · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
        refine ⟨0, ?_⟩
        apply Subtype.ext
        change 0 = middleDuality M 0 (q+1) h (d M (q+1) x)
        rw [hfzero, LinearMap.zero_apply, map_zero]
      · rintro ⟨x, rfl⟩
        refine ⟨0, ⟨0, (boundaryMap (d M (q+1)) (d M q) (d_comp M q)).map_zero⟩, ?_⟩
        apply Subtype.ext
        change middleDuality M 0 (q+1) h 0 = 0
        exact map_zero _
  | succ p =>
      refine threeTermCyclesEquiv_range
        (d M (q+1)) (d M q) (d_comp M q)
        (ProjectiveExtCohomology.incoming (familyResolution (k := k) (V := V)) M (p+1))
        (ProjectiveExtCohomology.differential (familyResolution (k := k) (V := V)) M (p+1))
        (ProjectiveExtCohomology.differential_comp (familyResolution (k := k) (V := V)) M (p+1))
        (signedDuality M (q+1) p (q+2) (by omega))
        (middleDuality M (p+1) (q+1) h)
        (signedDuality M q (p+2) q (by omega))
        ?_ (signedDuality_outgoing M (p+1) q h)
      intro z
      erw [signedDuality_apply (k := k) (V := V) M (q+1) p (q+2) (by omega) z]
      have he := middleDuality_d M p (q+1) (by omega) z
      simpa only [ProjectiveExtCohomology.incoming, map_smul] using! he

def homologyCohomologyDuality (p q : ℕ) (h : (q+1)+p = Fintype.card V) :
    PositiveHomology M q ≃ₗ[(S (k := k) (V := V))]
      ProjectiveExtCohomology.Cohomology (familyResolution (k := k) (V := V)) M p :=
  Submodule.Quotient.equiv _ _ (cyclesDuality M p q h) (cyclesDuality_boundaries M p q h)

/-- Actual Ext from the polynomial residue field is actual Tor in the
complementary positive degree. The comparison is an explicit composite
of genuine cohomology and homology equivalences. -/
def extTorDuality (p q : ℕ) (h : (q+1)+p = Fintype.card V) :
    Ext (ModuleCat.of (S (k := k) (V := V)) (Residue (k := k) (V := V))) M p ≃ₗ[(S (k := k) (V := V))]
      finitePolynomialTor (q+1) M :=
  (ProjectiveExtCohomology.cohomologyExtEquiv (familyResolution (k := k) (V := V)) M p).symm.trans
    ((homologyCohomologyDuality M p q h).symm.trans
      ((categoricalPositiveHomologyEquiv M q).symm.trans
        (finitePolynomialTorIso (q+1) M).symm.toLinearEquiv))

/-- Genuine ideal depth is determined by the top nonzero coefficient
Koszul homology degree. This consequence uses the actual Ext definition
of depth and not a newly stipulated numerical invariant. -/
theorem depth_eq_of_topTor (n : ℕ) (hn : 0 < n) (hnN : n ≤ Fintype.card V)
    (htop : ¬IsZero (finitePolynomialTor n M))
    (hvanish : ∀ j : ℕ, n < j → IsZero (finitePolynomialTor j M)) :
    (MvPolynomial.idealOfVars V k).depth M = (Fintype.card V - n : ℕ) := by
  have hbase : (MvPolynomial.idealOfVars V k).depth M =
      (ModuleCat.of (S (k := k) (V := V)) (Residue (k := k) (V := V))).depth M := by
    exact ModuleCat.depth_eq_of_linearEquiv
      (Shrink.linearEquiv (S (k := k) (V := V)) (Residue (k := k) (V := V)))
      (LinearEquiv.refl (S (k := k) (V := V)) M)
  rw [hbase, ModuleCat.depth_eq_iff]
  constructor
  · have hn' : n-1+1 = n := by omega
    have e := extTorDuality M (Fintype.card V-n) (n-1) (by omega)
    rw [hn'] at e
    apply e.toEquiv.nontrivial_congr.mpr
    exact not_subsingleton_iff_nontrivial.mp
      (fun hh => htop (ModuleCat.isZero_iff_subsingleton.mpr hh))
  · intro i hi
    have hj : n < Fintype.card V-i := by omega
    have hj' : Fintype.card V-i-1+1 = Fintype.card V-i := by omega
    have e := extTorDuality M i (Fintype.card V-i-1) (by omega)
    rw [hj'] at e
    letI : Subsingleton (finitePolynomialTor (Fintype.card V-i) M) :=
      ModuleCat.isZero_iff_subsingleton.mp (hvanish _ hj)
    exact e.injective.subsingleton

end FourPapers.KoszulExtTorDuality
end

end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.NormalizedBettiSupport -/
section

/-! # Normalized support of the actual monomial Tor groups

The internal shift is subtracted in the integers, so every normalized
internal degree is retained. The definition is shared by first occurrence
and stabilization without importing either proof into the other.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The literal normalized support, using integer subtraction. -/
def normalizedBettiSupport (m : ℕ) : Set (ℕ × ℤ) :=
  {b | ∃ Q : ℕ, ordinaryMonomialBettiNumber (k := k)
    (exponentPowerFamily (finiteRowFamily n E) m) Q b.1 ≠ 0 ∧
      (Q : ℤ) - (d : ℤ) * m = b.2}


end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.BettiSupportStabilization -/
section

/-!
# Persistence and the exact stabilization bound in Theorem 8.1

The support below is defined from genuine ordinary Koszul homology, hence
from derived Tor by the proved comparison. Repeating the bottom element
leaves every coefficient ideal unchanged. Removing repetitions and the
bottom leaves a strict chain of at most h elements. Thus the bound max 1 h
is proved without assuming the first-appearance assertion.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma finitePredecessorFamily_bottom (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    finitePredecessorFamily.{u} n E (finiteLatticeBottom hE hne).val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hbE, r, hr, _⟩ := Finset.mem_filter.mp hb
  exact (not_lt_of_ge (finiteLatticeBottom_le hE hne ⟨b, hbE⟩ r)) hr

def bottomPrependChain (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) : FiniteMultichain n E (m+1) := by
  refine ⟨Fin.cons (finiteLatticeBottom hE hne) w.val, ?_⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact le_refl _
      | succ j => exact finiteLatticeBottom_le hE hne (w.val j)
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hh : i.val + 1 ≤ 0 := hij
          omega
      | succ j => exact w.property (Fin.succ_le_succ_iff.mp hij)

@[simp] lemma bottomPrependChain_coefficient (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) {m : ℕ} (w : FiniteMultichain n E m) :
    finiteChainCoefficientFamily.{u} n (bottomPrependChain hE hne w) =
      finiteChainCoefficientFamily n w := by
  ext g
  simp only [finiteChainCoefficientFamily, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Fin.exists_fin_succ, bottomPrependChain, Fin.cons_zero, Fin.cons_succ,
    finitePredecessorFamily_bottom, Finset.notMem_empty, false_or]

lemma exists_padded_chain (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m N : ℕ} (w : FiniteMultichain n E m) (hmN : m ≤ N) :
    ∃ v : FiniteMultichain n E N,
      finiteChainCoefficientFamily.{u} n v = finiteChainCoefficientFamily n w := by
  induction N, hmN using Nat.le_induction with
  | base => exact ⟨w, rfl⟩
  | succ N hN ih =>
      obtain ⟨v, hv⟩ := ih
      exact ⟨bottomPrependChain hE hne v, by rw [bottomPrependChain_coefficient, hv]⟩

lemma chainCoefficient_mem_iff_list {m : ℕ} (w : FiniteMultichain n E m)
    (g : Exponent (FiniteVariable.{u} n)) :
    g ∈ finiteChainCoefficientFamily n w ↔
      ∃ a ∈ List.ofFn w.val, g ∈ finitePredecessorFamily n E a.val := by
  simp only [finiteChainCoefficientFamily, Finset.mem_biUnion, Finset.mem_univ,
    true_and, List.mem_ofFn]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨w.val s, ⟨s, rfl⟩, hs⟩
  · rintro ⟨a, ⟨s, rfl⟩, ha⟩
    exact ⟨s, ha⟩

def nonbottomChainList (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) : List E :=
  (List.ofFn w.val).dedup.filter (fun a => a ≠ finiteLatticeBottom hE hne)

lemma nonbottomChainList_mem (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) (a : E) :
    a ∈ nonbottomChainList hE hne w ↔
      (∃ s, w.val s = a) ∧ a ≠ finiteLatticeBottom hE hne := by
  simp [nonbottomChainList, List.mem_ofFn]

lemma nonbottomChainList_pairwise (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) :
    (nonbottomChainList hE hne w).Pairwise (· ≤ ·) :=
  (finiteChain_ofFn_pairwise w).sublist
    (List.filter_sublist.trans (List.dedup_sublist _))

lemma nonbottomChainList_length (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) :
    (nonbottomChainList hE hne w).length ≤ finiteLatticeHeight hE hne := by
  have hn : (nonbottomChainList hE hne w).Nodup := (List.nodup_dedup (List.ofFn w.val)).filter _
  rw [← List.toFinset_card_of_nodup hn]
  apply finiteLattice_chain_card hE hne
  · intro a ha b hb _
    obtain ⟨⟨i, rfl⟩, _⟩ := (nonbottomChainList_mem hE hne w a).mp
      (List.mem_toFinset.mp ha)
    obtain ⟨⟨j, rfl⟩, _⟩ := (nonbottomChainList_mem hE hne w b).mp
      (List.mem_toFinset.mp hb)
    rcases le_total i j with hij | hji
    · exact Or.inl (w.property hij)
    · exact Or.inr (w.property hji)
  · intro hb
    exact ((nonbottomChainList_mem hE hne w _).mp (List.mem_toFinset.mp hb)).2 rfl

lemma nonbottomChain_coefficient (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m : ℕ} (w : FiniteMultichain n E m) :
    finiteChainCoefficientFamily.{u} n
      (multichainOfList (nonbottomChainList hE hne w)
        (nonbottomChainList_pairwise hE hne w)) = finiteChainCoefficientFamily n w := by
  ext g
  rw [chainCoefficient_mem_iff_list, multichainOfList_ofFn,
    chainCoefficient_mem_iff_list]
  constructor
  · rintro ⟨a, ha, hg⟩
    obtain ⟨⟨s, rfl⟩, _⟩ := (nonbottomChainList_mem hE hne w a).mp ha
    exact ⟨w.val s, List.mem_ofFn.mpr ⟨s, rfl⟩, hg⟩
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, (nonbottomChainList_mem hE hne w a).mpr ⟨List.mem_ofFn.mp ha, ?_⟩, hg⟩
    intro he
    subst a
    simpa only [finitePredecessorFamily_bottom, Finset.notMem_empty] using hg

/-- Every coefficient ideal occurring at any power already occurs at the
specified stabilization power. The construction retains the exact ideal. -/
theorem exists_stabilized_coefficient_chain (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) {m : ℕ} (w : FiniteMultichain n E m) :
    ∃ v : FiniteMultichain n E (max 1 (finiteLatticeHeight hE hne)),
      finiteChainCoefficientFamily.{u} n v = finiteChainCoefficientFamily n w := by
  let v := multichainOfList (nonbottomChainList hE hne w)
    (nonbottomChainList_pairwise hE hne w)
  obtain ⟨z, hz⟩ := exists_padded_chain.{u} hE hne v
    ((nonbottomChainList_length hE hne w).trans (le_max_right _ _))
  exact ⟨z, hz.trans (nonbottomChain_coefficient hE hne w)⟩

section Field
variable {k : Type u} [Field k]

/-- Ordinary total degree is retained in the genuine Tor formula. -/
theorem ordinary_power_betti_nonzero_iff (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (Q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) Q p ≠ 0 ↔
    ∃ w : FiniteMultichain n E m, ∃ β : Exponent (FiniteVariable.{u} n),
      Q = m * d + β.degree ∧
      quotientBettiNumber (k := k) (finiteChainCoefficientFamily n w) β p ≠ 0 := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  constructor
  · intro h
    obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [allPowerBetti_admissible hE m hm p α.val] at hα
    obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    refine ⟨w.val, α.val - finiteChainShift n w.val, ?_, hw⟩
    have hd := congrArg Finsupp.degree (tsub_add_cancel_of_le w.property)
    rw [map_add, finiteChainShift_degree, α.property] at hd
    omega
  · rintro ⟨w, β, hQ, hβ⟩
    let α : OrdinaryFineIndex (FiniteVariable.{u} n) Q :=
      ⟨β + finiteChainShift n w, by rw [map_add, finiteChainShift_degree]; omega⟩
    let v : AdmissibleChain n E m α.val :=
      ⟨w, by intro x; simp only [α, Finsupp.add_apply]; omega⟩
    have hterm : quotientBettiNumber (k := k) (finiteChainCoefficientFamily n v.val)
        (α.val-finiteChainShift n v.val) p ≠ 0 := by
      simpa only [α, v, add_tsub_cancel_right] using hβ
    have hfine : 0 < bettiNumber (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) α.val p := by
      rw [allPowerBetti_admissible hE m hm p α.val]
      exact (Nat.pos_of_ne_zero hterm).trans_le
        (Finset.single_le_sum (f := fun w : AdmissibleChain n E m α.val =>
          quotientBettiNumber (k := k) (finiteChainCoefficientFamily n w.val)
            (α.val-finiteChainShift n w.val) p)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
    exact ne_of_gt (hfine.trans_le
      (Finset.single_le_sum (f := fun a : OrdinaryFineIndex (FiniteVariable.{u} n) Q =>
        bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m) a.val p)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ α)))


theorem mem_normalizedBettiSupport_iff (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (b : ℕ × ℤ) :
    b ∈ normalizedBettiSupport (k := k) (n := n) (E := E) m ↔
      ∃ w : FiniteMultichain n E m, ∃ β : Exponent (FiniteVariable.{u} n),
        (β.degree : ℤ) = b.2 ∧
        quotientBettiNumber (k := k) (finiteChainCoefficientFamily n w) β b.1 ≠ 0 := by
  constructor
  · rintro ⟨Q, hQ, hb⟩
    obtain ⟨w, β, hdeg, hβ⟩ := (ordinary_power_betti_nonzero_iff hE m hm Q b.1).mp hQ
    refine ⟨w, β, ?_, hβ⟩
    rw [hdeg, Nat.cast_add, Nat.cast_mul] at hb
    nlinarith
  · rintro ⟨w, β, hβ, hnonzero⟩
    refine ⟨m*d+β.degree,
      (ordinary_power_betti_nonzero_iff hE m hm _ b.1).mpr ⟨w, β, rfl, hnonzero⟩, ?_⟩
    push_cast
    nlinarith

/-- Nondecreasing normalized support at every positive power. -/
theorem normalizedBettiSupport_mono (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    normalizedBettiSupport (k := k) (n := n) (E := E) m ⊆
      normalizedBettiSupport (k := k) (n := n) (E := E) N := by
  intro b hb
  obtain ⟨w, β, hdeg, hβ⟩ := (mem_normalizedBettiSupport_iff hE m hm b).mp hb
  obtain ⟨v, hv⟩ := exists_padded_chain.{u} hE hne w hmN
  exact (mem_normalizedBettiSupport_iff hE N (hm.trans_le hmN) b).mpr
    ⟨v, β, hdeg, by simpa only [hv] using hβ⟩

/-- The exact support-stabilization clause of Theorem 8.1. -/
theorem theorem81_support_stabilization (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    normalizedBettiSupport (k := k) (n := n) (E := E) m =
      normalizedBettiSupport (k := k) (n := n) (E := E)
        (max 1 (finiteLatticeHeight hE hne)) := by
  have hM : 0 < max 1 (finiteLatticeHeight hE hne) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨w, β, hdeg, hβ⟩ :=
      (mem_normalizedBettiSupport_iff hE m (hM.trans_le hm) b).mp hb
    obtain ⟨v, hv⟩ := exists_stabilized_coefficient_chain.{u} hE hne w
    exact (mem_normalizedBettiSupport_iff hE _ hM b).mpr
      ⟨v, β, hdeg, by simpa only [hv] using hβ⟩
  · exact normalizedBettiSupport_mono hE hne hM hm

end Field
end FourPapers.Sublattice
end


end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.SaturatedChainColons -/
section

/-!
# The maximal-chain complete intersection in Theorem 8.1

The argument is stated first for any saturated chain from the actual bottom.
For b below its j-th entry, meet b with the preceding entry and use the cover
property. Induction finds a crossed ratio dividing the predecessor ratio.
This proves equality with the genuine colon sum. The crossed ratios are
nonzero squarefree monomials with pairwise disjoint variable supports.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma finiteRatio_nonzero_iff {b a : FiniteTuple n} (hba : b ≤ a)
    (r : Fin d) (j : Fin (n r)) :
    (finiteRowExponent.{u} n b - finiteRowExponent n a) ⟨r, ULift.up j⟩ ≠ 0 ↔
      b r = j ∧ b r < a r := by
  rw [Finsupp.tsub_apply, finiteRowExponent_apply, finiteRowExponent_apply]
  by_cases hb : b r = j
  · rw [if_pos hb]
    by_cases ha : a r = j
    · simp [ha, hb]
    · rw [if_neg ha, Nat.sub_zero]
      constructor
      · intro _
        exact ⟨hb, lt_of_le_of_ne (hba r) (fun he => ha (he.symm.trans hb))⟩
      · intro _
        exact Nat.one_ne_zero
  · simp [hb]

lemma finiteRatio_le_one (b a : FiniteTuple n) (x : FiniteVariable.{u} n) :
    (finiteRowExponent n b - finiteRowExponent n a) x ≤ 1 := by
  obtain ⟨r, ⟨j⟩⟩ := x
  simp only [Finsupp.tsub_apply, finiteRowExponent_apply]
  split_ifs <;> omega

lemma finiteRatio_ne_zero {b a : FiniteTuple n} (hba : b ≤ a) (hne : b ≠ a) :
    finiteRowExponent.{u} n b - finiteRowExponent n a ≠ 0 := by
  intro hz
  apply hne
  funext r
  by_contra h
  have hlt : b r < a r := lt_of_le_of_ne (hba r) h
  have hh := (finiteRatio_nonzero_iff.{u} hba r (b r)).mpr ⟨rfl, hlt⟩
  exact hh (congrArg (fun v : Exponent (FiniteVariable.{u} n) =>
    v ⟨r, ULift.up (b r)⟩) hz)

/-- Meeting b with an earlier chain entry only removes variables from the
ratio against any later entry. -/
lemma finiteMeet_ratio_le_later (b a c : FiniteTuple n) (hac : a ≤ c) :
    finiteRowExponent.{u} n (b ⊓ a) - finiteRowExponent n a ≤
      finiteRowExponent n b - finiteRowExponent n c := by
  rintro ⟨r, ⟨j⟩⟩
  by_cases hba : b r < a r
  · have hbc : b r < c r := hba.trans_le (hac r)
    simp only [Finsupp.tsub_apply, finiteRowExponent_apply, Pi.inf_apply,
      inf_eq_left.mpr hba.le]
    by_cases hb : b r = j
    · have ha : a r ≠ j := fun he => hba.ne (hb.trans he.symm)
      have hc : c r ≠ j := fun he => hbc.ne (hb.trans he.symm)
      simp [hb, ha, hc]
    · simp [hb]
  · have hab : a r ≤ b r := le_of_not_gt hba
    simp only [Finsupp.tsub_apply, finiteRowExponent_apply, Pi.inf_apply,
      inf_eq_right.mpr hab, tsub_self]
    exact Nat.zero_le _

section Saturated
variable (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
variable {h : ℕ} (C : Fin (h+1) → E)
  (hC : Monotone C)
  (hbot : C 0 = finiteLatticeBottom hE hne)
  (hcover : ∀ i : Fin h, C i.castSucc ⋖ C i.succ)

def saturatedCrossingRatio (i : Fin h) : Exponent (FiniteVariable.{u} n) :=
  finiteRowExponent n (C i.castSucc).val - finiteRowExponent n (C i.succ).val

include hE hne hC hbot hcover in
/-- A predecessor ratio is divisible by one of the actual cover ratios. -/
theorem saturated_predecessor_divisor (j : Fin (h+1)) (b : E)
    (hb : b ≤ C j) (hbne : b ≠ C j) :
    ∃ i : Fin h, i.val < j.val ∧
      saturatedCrossingRatio C i ≤
        finiteRowExponent.{u} n b.val - finiteRowExponent n (C j).val := by
  induction j using Fin.induction generalizing b with
  | zero =>
      have hh : C 0 ≤ b := by rw [hbot]; exact finiteLatticeBottom_le hE hne b
      exact (hbne (le_antisymm hb hh)).elim
  | succ j ih =>
      by_cases hprev : C j.castSucc ≤ b
      · rcases (hcover j).eq_or_eq hprev hb with he | he
        · subst b
          exact ⟨j, by simp, le_rfl⟩
        · exact (hbne he).elim
      · let b' : E := ⟨b.val ⊓ (C j.castSucc).val,
          hE.1 _ b.property _ (C j.castSucc).property⟩
        have hb' : b' ≤ C j.castSucc := fun r => inf_le_right
        have hbne' : b' ≠ C j.castSucc := by
          intro he
          apply hprev
          have hle : b' ≤ b := fun r => inf_le_left
          rwa [he] at hle
        obtain ⟨i, hij, hdiv⟩ := ih b' hb' hbne'
        refine ⟨i, by simpa only [Fin.val_succ, Fin.val_castSucc, Nat.succ_eq_add_one] using Nat.lt_succ_of_lt hij, ?_⟩
        exact hdiv.trans (finiteMeet_ratio_le_later b.val (C j.castSucc).val
          (C j.succ).val (hcover j).le)

def saturatedPositiveChain : FiniteMultichain n E h :=
  ⟨fun i => C i.succ, fun _ _ hij => hC (Fin.succ_le_succ_iff.mpr hij)⟩

def saturatedCrossingFamily : Family (FiniteVariable.{u} n) :=
  Finset.univ.image (saturatedCrossingRatio C)

include hE hne hbot hcover in
/-- Exact equality of the coefficient divisibility predicates. -/
theorem saturated_coefficient_contains (α : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily n (saturatedPositiveChain C hC)) α ↔
      Contains (saturatedCrossingFamily C) α := by
  rw [← finiteChainCoordinate_contains_iff hE]
  constructor
  · rintro ⟨g, hg, hgα⟩
    obtain ⟨j, _, hg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hbE, hb, hbne⟩ := Finset.mem_filter.mp hb
    obtain ⟨i, _, hi⟩ := saturated_predecessor_divisor hE hne C hC hbot hcover
      j.succ ⟨b, hbE⟩ hb (fun he => hbne (congrArg Subtype.val he))
    exact ⟨saturatedCrossingRatio C i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      hi.trans hgα⟩
  · rintro ⟨g, hg, hgα⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨saturatedCrossingRatio C i, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, ?_⟩, hgα⟩
    exact Finset.mem_image.mpr ⟨(C i.castSucc).val, Finset.mem_filter.mpr
      ⟨(C i.castSucc).property, (hcover i).le,
        fun he => (hcover i).ne (Subtype.ext he)⟩, rfl⟩

include hE hne hbot hcover in
theorem saturated_coefficient_ideal {k : Type*} [CommSemiring k] :
    monomialIdeal k (finiteChainCoefficientFamily n (saturatedPositiveChain C hC)) =
      monomialIdeal k (saturatedCrossingFamily C) := by
  ext f
  simp_rw [mem_monomialIdeal_iff,
    saturated_coefficient_contains hE hne C hC hbot hcover]

include hcover in
lemma saturatedCrossingRatio_nonzero (i : Fin h) :
    saturatedCrossingRatio.{u} C i ≠ 0 :=
  finiteRatio_ne_zero (hcover i).le (fun he => (hcover i).ne (Subtype.ext he))

lemma saturatedCrossingRatio_squarefree (i : Fin h) (x : FiniteVariable.{u} n) :
    saturatedCrossingRatio C i x ≤ 1 :=
  finiteRatio_le_one _ _ x

include hC hcover in
lemma saturatedCrossingRatio_disjoint {i j : Fin h} (hij : i ≠ j) :
    Disjoint (saturatedCrossingRatio.{u} C i).support
      (saturatedCrossingRatio C j).support := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨r, ⟨a⟩⟩ := x
  obtain ⟨hi, hi'⟩ := (finiteRatio_nonzero_iff (hcover i).le r a).mp
    (Finsupp.mem_support_iff.mp hxi)
  obtain ⟨hj, hj'⟩ := (finiteRatio_nonzero_iff (hcover j).le r a).mp
    (Finsupp.mem_support_iff.mp hxj)
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hh : (C i.succ).val r ≤ (C j.castSucc).val r :=
      hC (show i.succ ≤ j.castSucc by simpa using hij') r
    exact (not_lt_of_ge hh) (by simpa only [hi, hj] using hi')
  · have hh : (C j.succ).val r ≤ (C i.castSucc).val r :=
      hC (show j.succ ≤ i.castSucc by simpa using hji') r
    exact (not_lt_of_ge hh) (by simpa only [hi, hj] using hj')

end Saturated

def maximalPositiveChain (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    FiniteMultichain n E (finiteLatticeHeight hE hne) :=
  saturatedPositiveChain (finiteLatticeMaximalChain hE hne)
    (finiteLatticeMaximalChain_strictMono hE hne).monotone

def maximalCrossingFamily (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    Family (FiniteVariable.{u} n) :=
  saturatedCrossingFamily (finiteLatticeMaximalChain hE hne)

theorem maximalChain_coefficient_contains (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (α : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily n (maximalPositiveChain hE hne)) α ↔
      Contains (maximalCrossingFamily hE hne) α :=
  saturated_coefficient_contains hE hne (finiteLatticeMaximalChain hE hne)
    (finiteLatticeMaximalChain_strictMono hE hne).monotone
    (finiteLatticeMaximalChain_zero hE hne) (finiteLatticeMaximalChain_covBy hE hne) α

end FourPapers.Sublattice
end


end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81LowerBound -/
section

/-!
# The sharp projective-dimension lower bound in Theorem 8.1

The maximal chain has exactly h cover steps, where h is the actual number
of join-irreducibles. Its coefficient quotient has a displayed nonzero
fine degree-h Koszul class. The all-power formula carries this class to
every power at least h, by padding the chain with the actual bottom.
The final bound uses Mathlib's projective dimension of the literal ideal.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type u} [Field k]

def maximalCrossingDegree (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    Exponent (FiniteVariable.{u} n) :=
  ∑ i, saturatedCrossingRatio (finiteLatticeMaximalChain hE hne) i

lemma maximalChain_contains_crossing (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (α : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily n (maximalPositiveChain hE hne)) α ↔
      ∃ i, saturatedCrossingRatio (finiteLatticeMaximalChain hE hne) i ≤ α := by
  rw [maximalChain_coefficient_contains]
  constructor
  · rintro ⟨a, ha, haα⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, haα⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩

/-- The coefficient ideal has a genuine nonzero top derived-Tor component,
with its fine degree displayed explicitly. -/
theorem maximalChain_top_betti_nonzero (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hh : 0 < finiteLatticeHeight hE hne) :
    quotientBettiNumber (k := k)
      (finiteChainCoefficientFamily n (maximalPositiveChain hE hne))
      (maximalCrossingDegree.{u} hE hne) (finiteLatticeHeight hE hne) ≠ 0 := by
  letI : Nonempty (Fin (finiteLatticeHeight hE hne)) := ⟨⟨0, hh⟩⟩
  let C := finiteLatticeMaximalChain hE hne
  have hC : Monotone C := (finiteLatticeMaximalChain_strictMono hE hne).monotone
  have hn := saturatedCrossingRatio_nonzero (C := C) (hcover := finiteLatticeMaximalChain_covBy hE hne)
  have hs := saturatedCrossingRatio_squarefree (C := C)
  have hd : Pairwise (fun i j => Disjoint
      (saturatedCrossingRatio.{u} C i).support (saturatedCrossingRatio C j).support) := by
    intro i j hij
    exact saturatedCrossingRatio_disjoint C hC (finiteLatticeMaximalChain_covBy hE hne) hij
  have he := disjointSquarefree_quotientBetti_nonzero (K := k)
    (saturatedCrossingRatio C) hn hs hd
    (finiteChainCoefficientFamily n (maximalPositiveChain hE hne))
    (maximalChain_contains_crossing hE hne)
  simpa only [Fintype.card_fin, blockTotalExponent, maximalCrossingDegree, C] using he

theorem power_top_betti_nonzero (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (hh : 0 < finiteLatticeHeight hE hne) (m : ℕ) (hm : finiteLatticeHeight hE hne ≤ m) :
    ordinaryMonomialBettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m)
      (m*d + (maximalCrossingDegree.{u} hE hne).degree) (finiteLatticeHeight hE hne) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_padded_chain.{u} hE hne (maximalPositiveChain hE hne) hm
  apply (ordinary_power_betti_nonzero_iff (k := k) hE m (hh.trans_le hm)
    (m*d + (maximalCrossingDegree.{u} hE hne).degree) (finiteLatticeHeight hE hne)).mpr
  refine ⟨w, maximalCrossingDegree.{u} hE hne, rfl, ?_⟩
  rw [hw]
  exact maximalChain_top_betti_nonzero (k := k) hE hne hh

lemma ordinaryBetti_nonzero_le_projectiveDimension {V : Type u}
    [Fintype V] [LinearOrder V] (B : Family V) (Q p : ℕ)
    (h : ordinaryMonomialBettiNumber (k := k) B Q p ≠ 0) :
    (p : WithBot ℕ∞) ≤ projectiveDimension (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) := by
  rw [ordinaryMonomialBettiNumber_eq_sum] at h
  obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact finitePolynomialTor_nonzero_le_projectiveDimension (V := V) (k := k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) p
    (derivedTor_nonzero_of_graded (k := k) B α.val p
      ((bettiNumber_pos_iff (k := k) B α.val p).mp (Nat.pos_of_ne_zero hα)))

lemma finiteSublatticePower_not_isZero (hne : E.Nonempty) (m : ℕ) :
    ¬IsZero (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k := k) E)^m)) := by
  obtain ⟨a, ha⟩ := hne
  let u : MvPolynomial (FiniteVariable.{u} n) k := finiteRowMonomial n a
  have hu : u ∈ finiteSublatticeIdeal n (k := k) E :=
    Ideal.subset_span ⟨a, ha, rfl⟩
  have hu0 : u ≠ 0 := by
    dsimp only [u]
    rw [finiteRowMonomial_eq_monomial]
    intro he
    exact one_ne_zero (MvPolynomial.monomial_eq_zero.mp he)
  intro hzero
  letI : Subsingleton ↥((finiteSublatticeIdeal n (k := k) E)^m) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  have he : (⟨u^m, Ideal.pow_mem_pow hu m⟩ :
      ↥((finiteSublatticeIdeal n (k := k) E)^m)) = 0 := Subsingleton.elim _ _
  exact pow_ne_zero m hu0 (congrArg Subtype.val he)

/-- The lower-bound clause for every m at least max(1,h), including h=0.
Together with the cellular upper bound this gives the exact projective
dimension asserted in Theorem 8.1. -/
theorem theorem81_projectiveDimension_lower (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne) ≤ m) :
    (finiteLatticeHeight hE hne : WithBot ℕ∞) ≤
      projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
        ↥((finiteSublatticeIdeal n (k := k) E)^m)) := by
  by_cases hh : finiteLatticeHeight hE hne = 0
  · rw [hh, Nat.cast_zero]
    exact (projectiveDimension_ge_zero_iff _).mpr (finiteSublatticePower_not_isZero (k := k) hne m)
  · have hpos := Nat.pos_of_ne_zero hh
    have he := ordinaryBetti_nonzero_le_projectiveDimension
      (V := FiniteVariable.{u} n) (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m)
      (m*d + (maximalCrossingDegree.{u} hE hne).degree) (finiteLatticeHeight hE hne)
      (power_top_betti_nonzero (k := k) hE hne hpos m ((le_max_right _ _).trans hm))
    rwa [finitePowerFamily_ideal (n := n) (k := k) E m] at he

end FourPapers.Sublattice
end


end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem81ProjectiveDimension -/
section

/-! # The exact eventual projective dimension in Theorem 8.1 -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open CategoryTheory
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  {k : Type u} [Field k]

theorem theorem81_projectiveDimension (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (m : ℕ) (hm : max 1 (finiteLatticeHeight hE hne)≤m) :
    projectiveDimension (ModuleCat.of (MvPolynomial (FiniteVariable.{u} n) k)
      ↥((finiteSublatticeIdeal n (k:=k) E)^m)) =
        (finiteLatticeHeight hE hne : WithBot ℕ∞) :=
  le_antisymm (theorem81_projectiveDimension_upper (k := k) hE hne m)
    (theorem81_projectiveDimension_lower (k := k) hE hne m hm)

end FourPapers.Sublattice

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.Corollary53 -/
section

/-! # Corollary 5.3: first occurrence in the actual normalized Tor support

The normalized degree is an integer. Membership in this support means that
an actual ordinary Tor group is nonzero, with the shift `dm` subtracted in ℤ.
The multiplication-map assertion of the corollary is a separate construction.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

theorem corollary53_first_occurrence (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (h : (p, q) ∈ normalizedBettiSupport (k := k) (n := n) (E := E) m) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧
      (p, q) ∈ normalizedBettiSupport (k := k) (n := n) (E := E) r := by
  obtain ⟨Q, hQ, hq⟩ := h
  rw [ordinaryMonomialBettiNumber_eq_sum (k := k)] at hQ
  obtain ⟨α, _, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  obtain ⟨r, hr, hrp, γ, hdegree, hγ⟩ :=
    fine_first_strand_occurrence (k := k) hE m hm α.val p hp hα
  refine ⟨r, hr, hrp, γ.degree, ?_, ?_⟩
  · rw [ordinaryMonomialBettiNumber_eq_sum (k := k)]
    let a : OrdinaryFineIndex (FiniteVariable.{u} n) γ.degree := ⟨γ, rfl⟩
    exact ne_of_gt ((Nat.pos_of_ne_zero hγ).trans_le
      (Finset.single_le_sum (a := a) (s := Finset.univ)
        (f := fun a : OrdinaryFineIndex (FiniteVariable.{u} n) γ.degree =>
        bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) r) a.val p)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)))
  · rw [α.property] at hdegree
    change (Q : ℤ) - (d : ℤ) * m = q at hq
    change (γ.degree : ℤ) - (d : ℤ) * r = q
    nlinarith

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary53_first_occurrence

end
end
end


end

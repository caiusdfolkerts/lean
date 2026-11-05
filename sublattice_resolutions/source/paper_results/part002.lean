module
public import graph_foundation.part014
public import shared_results.part001
public import paper_results.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.CoefficientProjectiveDimension -/
section

/-! # Genuine projective-dimension detection by coefficient Koszul homology

This proves the needed vanishing theorem directly from a projective presentation and
its homology long exact sequence. No balance theorem for `Tor` and `Tor'` is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

/-- Tensor a fixed chain complex with a variable coefficient module. -/
def tensorCoefficientFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  map f := (((tensoringRight (ModuleCat R)).map f).mapHomologicalComplex
    (ComplexShape.down ℕ)).app K
  map_id M := by simp
  map_comp f g := by simp

instance tensorCoefficientFunctor_preservesZero (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (tensorCoefficientFunctor K).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (tensorLeft (K.X i)).map (0 : X ⟶ Y) = 0
    exact Functor.map_zero _ _ _

/-- Flat chain groups preserve short exact coefficient sequences degree by degree. -/
lemma tensorCoefficient_shortExact (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (tensorCoefficientFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  letI : Module.Flat R (K.X i) := hflat i
  change (S.map (tensorLeft (K.X i))).ShortExact
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (Module.Flat.lTensor_shortComplex_exact (K.X i) S hS.exact) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K.X i) S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective (K.X i)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

/-- Tensoring an exact positive-degree complex with a projective coefficient module preserves exactness. -/
lemma tensorCoefficient_isZero_of_projective
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) [Projective M] (i : ℕ) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology (i + 1)) := by
  letI : Module.Flat R M := inferInstance
  apply HomologicalComplex.ExactAt.isZero_homology
  change ((K.sc (i + 1)).map (tensorRight M)).Exact
  exact Module.Flat.rTensor_shortComplex_exact M (K.sc (i + 1)) (hexact i)

/-- If the actual projective dimension is below `n`, coefficient homology vanishes in degree `n`.
The induction uses actual projective presentations and actual homology connecting maps. -/
lemma tensorCoefficient_isZero_of_hasProjectiveDimensionLT
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (n : ℕ) (M : ModuleCat.{u} R) (hM : HasProjectiveDimensionLT M n) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology n) := by
  induction n generalizing M with
  | zero =>
      have hz : IsZero M := (hasProjectiveDimensionLT_zero_iff_isZero M).mp hM
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map_isZero
        ((tensorCoefficientFunctor K).map_isZero hz)
  | succ n ih =>
      cases n with
      | zero =>
          letI : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
          exact tensorCoefficient_isZero_of_projective K hexact M 0
      | succ n =>
          let ⟨p⟩ := EnoughProjectives.presentation M
          let S := ShortComplex.mk (kernel.ι p.f) p.f (kernel.condition p.f)
          have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
          have hKer : HasProjectiveDimensionLT S.X₁ (n + 1) :=
            (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
          have hleft := tensorCoefficient_isZero_of_projective K hexact S.X₂ (n + 1)
          have hright := ih S.X₁ hKer
          have ht := tensorCoefficient_shortExact K hflat S hS
          have he := ht.homology_exact₃ (n + 2) (n + 1) (by rfl)
          exact he.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

/-- Nonzero coefficient homology supplies a lower bound for Mathlib's actual projective dimension. -/
lemma tensorCoefficient_nonzero_le_projectiveDimension
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) (n : ℕ)
    (h : ¬ IsZero (((tensorCoefficientFunctor K).obj M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  rw [projectiveDimension_ge_iff]
  exact fun hM => h (tensorCoefficient_isZero_of_hasProjectiveDimensionLT K hflat hexact n M hM)

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Genuine coefficient Koszul homology cannot occur above the actual projective dimension. -/
lemma familyCoefficient_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply tensorCoefficient_nonzero_le_projectiveDimension
    (koszulComplex (Fintype.linearCombination (MvPolynomial V k) MvPolynomial.X))
    (fun i => by
      change Module.Flat (MvPolynomial V k) (⋀[MvPolynomial V k]^i (V → MvPolynomial V k))
      infer_instance) ?_ M n h
  intro i
  exact (koszulComplex.exactAt_of_isRegular
    (finiteVariableList (V := V) (k := k)) finite_variables_regular (i + 1) (by omega)).of_iso
    finiteVariableKoszulIso

/-- The same bound for Mathlib's actual first-factor derived Tor module. -/
lemma finitePolynomialTor_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero (finitePolynomialTor n M)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply familyCoefficient_nonzero_le_projectiveDimension M n
  exact fun hz => h ((finitePolynomialTorIso n M).isZero_iff.mpr hz)

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.DerivedDecomposition -/
section

/-! # Every genuine derived Tor class is a finite sum of multigraded classes -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- A canonical component of a derived Tor element, regarded as a member of its true degree submodule. -/
def derivedComponent (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))))
    (a : Exponent V) : gradedTor (k := k) B a i :=
  ⟨toDerivedTor (k := k) B a i
    (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i
      ((coefficientTorIso (k := k) B i).hom x)), ⟨_, rfl⟩⟩

/-- Completeness of the multigrading: every actual derived Tor class is a finite sum of its components. -/
lemma derivedTor_decomposition (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :
    ∃ s : Finset (Exponent V), ∑ a ∈ s, (derivedComponent (k := k) B i x a).val = x := by
  obtain ⟨s, hs⟩ := homogeneous_homology_decomposition (k := k) B i
    ((coefficientTorIso (k := k) B i).hom x)
  refine ⟨s, ?_⟩
  apply (coefficientTorIso (k := k) B i).toLinearEquiv.injective
  change (coefficientTorIso (k := k) B i).hom _ = _
  rw [map_sum]
  calc
    ∑ a ∈ s, (coefficientTorIso (k := k) B i).hom
        (derivedComponent (k := k) B i x a).val =
      ∑ a ∈ s, HomologicalComplex.homologyMap
        (homogeneousProjector (k := k) B a) i ((coefficientTorIso (k := k) B i).hom x) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [derivedComponent, toDerivedTor, ModuleCat.comp_apply,
        ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
        homogeneousProjector, HomologicalComplex.homologyMap_comp, Category.assoc,
        Iso.inv_hom_id_assoc, Category.comp_id]
    _ = _ := hs

/-- The actual degree submodules span all of derived Tor. -/
lemma iSup_gradedTor (B : Family V) (i : ℕ) :
    (⨆ a : Exponent V, gradedTor (k := k) B a i) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
  rw [← hs]
  apply Submodule.sum_mem
  intro a ha
  exact (le_iSup (fun a : Exponent V => gradedTor (k := k) B a i) a)
    (derivedComponent (k := k) B i x a).property

/-- Nonzero derived Tor has some nonzero multidegree, and conversely. -/
lemma derivedTor_nonzero_iff (B : Family V) (i : ℕ) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ↔
      ∃ a, GradedBettiNonzero (k := k) B a i := by
  constructor
  · contrapose!
    intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    have hx : x = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i x a) 0)
    have hy : y = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i y
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i y a) 0)
    exact hx.trans hy.symm
  · rintro ⟨a, ha⟩
    exact derivedTor_nonzero_of_graded (k := k) B a i ha

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: FourPapers.Common.HomogeneousCycleDetection -/
section

/-! # Detecting a nonzero homogeneous class among cycle generators

The assertions concern literal boundary ranges. Projection to the required
degree converts an arbitrary filling into a homogeneous filling, and therefore
detects a nonboundary generator in the same degree as the original class.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.BasisHomology
open Classical CommAlg

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (b : Module.Basis I R M) (degree : I → ℕ) (D : Module.End R M)
  (hlower : ∀ i, D (b i) ∈ Grading.Piece b degree (degree i - 1))
  (hzero : ∀ i, degree i = 0 → D (b i) = 0)

include hlower hzero

theorem differential_projection (p : ℕ) :
    D.comp (Grading.projection b degree (p + 1)) =
      (Grading.projection b degree p).comp D := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, Grading.projection_basis]
  by_cases hi : degree i = p + 1
  · rw [if_pos hi]
    exact (Grading.projection_eq_self
      (by simpa only [hi, Nat.add_sub_cancel] using hlower i)).symm
  · rw [if_neg hi, map_zero]
    by_cases h0 : degree i = 0
    · rw [hzero i h0, map_zero]
    · exact (Grading.projection_eq_zero (by omega) (hlower i)).symm

theorem homogeneous_filling (p : ℕ) (z : M)
    (hz : z ∈ Grading.Piece b degree p) (hb : z ∈ LinearMap.range D) :
    ∃ y, y ∈ Grading.Piece b degree (p + 1) ∧ D y = z := by
  obtain ⟨y, rfl⟩ := hb
  refine ⟨Grading.projection b degree (p + 1) y,
    Grading.projection_mem _ _ _ _, ?_⟩
  have he := LinearMap.congr_fun
    (differential_projection b degree D hlower hzero p) y
  exact he.trans (Grading.projection_eq_self hz)

theorem exists_homogeneous_nonboundary (s : Set M)
    (hs : ∀ x ∈ s, ∃ q, x ∈ Grading.Piece b degree q)
    (hspan : LinearMap.ker D ≤ Submodule.span R s ⊔ LinearMap.range D)
    (p : ℕ) (z : M) (hz : z ∈ Grading.Piece b degree p)
    (hcycle : D z = 0) (hboundary : z ∉ LinearMap.range D) :
    ∃ x ∈ s, x ∈ Grading.Piece b degree p ∧ x ∉ LinearMap.range D := by
  let π := Grading.projection b degree p
  let S := (LinearMap.range D).comap π
  have hrange : LinearMap.range D ≤ S := by
    rintro x ⟨y, rfl⟩
    exact ⟨Grading.projection b degree (p + 1) y,
      LinearMap.congr_fun (differential_projection b degree D hlower hzero p) y⟩
  have hzS : z ∉ S := by
    change π z ∉ LinearMap.range D
    simpa only [π, Grading.projection_eq_self hz] using hboundary
  have hex : ∃ x ∈ s, x ∉ S := by
    by_contra h
    push_neg at h
    have hle : Submodule.span R s ⊔ LinearMap.range D ≤ S :=
      sup_le (Submodule.span_le.mpr h) hrange
    exact hzS (hle (hspan hcycle))
  obtain ⟨x, hx, hxS⟩ := hex
  obtain ⟨q, hq⟩ := hs x hx
  have hpq : p = q := by
    by_contra h
    apply hxS
    change π x ∈ LinearMap.range D
    rw [show π x = 0 from Grading.projection_eq_zero h hq]
    exact Submodule.zero_mem _
  exact ⟨x, hx, by simpa only [hpq] using hq, fun h => hxS (hrange h)⟩

end FourPapers.BasisHomology

#print axioms FourPapers.BasisHomology.exists_homogeneous_nonboundary

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialZeroBetti -/
section

/-! # Degree-zero Tor of an equigenerated monomial ideal

A nonzero degree-zero class has the degree of a minimal monomial generator.
The proof supplies a one-vertex filling whenever a generator properly divides
the proposed multidegree; it does not assume a minimal-resolution theorem.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem monomial_zero_betti_degree (B : Family V) (d : ℕ)
    (hB : ∀ b ∈ B, b.degree = d) (α : Exponent V)
    (hβ : bettiNumber (k := k) B α 0 ≠ 0) : α.degree = d := by
  have hn : ¬Simplicial.ExactIn (k := k) (koszulFaces B α) 0 :=
    (Simplicial.nonzeroHomology_iff_not_exactIn _ _).mp
      ((bettiNumber_pos_iff_faces B α 0).mp (Nat.pos_of_ne_zero hβ))
  have hcontains : Contains B α := by
    by_contra h
    apply hn
    apply Simplicial.exactIn_of_no_face
    intro F hF _
    obtain ⟨b, hb, hble⟩ := hF.2
    exact h ⟨b, hb, hble.trans tsub_le_self⟩
  obtain ⟨b, hb, hble⟩ := hcontains
  by_cases he : b = α
  · simpa only [he] using hB b hb
  · have hgap : ∃ e, b e < α e := by
      by_contra h
      push_neg at h
      exact he (le_antisymm hble h)
    obtain ⟨e, he⟩ := hgap
    apply False.elim
    apply hn
    apply Simplicial.exactIn_zero_of_vertex e
    refine ⟨?_, b, hb, ?_⟩
    · intro v
      by_cases hv : v = e
      · subst v
        simp only [faceExponent_apply, Finset.mem_singleton, if_pos rfl, ite_true]
        omega
      · simp only [faceExponent_apply, Finset.mem_singleton, if_neg hv]
        exact Nat.zero_le _
    · intro v
      by_cases hv : v = e
      · subst v
        simp only [Finsupp.tsub_apply, faceExponent_apply,
          Finset.mem_singleton, if_pos rfl, ite_true]
        omega
      · simpa only [Finsupp.tsub_apply, faceExponent_apply,
          Finset.mem_singleton, if_neg hv, tsub_zero] using hble v

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.monomial_zero_betti_degree

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CentralFilterProducts -/
section

/-! # Removing central factors and counting positive degrees

These elementary lemmas preserve the order of the retained factors. They need
no commutativity among those factors, which is essential for Koszul homology.
-/

section
set_option autoImplicit false
namespace FourPapers
open Classical

theorem prod_filter_central {I A : Type*} [Monoid A]
    (xs : List I) (f : I → A) (P : I → Prop)
    (hc : ∀ a ∈ xs, ¬P a → ∀ b : A, Commute (f a) b) :
    (xs.map f).prod =
      ((xs.filter (fun a => decide (P a))).map f).prod *
        ((xs.filter (fun a => decide (¬P a))).map f).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have htail : ∀ a ∈ xs, ¬P a → ∀ b : A, Commute (f a) b :=
        fun x hx => hc x (List.mem_cons_of_mem a hx)
      by_cases ha : P a
      · simpa only [List.map_cons, List.prod_cons, List.filter_cons,
          decide_eq_true ha, decide_eq_false (not_not.mpr ha), Bool.true_eq,
          if_true, Bool.false_eq_true, if_false, mul_assoc] using
          congrArg (fun z => f a * z) (ih htail)
      · simp only [List.map_cons, List.prod_cons, List.filter_cons,
          decide_eq_false ha, decide_eq_true ha, Bool.true_eq,
          if_true, Bool.false_eq_true, if_false]
        rw [ih htail, ← mul_assoc,
          (hc a (List.mem_cons_self ..) ha _).eq, mul_assoc]

theorem prod_filter_ne_zero {I A : Type*} [MonoidWithZero A]
    (xs : List I) (f : I → A) (P : I → Prop)
    (hc : ∀ a ∈ xs, ¬P a → ∀ b : A, Commute (f a) b)
    (h : (xs.map f).prod ≠ 0) :
    ((xs.filter (fun a => decide (P a))).map f).prod ≠ 0 := by
  intro hz
  apply h
  rw [prod_filter_central xs f P hc, hz, zero_mul]

theorem positive_filter_length_le_sum {I : Type*} (xs : List I) (degree : I → ℕ) :
    (xs.filter (fun a => decide (degree a ≠ 0))).length ≤ (xs.map degree).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      by_cases ha : degree a = 0
      · simpa [ha] using ih
      · have hp : 0 < degree a := Nat.pos_of_ne_zero ha
        have hh : (xs.filter (fun i => decide (degree i ≠ 0))).length + 1 ≤
            degree a + (xs.map degree).sum := by omega
        simpa [ha] using hh

theorem positive_filter_length_pos {I : Type*} (xs : List I) (degree : I → ℕ)
    (h : 0 < (xs.map degree).sum) :
    0 < (xs.filter (fun a => decide (degree a ≠ 0))).length := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      by_cases ha : degree a = 0
      · simp only [List.map_cons, List.sum_cons, ha, zero_add] at h
        simpa [ha] using ih h
      · simp [ha]

theorem positive_filter_sum {I : Type*} (xs : List I) (degree : I → ℕ) :
    ((xs.filter (fun a => decide (degree a ≠ 0))).map degree).sum =
      (xs.map degree).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      by_cases ha : degree a = 0 <;> simpa [ha] using ih

theorem sum_map_eq_length_mul {I : Type*} (xs : List I) (f : I → ℕ) (c : ℕ)
    (h : ∀ a ∈ xs, f a = c) : (xs.map f).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
        ih (fun b hb => h b (List.mem_cons_of_mem a hb)), List.length_cons, Nat.succ_mul]
      omega

end FourPapers

#print axioms FourPapers.prod_filter_ne_zero
#print axioms FourPapers.positive_filter_length_le_sum

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BottomMultichain -/
section

/-!
# Prepending the minimum of the lattice

These are the literal index and coefficient-ideal identities used for
multiplication by the minimum generator in Corollary 5.3.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped BigOperators

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (μ : E) (hμ : ∀ a : E, μ.val ≤ a.val)

include hμ in
lemma minimum_predecessorFamily_eq_empty : finitePredecessorFamily n E μ.val = ∅ := by
  have hp : finitePrefix n E μ.val = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, r, hr, _⟩ := Finset.mem_filter.mp ha
    exact (not_lt_of_ge (hμ ⟨a, ha⟩ r)) hr
  simp only [finitePredecessorFamily, hp, Finset.image_empty]

/-- Insert the actual minimum as the first factor of a multichain. -/
def bottomPrepend {m : ℕ} (w : FiniteMultichain n E m) :
    FiniteMultichain n E (m + 1) := by
  refine ⟨Fin.cons μ w.val, ?_⟩
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact le_refl _
      | succ j => exact hμ (w.val j)
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          have hh : i.val + 1 ≤ 0 := hij
          omega
      | succ j => exact w.property (Fin.succ_le_succ_iff.mp hij)

@[simp] lemma bottomPrepend_zero {m : ℕ} (w : FiniteMultichain n E m) :
    (bottomPrepend μ hμ w).val 0 = μ := rfl

@[simp] lemma bottomPrepend_succ {m : ℕ} (w : FiniteMultichain n E m) (j : Fin m) :
    (bottomPrepend μ hμ w).val j.succ = w.val j := rfl

lemma bottomPrepend_injective (m : ℕ) :
    Function.Injective (bottomPrepend μ hμ : FiniteMultichain n E m → _) := by
  intro w z h
  apply Subtype.ext
  funext j
  have he := congrArg (fun a : FiniteMultichain n E (m + 1) => a.val j.succ) h
  exact he

@[simp] lemma bottomPrepend_shift {m : ℕ} (w : FiniteMultichain n E m) :
    finiteChainShift n (bottomPrepend μ hμ w) =
      finiteRowExponent n μ.val + finiteChainShift n w := by
  simp only [finiteChainShift, Fin.sum_univ_succ, bottomPrepend_zero, bottomPrepend_succ]

@[simp] lemma bottomPrepend_coefficientFamily {m : ℕ} (w : FiniteMultichain n E m) :
    finiteChainCoefficientFamily n (bottomPrepend μ hμ w) =
      finiteChainCoefficientFamily n w := by
  apply Finset.ext
  intro a
  simp only [finiteChainCoefficientFamily, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Fin.exists_fin_succ, bottomPrepend_zero, bottomPrepend_succ,
    minimum_predecessorFamily_eq_empty μ hμ, Finset.notMem_empty, false_or]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BottomChainGeometry -/
section

/-! # Literal coefficient blocks under multiplication by the minimum generator -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (μ : E) (hμ : ∀ a : E, μ.val ≤ a.val)

/-- The coefficient monomial is unchanged; the normal multichain gains
one copy of the actual minimum. -/
def bottomChainIndex {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) :
    FiniteChainStandardIndex.{u} n E (m+1) :=
  ⟨bottomPrepend μ hμ a.1, a.2.val, by
    rw [bottomPrepend_coefficientFamily]
    exact a.2.property⟩

@[simp] theorem bottomChainIndex_exponent {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) :
    finiteChainIndexExponent (bottomChainIndex μ hμ a) =
      finiteRowExponent n μ.val + finiteChainIndexExponent a := by
  change a.2.val + finiteChainShift n (bottomPrepend μ hμ a.1) = _
  rw [bottomPrepend_shift]
  change a.2.val + (finiteRowExponent n μ.val + finiteChainShift n a.1) =
    finiteRowExponent n μ.val + (a.2.val + finiteChainShift n a.1)
  abel

def bottomAdmissibleChain {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (w : AdmissibleChain n E m α) :
    AdmissibleChain n E (m+1) (α + finiteRowExponent n μ.val) :=
  ⟨bottomPrepend μ hμ w.val, by
    rw [bottomPrepend_shift]
    exact (add_le_add (le_refl (finiteRowExponent n μ.val)) w.property).trans_eq
      (add_comm (finiteRowExponent n μ.val) α)⟩

@[simp] theorem bottom_residual {m : ℕ} (α : Exponent (FiniteVariable.{u} n))
    (w : FiniteMultichain n E m) :
    (α + finiteRowExponent n μ.val) - finiteChainShift n (bottomPrepend μ hμ w) =
      α - finiteChainShift n w := by
  rw [bottomPrepend_shift, add_comm α (finiteRowExponent n μ.val), add_tsub_add_eq_tsub_left]

/-- Every exterior face is retained exactly, with its coefficient quotient
and residual fine exponent identified by the proved minimum identities. -/
def bottomChainFace {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) :
    ChainFaceIndex n E (m+1) (α + finiteRowExponent n μ.val) :=
  ⟨bottomAdmissibleChain μ hμ a.1, a.2.val, by
    change quotientKoszulFaces (finiteChainCoefficientFamily n (bottomPrepend μ hμ a.1.val))
      ((α + finiteRowExponent n μ.val) - finiteChainShift n (bottomPrepend μ hμ a.1.val)) a.2.val
    rw [bottomPrepend_coefficientFamily, bottom_residual]
    exact a.2.property⟩

@[simp] theorem bottomChainFace_face {m : ℕ} {α : Exponent (FiniteVariable.{u} n)}
    (a : ChainFaceIndex n E m α) : (bottomChainFace μ hμ a).2.val = a.2.val := rfl

theorem bottomChainFace_injective (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) :
    Function.Injective (bottomChainFace μ hμ : ChainFaceIndex n E m α → _) := by
  intro a b h
  have hw : a.1.val = b.1.val := bottomPrepend_injective μ hμ m
    (congrArg (fun c : ChainFaceIndex n E (m+1) (α + finiteRowExponent n μ.val) => c.1.val) h)
  have hF : a.2.val = b.2.val := congrArg
    (fun c : ChainFaceIndex n E (m+1) (α + finiteRowExponent n μ.val) => c.2.val) h
  rcases a with ⟨⟨w, hw'⟩, ⟨F, hF'⟩⟩
  rcases b with ⟨⟨z, hz⟩, ⟨G, hG⟩⟩
  dsimp only at hw hF
  subst z
  subst G
  rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisIndexRetraction -/
section

/-! # An actual basis inclusion and its coordinate retraction -/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.BasisIndexRetraction

open Classical

variable {K X Y I J : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  (b : Module.Basis I K X) (c : Module.Basis J K Y)
  (ι : I → J) (hι : Function.Injective ι)

def inclusion : X →ₗ[K] Y :=
  c.repr.symm.toLinearMap.comp ((Finsupp.lmapDomain K K ι).comp b.repr.toLinearMap)

def retraction : Y →ₗ[K] X :=
  b.repr.symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (R := K) (M := K) ι hι).comp c.repr.toLinearMap)

@[simp] theorem inclusion_basis (i : I) : inclusion b c ι (b i) = c (ι i) := by
  simp only [inclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Module.Basis.repr_symm_single, one_smul]

@[simp] theorem retraction_coefficient (y : Y) (i : I) :
    b.repr (retraction b c ι hι y) i = c.repr y (ι i) := by
  simp only [retraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]

@[simp] theorem retraction_inclusion (x : X) :
    retraction b c ι hι (inclusion b c ι x) = x := by
  apply b.repr.injective
  simp only [retraction, inclusion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := K) (M := K) ι hι (b.repr x)

@[simp] theorem retraction_basis_image (i : I) : retraction b c ι hι (c (ι i)) = b i := by
  rw [← inclusion_basis b c ι i, retraction_inclusion]

theorem retraction_basis_outside (j : J) (hj : j ∉ Set.range ι) :
    retraction b c ι hι (c j) = 0 := by
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  rw [retraction_coefficient, Module.Basis.repr_self, map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  exact fun h => hj ⟨i, h⟩

theorem inclusion_preserves (w : I → ℕ) (v : J → ℕ)
    (hw : ∀ i, v (ι i) = w i) :
    FilteredHomology.Preserves (Universal.basisFiltration b w)
      (Universal.basisFiltration c v) (inclusion b c ι) := by
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [inclusion_basis]
      exact Submodule.subset_span ⟨ι i, by simpa only [Set.mem_setOf_eq, hw] using hi, rfl⟩
  | zero => simpa only [map_zero] using ((Universal.basisFiltration c v).level n).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem retraction_preserves (w : I → ℕ) (v : J → ℕ)
    (hw : ∀ i, v (ι i) = w i) :
    FilteredHomology.Preserves (Universal.basisFiltration c v)
      (Universal.basisFiltration b w) (retraction b c ι hι) := by
  intro n y hy
  rw [Universal.basisFiltration_mem] at hy ⊢
  intro i hi
  rw [retraction_coefficient]
  exact hy (ι i) (by simpa only [hw] using hi)

end FourPapers.BasisIndexRetraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WeightedMatrixHomogenization -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.WeightedMatrix
open Classical Polynomial
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
variable (w : ι → ℕ)

/-- A matrix preserves the increasing filtration given by `w`. -/
def NonIncreasing (A : Matrix ι ι R) : Prop :=
  ∀ i j, w j < w i → A i j = 0

/-- Literal integer-weight homogenization. The exponent records the drop of
filtration weight from the source basis vector to the target basis vector. -/
def homogenize (A : Matrix ι ι R) : Matrix ι ι R[X] :=
  fun i j => C (A i j) * X ^ (w j - w i)

@[simp] lemma homogenize_zero : homogenize w (0 : Matrix ι ι R) = 0 := by
  ext i j
  simp [homogenize]

@[simp] lemma homogenize_add (A B : Matrix ι ι R) :
    homogenize w (A+B) = homogenize w A + homogenize w B := by
  ext i j
  simp [homogenize,add_mul]

@[simp] lemma homogenize_one : homogenize w (1 : Matrix ι ι R) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [homogenize,Matrix.one_apply]
  · simp [homogenize,Matrix.one_apply,h]

lemma nonIncreasing_mul (A B : Matrix ι ι R) (hA : NonIncreasing w A) (hB : NonIncreasing w B) :
    NonIncreasing w (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases hia : w a < w i
  · rw [hA i a hia,zero_mul]
  · have haj : w j < w a := by omega
    rw [hB a j haj,mul_zero]

lemma homogenize_mul (A B : Matrix ι ι R) (hA : NonIncreasing w A) (hB : NonIncreasing w B) :
    homogenize w (A*B) = homogenize w A * homogenize w B := by
  apply Matrix.ext
  intro i j
  simp only [homogenize,Matrix.mul_apply,map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hA0 : A i a = 0
  · simp [hA0]
  by_cases hB0 : B a j = 0
  · simp [hB0]
  have hia : w i ≤ w a := by
    by_contra! h
    exact hA0 (hA i a h)
  have haj : w a ≤ w j := by
    by_contra! h
    exact hB0 (hB a j h)
  have hpow : w a - w i + (w j - w a) = w j - w i := by omega
  rw [map_mul]
  calc
    C (A i a) * C (B a j) * X ^ (w j - w i) =
      C (A i a) * C (B a j) * (X ^ (w a-w i) * X ^ (w j-w a)) := by rw [←pow_add,hpow]
    _ = (C (A i a) * X ^ (w a-w i)) * (C (B a j) * X ^ (w j-w a)) := by ring

/-- The original differential relation survives literal homogenization. -/
theorem homogenize_chain_relation (D E F : Matrix ι ι R)
    (hD : NonIncreasing w D) (hE : NonIncreasing w E) (hF : NonIncreasing w F)
    (h : D*F = F*E) :
    homogenize w D * homogenize w F = homogenize w F * homogenize w E := by
  rw [←homogenize_mul w D F hD hF,←homogenize_mul w F E hF hE,h]

lemma homogenize_square_zero (D : Matrix ι ι R) (hD : NonIncreasing w D) (h : D*D = 0) :
    homogenize w D * homogenize w D = 0 := by
  rw [←homogenize_mul w D D hD hD,h,homogenize_zero]

@[simp] lemma homogenize_at_one (A : Matrix ι ι R) (i j : ι) :
    (homogenize w A i j).eval 1 = A i j := by
  simp [homogenize]

lemma homogenize_weight_preserving (A : Matrix ι ι R)
    (h : ∀ i j, w i ≠ w j → A i j = 0) :
    homogenize w A = A.map C := by
  ext i j
  by_cases hij : w i = w j
  · simp [homogenize,hij]
  · simp [homogenize,h i j hij]

/-- A matrix equal to the identity in every nondecreasing-weight position has
identity special fiber after homogenization. No determinant or field hypothesis
is used. -/
theorem homogenize_unitriangular_at_zero (A : Matrix ι ι R)
    (h : ∀ i j, w j ≤ w i → A i j = if i = j then 1 else 0) (i j : ι) :
    (homogenize w A i j).eval 0 = (1 : Matrix ι ι R) i j := by
  by_cases hij : i = j
  · subst j
    simp [homogenize,h i i le_rfl,Matrix.one_apply]
  · by_cases hw : w j ≤ w i
    · simp [homogenize,h i j hw,hij,Matrix.one_apply]
    · have hpos : 0 < w j-w i := Nat.sub_pos_of_lt (lt_of_not_ge hw)
      simp [homogenize,zero_pow (Nat.ne_of_gt hpos),Matrix.one_apply,hij]


lemma strict_pow_eq_zero (N : Matrix ι ι R)
    (hN : ∀ i j, w j ≤ w i → N i j = 0) (n : ℕ) (i j : ι)
    (hij : w j < w i+n) : (N^n) i j = 0 := by
  induction n generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp [Matrix.one_apply,hne]
  | succ n ih =>
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hja : w j ≤ w a
    · rw [hN a j hja,mul_zero]
    · have ha : w a < w i+n := by omega
      rw [ih i a ha,zero_mul]

lemma strict_isNilpotent (N : Matrix ι ι R)
    (hN : ∀ i j, w j ≤ w i → N i j = 0) : IsNilpotent N := by
  refine ⟨(∑ i, w i)+1, ?_⟩
  ext i j
  apply strict_pow_eq_zero w N hN
  have hj : w j ≤ ∑ i, w i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

/-- The homogenized change of basis is invertible over the polynomial ring
itself, including over coefficient rings with zero divisors. -/
theorem homogenize_isUnit (A : Matrix ι ι R)
    (h : ∀ i j, w j ≤ w i → A i j = if i = j then 1 else 0) :
    IsUnit (homogenize w A) := by
  have hN : ∀ i j, w j ≤ w i → (homogenize w A - 1) i j = 0 := by
    intro i j hij
    simp [homogenize,Matrix.one_apply,h i j hij,Nat.sub_eq_zero_of_le hij]
  have hunit := (strict_isNilpotent w (homogenize w A-1) hN).isUnit_one_add
  simpa only [←add_sub_assoc,add_sub_cancel_left] using hunit

/-- A full polynomial-parameter chain conjugacy. This is stronger than
quasi-isomorphism: the change of basis is an actual matrix unit and its two
endpoint specializations are controlled by the preceding lemmas. -/
theorem homogenized_chain_isomorphism (D E F : Matrix ι ι R)
    (hD : NonIncreasing w D) (hE : NonIncreasing w E)
    (hF : ∀ i j, w j ≤ w i → F i j = if i = j then 1 else 0)
    (hchain : D*F = F*E) :
    IsUnit (homogenize w F) ∧
      homogenize w D * homogenize w F = homogenize w F * homogenize w E := by
  refine ⟨homogenize_isUnit w F hF,homogenize_chain_relation w D E F hD hE ?_ hchain⟩
  intro i j hij
  have hne : i ≠ j := by intro h; subst j; omega
  simpa only [if_neg hne] using hF i j (le_of_lt hij)

end FourPapers.WeightedMatrix

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WellOrderedHomologyInjection -/
section

/-! # Injectivity of literal multiplication under a well-ordered degeneration

The map here is multiplication by the given cycle itself. Its leading symbol
acts on the actual associated Koszul homology. Cycle lifting makes boundaries
strict; well-founded descent then reflects boundaries of this particular map.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.WellOrderedFiltered.MultiplicativeFiltration

open Classical

private theorem algMap_sub
    {R X Y : Type*} [CommRing R] [Ring X] [Ring Y] [Algebra R X] [Algebra R Y]
    (f : X →ₐ[R] Y) (x y : X) : f (x-y)=f x-f y := map_sub f x y

private theorem algMap_mul
    {R X Y : Type*} [CommRing R] [Ring X] [Ring Y] [Algebra R X] [Algebra R Y]
    (f : X →ₐ[R] Y) (x y : X) : f (x*y)=f x*f y := map_mul f x y

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [WellFoundedLT Γ]
  (F : MultiplicativeFiltration K A Γ) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

include hd in
/-- Cycle lifting implies strictness of the actual boundary differential. -/
theorem boundary_strict_of_cycle_lifts (hlift : F.LiftsCycles D)
    (n : Γ) (x : A) (hx : D.d x ∈ F.level n) :
    ∃ y, y ∈ F.level n ∧ D.d y = D.d x := by
  have step : ∀ m (z : A), z ∈ F.level m → D.d z ∈ F.level n →
      ∃ y, y ∈ F.level n ∧ D.d y = D.d z := by
    intro m
    induction m using WellFoundedLT.induction with
    | ind m ih =>
      intro z hz hdz
      by_cases hmn : m ≤ n
      · exact ⟨z,F.mono hmn hz,rfl⟩
      · have hnm : n < m := lt_of_not_ge hmn
        obtain ⟨c,hc,hdc,hrest⟩ := hlift m z hz (Or.inr ⟨n,hnm,hdz⟩)
        have he : D.d (z-c) = D.d z := by rw [D.d.map_sub,hdc,sub_zero]
        rcases hrest with hzero | ⟨r,hr,hzr⟩
        · refine ⟨0,(F.level n).zero_mem,?_⟩
          rw [D.d.map_zero,← he,hzero,D.d.map_zero]
        · obtain ⟨y,hy,hey⟩ := ih r hr (z-c) hzr (he.symm ▸ hdz)
          exact ⟨y,hy,hey.trans he⟩
  obtain ⟨m,hm⟩ := F.exhaustive x
  exact step m x hm hx

theorem monomial_is_cycle (n : Γ) (x : F.level n) (hx : D.d x.val = 0) :
    (F.reesDGA D hd hp).d (F.monomial n x) = 0 := by
  apply Subtype.ext
  ext i
  rw [F.reesDGA_d_coeff,F.monomial_coeff]
  split_ifs
  · exact hx
  · exact D.d.map_zero

def symbolCycle (n : Γ) (x : F.level n) (hx : D.d x.val = 0) :
    (F.associatedDGA D hd hp).cycles :=
  ⟨F.leadingMap (F.monomial n x),by
    change (F.associatedDGA D hd hp).d (F.leadingMap (F.monomial n x))=0
    rw [F.leadingMap_intertwines,F.monomial_is_cycle D hd hp n x hx,
      map_zero F.leadingMap]⟩

def symbolHomologyClass (n : Γ) (x : F.level n) (hx : D.d x.val = 0) :
    (F.associatedDGA D hd hp).Homology :=
  (F.associatedDGA D hd hp).classMap (F.symbolCycle D hd hp n x hx)

/-- Vanishing of this actual leading class is equivalent to an actual
boundary approximation in the same filtration level. -/
theorem symbolHomologyClass_eq_zero_iff (n : Γ) (x : F.level n)
    (hx : D.d x.val = 0) :
    F.symbolHomologyClass D hd hp n x hx = 0 ↔
      ∃ y, y ∈ F.level n ∧ x.val - D.d y ∈ F.lower n := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := ((F.associatedDGA D hd hp).classMap_eq_zero _).mp h
    obtain ⟨q,rfl⟩ := F.leadingMap_surjective q
    change (F.associatedDGA D hd hp).d (F.leadingMap q)=F.leadingMap (F.monomial n x) at hq
    have he : F.leadingMap (F.monomial n x - (F.reesDGA D hd hp).d q) = 0 := by
      rw [algMap_sub F.leadingMap,← F.leadingMap_intertwines]
      change F.leadingMap (F.monomial n x) -
        (F.associatedDGA D hd hp).d (F.leadingMap q) = 0
      rw [hq,sub_self]
    refine ⟨q.val.coeff n,q.property n,?_⟩
    have hh := (F.leadingMap_eq_zero _).mp he n
    change (F.monomial n x).val.coeff n - D.d (q.val.coeff n) ∈ F.lower n at hh
    simpa only [F.monomial_coeff,if_pos rfl,ite_true] using hh
  · rintro ⟨y,hy,hrest⟩
    apply ((F.associatedDGA D hd hp).classMap_eq_zero _).mpr
    refine ⟨F.leadingMap (F.monomial n ⟨y,hy⟩),?_⟩
    change (F.associatedDGA D hd hp).d (F.leadingMap (F.monomial n ⟨y,hy⟩))=
      F.leadingMap (F.monomial n x)
    rw [F.leadingMap_intertwines]
    apply sub_eq_zero.mp
    rw [← algMap_sub F.leadingMap,F.leadingMap_eq_zero]
    intro i
    change D.d ((F.monomial n ⟨y,hy⟩).val.coeff i) -
      (F.monomial n x).val.coeff i ∈ F.lower i
    rw [F.monomial_coeff,F.monomial_coeff]
    split_ifs with hi
    · subst i
      simpa only [neg_sub] using (F.lower n).neg_mem hrest
    · rw [D.d.map_zero,sub_zero]
      exact (F.lower i).zero_mem

theorem symbolHomologyClass_mul (a n : Γ) (f : F.level a) (x : F.level n)
    (hf : D.d f.val = 0) (hx : D.d x.val = 0) :
    F.symbolHomologyClass D hd hp a f hf * F.symbolHomologyClass D hd hp n x hx =
      F.symbolHomologyClass D hd hp (a+n)
        ⟨f.val*x.val,F.mul_mem a n _ f.property _ x.property⟩
        (by rw [D.leibniz,hf,hx,zero_mul,mul_zero,add_zero]) := by
  unfold symbolHomologyClass
  rw [← algMap_mul ((F.associatedDGA D hd hp).classMap)]
  apply congrArg (F.associatedDGA D hd hp).classMap
  apply Subtype.ext
  change F.leadingMap (F.monomial a f) * F.leadingMap (F.monomial n x) = _
  rw [← algMap_mul F.leadingMap]
  apply congrArg F.leadingMap
  apply Subtype.ext
  exact AddMonoidAlgebra.single_mul_single a n f.val x.val

include hd hp in
/-- Literal multiplication by an even cycle reflects actual boundaries if
its leading symbol is injective on associated homology. -/
theorem mul_reflects_boundaries_of_special
    (hlift : F.LiftsCycles D) (a : Γ) (f : F.level a)
    (hf : D.d f.val = 0) (hpf : D.parity f.val = f.val)
    (hinj : Function.Injective
      (fun z : (F.associatedDGA D hd hp).Homology =>
        F.symbolHomologyClass D hd hp a f hf * z))
    (x : A) (hx : D.d x = 0) (hfx : ∃ w, D.d w = f.val*x) :
    ∃ y, D.d y = x := by
  have step : ∀ n (z : A), z ∈ F.level n → D.d z = 0 →
      (∃ w, D.d w = f.val*z) → ∃ y, D.d y = z := by
    intro n
    induction n using WellFoundedLT.induction with
    | ind n ih =>
      intro z hz hdz hboundary
      obtain ⟨w,hw⟩ := hboundary
      obtain ⟨w',hw',hew⟩ := F.boundary_strict_of_cycle_lifts D hd hlift (a+n) w
        (hw.symm ▸ F.mul_mem a n _ f.property z hz)
      have hclass : F.symbolHomologyClass D hd hp n ⟨z,hz⟩ hdz = 0 := by
        apply hinj
        change F.symbolHomologyClass D hd hp a f hf *
          F.symbolHomologyClass D hd hp n ⟨z,hz⟩ hdz =
          F.symbolHomologyClass D hd hp a f hf * 0
        rw [mul_zero,F.symbolHomologyClass_mul D hd hp a n f ⟨z,hz⟩ hf hdz]
        apply (F.symbolHomologyClass_eq_zero_iff D hd hp _ _ _).mpr
        refine ⟨w',hw',?_⟩
        rw [hew,hw,sub_self]
        exact (F.lower (a+n)).zero_mem
      obtain ⟨v,hv,hrest⟩ :=
        (F.symbolHomologyClass_eq_zero_iff D hd hp n ⟨z,hz⟩ hdz).mp hclass
      have hdrest : D.d (z-D.d v) = 0 := by
        rw [D.d.map_sub,hdz,D.square_zero,sub_self]
      have hbrest : ∃ w, D.d w = f.val*(z-D.d v) := by
        refine ⟨w-f.val*v,?_⟩
        rw [D.d.map_sub,D.leibniz,hf,hpf,zero_mul,zero_add,hw,mul_sub]
      rcases hrest with hzero | ⟨r,hr,hzr⟩
      · exact ⟨v,(sub_eq_zero.mp hzero).symm⟩
      · obtain ⟨v',hv'⟩ := ih r hr (z-D.d v) hzr hdrest hbrest
        refine ⟨v+v',?_⟩
        rw [D.d.map_add,hv']
        abel
  obtain ⟨n,hn⟩ := F.exhaustive x
  exact step n x hn hx hfx

/-- This is injectivity of multiplication by the specified homology class,
not an abstract injection inferred from a dimension inequality. -/
theorem mul_homology_injective_of_special
    (hlift : F.LiftsCycles D) (a : Γ) (f : F.level a)
    (hf : D.d f.val = 0) (hpf : D.parity f.val = f.val)
    (hinj : Function.Injective
      (fun z : (F.associatedDGA D hd hp).Homology =>
        F.symbolHomologyClass D hd hp a f hf * z)) :
    Function.Injective (fun z : D.Homology => D.classMap ⟨f.val,(D.mem_cycles f.val).mpr hf⟩ * z) := by
  have zero_kernel : ∀ z : D.Homology, D.classMap ⟨f.val,(D.mem_cycles f.val).mpr hf⟩ * z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x,rfl⟩ := D.classMap_surjective z
    have hproduct : D.classMap (⟨f.val,(D.mem_cycles f.val).mpr hf⟩ * x) = 0 := by
      rw [algMap_mul D.classMap]
      exact hz
    apply (D.classMap_eq_zero x).mpr
    exact F.mul_reflects_boundaries_of_special D hd hp hlift a f hf hpf hinj
      x.val x.property ((D.classMap_eq_zero _).mp hproduct)
  intro x y hxy
  change D.classMap ⟨f.val,(D.mem_cycles f.val).mpr hf⟩*x=
    D.classMap ⟨f.val,(D.mem_cycles f.val).mpr hf⟩*y at hxy
  apply sub_eq_zero.mp
  apply zero_kernel
  rw [mul_sub,hxy,sub_self]

end FourPapers.WellOrderedFiltered.MultiplicativeFiltration

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedBasisHomologyInjection -/
section

/-! # Injection for a specified basis generator in an ordered degeneration -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.OrderedBasis
open Classical
variable {K A B I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [Ring B] [Algebra K B] [AddCancelCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [WellFoundedLT Γ]
  (b : Module.Basis I K A) (c : Module.Basis I K B) (w : I → Γ)
  (hcprod : ∀ i j k, c.repr (c i*c j) k ≠ 0 → w k=w i+w j)
  (hlead : ∀ i j k, w i+w j≤w k → b.repr (b i*b j) k=c.repr (c i*c j) k)
  (h1 : ∀ i, b.repr (1:A) i ≠ 0 → w i≤0)
  (hone : leadingProjection b c w 0 1=1)
  (D : ParityDifferential K A) (E : ParityDifferential K B)
  (hdhom : ∀ i j, c.repr (E.d (c i)) j ≠ 0 → w j=w i)
  (hdlead : ∀ i j, w i≤w j → b.repr (D.d (b i)) j=c.repr (E.d (c i)) j)
  (hphom : ∀ i j, c.repr (E.parity (c i)) j ≠ 0 → w j=w i)
  (hplead : ∀ i j, w i≤w j → b.repr (D.parity (b i)) j=c.repr (E.parity (c i)) j)

local notation "F" => comparisonFiltration b c w hcprod hlead h1
local notation "hd" => differential_preserves b c w hcprod hlead h1 D E hdhom hdlead
local notation "hp" => parity_preserves b c w hcprod hlead h1 D E hphom hplead
local notation "e" => associatedHomologyEquiv b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead

theorem associatedHomologyEquiv_basis_symbol (i : I)
    (hi : D.d (b i)=0) (hci : E.d (c i)=0) :
    e ((F).symbolHomologyClass D hd hp (w i) ⟨b i,basis_mem_level b w i⟩ hi) =
      E.classMap ⟨c i,(E.mem_cycles (c i)).mpr hci⟩ := by
  rw [WellOrderedFiltered.MultiplicativeFiltration.symbolHomologyClass,
    associatedHomologyEquiv,ParityDifferential.homologyEquiv_classMap]
  apply congrArg E.classMap
  apply Subtype.ext
  have hi_level : b i ∈ (F).level (w i) := by
    change b i ∈ level b w (w i)
    exact basis_mem_level b w i
  let xi : (F).level (w i) := ⟨b i, hi_level⟩
  change associatedAlgebraEquiv b c w hcprod hlead h1 hone
    ((F).leadingMap ((F).monomial (w i) xi)) = c i
  have hs : specialization b c w hcprod hlead h1 hone
      ((F).monomial (w i) xi) = leadingProjection b c w (w i) (b i) := by
    exact specialization_monomial b c w hcprod hlead h1 hone (w i)
      (show level b w (w i) from xi)
  exact (associatedAlgebraEquiv_leading b c w hcprod hlead h1 hone
    ((F).monomial (w i) xi)).trans
      (hs.trans ((leadingProjection_basis b c w (w i) i).trans (if_pos rfl)))

/-- This evaluates the symbol of an arbitrary actual cycle, not merely a
basis vector. The specified leading projection is the only identification. -/
theorem associatedHomologyEquiv_symbol (n : Γ) (x : (F).level n)
    (hx : D.d x.val=0) (y : B) (hy : E.d y=0)
    (hleading : leadingProjection b c w n x.val=y) :
    e ((F).symbolHomologyClass D hd hp n x hx)=E.classMap ⟨y,(E.mem_cycles y).mpr hy⟩ := by
  rw [WellOrderedFiltered.MultiplicativeFiltration.symbolHomologyClass,
    associatedHomologyEquiv,ParityDifferential.homologyEquiv_classMap]
  apply congrArg E.classMap
  apply Subtype.ext
  change associatedAlgebraEquiv b c w hcprod hlead h1 hone
    ((F).leadingMap ((F).monomial n x))=y
  have hs : specialization b c w hcprod hlead h1 hone
      ((F).monomial n x) = leadingProjection b c w n x.val := by
    exact specialization_monomial b c w hcprod hlead h1 hone n
      (show level b w n from x)
  exact (associatedAlgebraEquiv_leading b c w hcprod hlead h1 hone
    ((F).monomial n x)).trans (hs.trans hleading)

include hone hdhom hdlead hphom hplead in
/-- Every chosen cycle with the stated genuine leading symbol acts
injectively. In particular this does not impose a canonical choice of lift. -/
theorem element_homology_mul_injective
    (hlift : (F).LiftsCycles D) (n : Γ) (x : (F).level n)
    (hx : D.d x.val=0) (hpx : D.parity x.val=x.val)
    (y : B) (hy : E.d y=0) (hleading : leadingProjection b c w n x.val=y)
    (hinj : Function.Injective (fun z : E.Homology => E.classMap ⟨y,(E.mem_cycles y).mpr hy⟩*z)) :
    Function.Injective (fun z : D.Homology => D.classMap ⟨x.val,(D.mem_cycles x.val).mpr hx⟩*z) := by
  apply (F).mul_homology_injective_of_special D hd hp hlift n x hx hpx
  intro a t hat
  apply (e).injective
  apply hinj
  have he := congrArg e hat
  rw [map_mul e,map_mul e,
    associatedHomologyEquiv_symbol b c w hcprod hlead h1 hone D E
      hdhom hdlead hphom hplead n x hx y hy hleading] at he
  exact he

/-- A one-dimensional leading basis support identifies the actual symbol. -/
theorem leadingProjection_eq_basis (i : I) (x : A)
    (hcoeff : b.repr x i=1)
    (hunique : ∀ j, b.repr x j ≠ 0 → w j = w i → j = i) :
    leadingProjection b c w (w i) x=c i := by
  apply c.repr.injective
  apply Finsupp.ext
  intro j
  rw [leadingProjection_repr,Module.Basis.repr_self,Finsupp.single_apply]
  by_cases hji : j=i
  · subst j
    rw [if_pos rfl,if_pos rfl,hcoeff]
  · rw [if_neg (Ne.symm hji)]
    split_ifs with hw
    · by_contra hc
      exact hji (hunique j hc hw)
    · rfl

include hone hdhom hdlead hphom hplead in
/-- An actual initial generator with injective multiplication gives
injective multiplication by its actual triangular lift. -/
theorem basis_homology_mul_injective
    (hlift : (F).LiftsCycles D) (i : I)
    (hi : D.d (b i)=0) (hpi : D.parity (b i)=b i) (hci : E.d (c i)=0)
    (hinj : Function.Injective (fun z : E.Homology => E.classMap ⟨c i,(E.mem_cycles (c i)).mpr hci⟩*z)) :
    Function.Injective (fun z : D.Homology => D.classMap ⟨b i,(D.mem_cycles (b i)).mpr hi⟩*z) := by
  apply (F).mul_homology_injective_of_special D hd hp hlift (w i)
    ⟨b i,basis_mem_level b w i⟩ hi hpi
  intro x y hxy
  apply (e).injective
  apply hinj
  have he := congrArg e hxy
  rw [map_mul e,map_mul e,
    associatedHomologyEquiv_basis_symbol b c w hcprod hlead h1 hone D E
      hdhom hdlead hphom hplead i hi hci] at he
  exact he

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulProjection -/
section

/-! # Literal exterior-coordinate projections from the total Koszul complex

Extracting faces of cardinality `p` gives the standard coordinate complex.
The projection commutes with the differential, including degree zero.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.TensorExteriorKoszul
open Classical CommAlg CommAlg.Koszul CategoryTheory
open scoped TensorProduct
universe u
variable {K R V M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype V] [LinearOrder V] [AddCommGroup M] [Module R M] [Module K M]
  [IsScalarTower K R M]

def projection (p : ℕ) : Total (K:=K) (V:=V) (M:=M) →ₗ[K]
    (Set.powersetCard V p →₀ M) :=
  (Finsupp.lsubtypeDomain {F : Finset V | F.card=p}).comp
    (coordinates (K:=K) (V:=V) (M:=M)).toLinearMap

@[simp] theorem projection_tmul_basis_apply (p : ℕ) (a : M)
    (F : Finset V) (H : Set.powersetCard V p) :
    projection (K:=K) p (a ⊗ₜ[K] Simplicial.basis F) H =
      if F=H.val then a else 0 := by
  change coordinates (a ⊗ₜ[K] Simplicial.basis F) H.val = _
  rw [coordinates_tmul_basis,Finsupp.single_apply]

theorem projection_tmul_basis (p : ℕ) (a : M) (F : Finset V) (hF : F.card=p) :
    projection (K:=K) p (a ⊗ₜ[K] Simplicial.basis F) = Finsupp.single ⟨F,hF⟩ a := by
  apply Finsupp.ext
  intro H
  rw [projection_tmul_basis_apply,Finsupp.single_apply]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem projection_tmul_basis_of_ne (p : ℕ) (a : M) (F : Finset V) (hF : F.card≠p) :
    projection (K:=K) p (a ⊗ₜ[K] Simplicial.basis F) = 0 := by
  apply Finsupp.ext
  intro H
  rw [projection_tmul_basis_apply,Finsupp.zero_apply,if_neg]
  exact fun h => hF (h ▸ H.property)

@[simp] theorem projection_lift (p : ℕ) (x : Set.powersetCard V p →₀ M) :
    projection (K:=K) p (lift p x)=x := by
  have he : (projection (K:=K) (V:=V) (M:=M) p).comp (lift p)=LinearMap.id := by
    apply Finsupp.lhom_ext
    intro F a
    rw [LinearMap.comp_apply,lift_single,projection_tmul_basis p a F.val F.property]
    rfl
  exact LinearMap.congr_fun he x

theorem projection_differential_tmul_basis (x : V → R) (p : ℕ) (a : M) (F : Finset V) :
    projection (K:=K) p (differential x (a ⊗ₜ[K] Simplicial.basis F)) =
      coordinateDifferential x (ModuleCat.of R M) p
        (projection (K:=K) (p+1) (a ⊗ₜ[K] Simplicial.basis F)) := by
  by_cases hF : F.card=p+1
  · rw [projection_tmul_basis (p+1) a F hF]
    rw [← lift_single (p+1) (⟨F,hF⟩ : Set.powersetCard V (p+1)) a,
      differential_lift,projection_lift]
  · rw [projection_tmul_basis_of_ne (p+1) a F hF,
      (coordinateDifferential x (ModuleCat.of R M) p).map_zero,differential_tmul,
      map_sum]
    apply Finset.sum_eq_zero
    intro v _
    rw [Simplicial.contraction_basis]
    by_cases hv : v∈F
    · rw [if_pos hv,TensorProduct.tmul_smul,map_zsmul_unit]
      rw [projection_tmul_basis_of_ne]
      · exact smul_zero _
      · rw [Finset.card_erase_of_mem hv]
        have hp : 0<F.card := Finset.card_pos.mpr ⟨v,hv⟩
        omega
    · rw [if_neg hv,TensorProduct.tmul_zero,
        (projection (K:=K) (V:=V) (M:=M) p).map_zero]

theorem projection_differential (x : V → R) (p : ℕ)
    (z : Total (K:=K) (V:=V) (M:=M)) :
    projection (K:=K) p (differential x z)=
      coordinateDifferential x (ModuleCat.of R M) p (projection (K:=K) (p+1) z) := by
  have he : (projection (K:=K) (V:=V) (M:=M) p).comp (differential x)=
      ((coordinateDifferential x (ModuleCat.of R M) p).restrictScalars K).comp
        (projection (K:=K) (p+1)) := by
    apply TensorProduct.ext'
    intro a
    have hb := (Simplicial.basis (V:=V) (k:=K)).mem_span
    intro z
    induction hb z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F,rfl⟩ := hz
      exact projection_differential_tmul_basis x p a F
    | zero => simp only [TensorProduct.tmul_zero,LinearMap.comp_apply,map_zero,
        LinearMap.restrictScalars_apply]
    | add z w hz hw ihz ihw =>
      simpa only [TensorProduct.tmul_add,LinearMap.comp_apply,map_add,
        LinearMap.restrictScalars_apply] using congrArg₂ (·+·) ihz ihw
    | smul r z hz ih =>
      simpa only [TensorProduct.tmul_smul,LinearMap.comp_apply,map_smul,
        LinearMap.restrictScalars_apply] using congrArg (r • ·) ih
  exact LinearMap.congr_fun he z

end FourPapers.TensorExteriorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerCoordinateProjection -/
section

/-! # Actual coefficient and exterior projections from Rees Koszul chains -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul MvPolynomial CategoryTheory
open scoped TensorProduct
universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (J : Ideal (MvPolynomial V K))

theorem powerCoefficient_baseVariable_mul (s : ℕ) (v : V) (r : coefficientRees J) :
    coefficientAt (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s
      (idealReesBaseVariable J v*r) =
      (X v : MvPolynomial V K) •
        coefficientAt (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s r := by
  apply Subtype.ext
  change (AddMonoidAlgebra.single 0 (X v)*r.val).coeff s = X v*r.val.coeff s
  simpa only [zero_add] using AddMonoidAlgebra.coeff_single_mul_add r.val (X v) 0 s

theorem powerKoszulProjection_d (s : ℕ) (z : IdealReesKoszul J) :
    powerKoszulProjection J s ((idealReesKoszulDGA J).d z)=
      idealPowerKoszulDifferential J s (powerKoszulProjection J s z) := by
  have he : (powerKoszulProjection J s).comp (idealReesKoszulDGA J).d =
      (idealPowerKoszulDifferential J s).comp (powerKoszulProjection J s) := by
    apply TensorProduct.ext'
    intro r z
    change powerKoszulProjection J s
      (TensorExteriorKoszul.differential (idealReesBaseVariable J) (r ⊗ₜ[K] z)) = _
    rw [TensorExteriorKoszul.differential_tmul, map_sum (powerKoszulProjection J s)]
    change _ = TensorExteriorKoszul.differential (X : V → MvPolynomial V K)
      (powerKoszulProjection J s (r ⊗ₜ[K] z))
    rw [powerKoszulProjection,TensorProduct.map_tmul,LinearMap.id_apply,
      TensorExteriorKoszul.differential_tmul]
    apply Finset.sum_congr rfl
    intro v _
    rw [TensorProduct.map_tmul, LinearMap.id_apply, smul_eq_mul,
      powerCoefficient_baseVariable_mul]
  exact LinearMap.congr_fun he z

def powerCoordinateProjection (s p : ℕ) : IdealReesKoszul J →ₗ[K]
    PowerIdealCoordinates J s p :=
  (TensorExteriorKoszul.projection (K:=K) (V:=V) (M:=idealPowerPiece J s) p).comp
    (powerKoszulProjection J s)

@[simp] theorem powerCoordinateProjection_inclusion (s p : ℕ)
    (x : PowerIdealCoordinates J s p) :
    powerCoordinateProjection J s p (powerCoordinateInclusion J s p x)=x := by
  change TensorExteriorKoszul.projection p
    (powerKoszulProjection J s (powerKoszulInclusion J s (TensorExteriorKoszul.lift p x)))=x
  rw [powerKoszulProjection_inclusion,TensorExteriorKoszul.projection_lift]

theorem powerCoordinateInclusion_injective (s p : ℕ) :
    Function.Injective (powerCoordinateInclusion J s p) := by
  intro x y h
  have he := congrArg (powerCoordinateProjection J s p) h
  simpa only [powerCoordinateProjection_inclusion] using he

theorem powerCoordinateProjection_d (s p : ℕ) (z : IdealReesKoszul J) :
    powerCoordinateProjection J s p ((idealReesKoszulDGA J).d z)=
      powerPreviousDifferential J s (p+1) (powerCoordinateProjection J s (p+1) z) := by
  change TensorExteriorKoszul.projection p
    (powerKoszulProjection J s ((idealReesKoszulDGA J).d z)) = _
  rw [powerKoszulProjection_d]
  exact TensorExteriorKoszul.projection_differential
    (X : V → MvPolynomial V K) p (powerKoszulProjection J s z)

/-- A filling in the total Rees complex gives a filling in the exact
original power and exact homological degree, by the literal projections. -/
theorem powerCoordinateInclusion_reflects_boundaries (s p : ℕ)
    (x : PowerIdealCoordinates J s p)
    (h : ∃ z, (idealReesKoszulDGA J).d z=powerCoordinateInclusion J s p x) :
    ∃ y, powerPreviousDifferential J s (p+1) y=x := by
  obtain ⟨z,hz⟩ := h
  refine ⟨powerCoordinateProjection J s (p+1) z,?_⟩
  rw [← powerCoordinateProjection_d,hz,powerCoordinateProjection_inclusion]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.HomologyMapBoundaryCriterion -/
section

/-! # Injectivity of categorical homology maps from literal boundary reflection -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]

/-- The criterion refers to the actual middle map of the supplied short
complex morphism and to the actual boundary maps. -/
theorem moduleCat_homologyMap_injective_of_reflects_boundaries
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)
    (hreflect : ∀ x : S.X₂, S.g x=0 →
      (∃ y : T.X₁,T.f y=φ.τ₂ x) → ∃ y : S.X₁,S.f y=x) :
    Function.Injective (ShortComplex.homologyMap φ) := by
  change Function.Injective (ShortComplex.homologyMap φ).hom
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  have hs : Function.Surjective S.homologyπ :=
    (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance
  obtain ⟨x,rfl⟩ := hs z
  have hcycle : S.g (S.iCycles x)=0 := by
    exact congrArg (fun f => ModuleCat.Hom.hom f x) S.iCycles_g
  have he : S.homologyπ ≫ ShortComplex.homologyMap φ ≫ T.homologyι =
      S.iCycles ≫ φ.τ₂ ≫ T.pOpcycles := by
    rw [ShortComplex.homologyπ_naturality_assoc,T.homology_π_ι,
      ← Category.assoc,ShortComplex.cyclesMap_i,Category.assoc]
  have ht : T.pOpcycles (φ.τ₂ (S.iCycles x))=0 := by
    have hh := congrArg (fun f => ModuleCat.Hom.hom f x) he
    change T.homologyι (ShortComplex.homologyMap φ (S.homologyπ x)) =
      T.pOpcycles (φ.τ₂ (S.iCycles x)) at hh
    change ShortComplex.homologyMap φ (S.homologyπ x)=0 at hz
    rw [hz,T.homologyι.hom.map_zero] at hh
    exact hh.symm
  obtain ⟨y,hy⟩ := hreflect (S.iCycles x) hcycle
    ((T.moduleCat_pOpcycles_eq_zero_iff _).mp ht)
  have hp : S.pOpcycles (S.iCycles x)=0 :=
    (S.moduleCat_pOpcycles_eq_zero_iff _).mpr ⟨y,hy⟩
  apply (Submodule.mem_bot R).mpr
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [S.homologyι.hom.map_zero]
  have hh := congrArg (fun f => ModuleCat.Hom.hom f x) S.homology_π_ι
  change S.homologyι (S.homologyπ x)=S.pOpcycles (S.iCycles x) at hh
  exact hh.trans hp

/-- The chain-complex form includes the end degree, through Mathlib's
actual `prev` and `next` short complex. -/
theorem chain_homologyMap_injective_of_reflects_boundaries
    {C D : ChainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) (p : ℕ)
    (hreflect : ∀ x : C.X p, C.d p p.pred x=0 →
      (∃ y : D.X (p+1),D.d (p+1) p y=f.f p x) →
        ∃ y : C.X (p+1),C.d (p+1) p y=x) :
    Function.Injective (HomologicalComplex.homologyMap f p) := by
  apply moduleCat_homologyMap_injective_of_reflects_boundaries
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.down ℕ) p).map f)
  have hprev : (ComplexShape.down ℕ).prev p=p+1 := ChainComplex.prev ℕ p
  have hnext : (ComplexShape.down ℕ).next p=p.pred := by
    cases p with
    | zero => exact ChainComplex.next_nat_zero
    | succ p => exact ChainComplex.next_nat_succ p
  intro x hx hy
  change C.d p ((ComplexShape.down ℕ).next p) x = 0 at hx
  change (∃ y : D.X ((ComplexShape.down ℕ).prev p),
    D.d ((ComplexShape.down ℕ).prev p) p y = f.f p x) at hy
  change ∃ y : C.X ((ComplexShape.down ℕ).prev p),
    C.d ((ComplexShape.down ℕ).prev p) p y = x
  have hx' : C.d p p.pred x = 0 :=
    Eq.mp (congrArg (fun j : ℕ => C.d p j x = 0) hnext) hx
  have hy' : ∃ y : D.X (p+1), D.d (p+1) p y = f.f p x :=
    Eq.mp (congrArg (fun j : ℕ => ∃ y : D.X j, D.d j p y = f.f p x) hprev) hy
  exact Eq.mpr (congrArg (fun j : ℕ => ∃ y : C.X j, C.d j p y = x) hprev)
    (hreflect x hx' hy')

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialTorNaturality -/
section

/-! # Naturality of the genuine polynomial Tor–Koszul comparison

The comparison uses the fixed polynomial-residue resolution. A coefficient
module map is sent to the same tensor-factor map on the Koszul complex;
this is proved from Mathlib's naturality of derived natural transformations.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.PolynomialTorNaturality
open CategoryTheory CategoryTheory.MonoidalCategory CommAlg.Koszul
open scoped TensorProduct
universe u
variable {V k : Type u} [CommRing k] [Nontrivial k] [Fintype V] [LinearOrder V]
variable {M N : ModuleCat.{u} (MvPolynomial V k)}

def coordinateMap (f : M ⟶ N) (p : ℕ) :
    (Set.powersetCard V p →₀ M) →ₗ[MvPolynomial V k] (Set.powersetCard V p →₀ N) :=
  Finsupp.mapRange.linearMap f.hom

def coordinatePrevious (M : ModuleCat.{u} (MvPolynomial V k)) : ∀ p : ℕ,
    (Set.powersetCard V p →₀ M) →ₗ[MvPolynomial V k] (Set.powersetCard V p.pred →₀ M)
  | 0 => 0
  | p+1 => coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) M p

/-- The actual coefficient-factor map on the variable-indexed tensor Koszul
complex. Its component is `id ⊗ f`, with the canonical tensor module action. -/
def familyMap (f : M ⟶ N) :
    familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M ⟶
      familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) N :=
  (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat (MvPolynomial V k))).map f)
    (ComplexShape.down ℕ)).app
      (koszulComplex (Fintype.linearCombination (MvPolynomial V k) MvPolynomial.X))

/-- The literal map of the actual derived tensor functor. -/
def torMap (p : ℕ) (f : M ⟶ N) : finitePolynomialTor p M ⟶ finitePolynomialTor p N :=
  ((Tor' (ModuleCat (MvPolynomial V k)) p).obj
    (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k))).map f

theorem familyMap_coordinates (f : M ⟶ N) (p : ℕ)
    (z : (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).X p) :
    coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) N p
      ((familyMap f).f p z) =
        coordinateMap f p (coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p z) := by
  let eM := coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p
  let eN := coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) N p
  have he : eN.toLinearMap.comp (((familyMap f).f p).hom.comp eM.symm.toLinearMap) =
      coordinateMap f p := by
    apply Finsupp.lhom_ext
    intro F
    intro a
    change coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) N p
      ((familyMap f).f p
        ((coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p).symm
          (Finsupp.single F a))) = _
    rw [coordinates_symm_single]
    change coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) N p
      (((Pi.basisFun (MvPolynomial V k) V).exteriorPower p F) ⊗ₜ[MvPolynomial V k] f a) = _
    rw [coordinates_basis_tensor]
    simp only [coordinateMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  have hh := LinearMap.congr_fun he (eM z)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using hh

theorem familyPrevious_coordinates (M : ModuleCat.{u} (MvPolynomial V k)) (p : ℕ)
    (z : (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).X p) :
    coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p.pred
      ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).d p p.pred z)=
      coordinatePrevious M p (coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p z) := by
  cases p with
  | zero =>
    rw [HomologicalComplex.shape _ _ _ (by simp)]
    exact (coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M 0).map_zero
  | succ p =>
    simp only [Nat.succ_pred,coordinatePrevious,coordinateDifferential,LinearMap.comp_apply,
      LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] <;> rfl

private theorem transported_homology_naturality
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {X Y X' Y' : C} {A B : D} (e : A ≅ H.obj X) (e' : B ≅ H.obj Y)
    (a : X ⟶ Y) (i : X ⟶ X') (j : Y ⟶ Y') (b : X' ⟶ Y')
    (h : i ≫ b = a ≫ j) :
    (e.hom ≫ H.map a ≫ e'.inv) ≫ (e'.hom ≫ H.map j) =
      (e.hom ≫ H.map i) ≫ H.map b := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp, ← h, H.map_comp] <;> simp only [Category.assoc]

theorem family_homologyMap_injective_of_coordinate_reflection (p : ℕ) (f : M ⟶ N)
    (hreflect : ∀ z : Set.powersetCard V p →₀ M, coordinatePrevious M p z=0 →
      (∃ w : Set.powersetCard V (p+1) →₀ N,
        coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) N p w=coordinateMap f p z) →
      ∃ w : Set.powersetCard V (p+1) →₀ M,
        coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) M p w=z) :
    Function.Injective (HomologicalComplex.homologyMap (familyMap f) p) := by
  apply FourPapers.chain_homologyMap_injective_of_reflects_boundaries
  intro z hz hb
  let eM := coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p
  have hcycle : coordinatePrevious M p (eM z)=0 := by
    rw [← familyPrevious_coordinates,hz]
    exact (coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p.pred).map_zero
  obtain ⟨w,hw⟩ := hb
  have hbound : ∃ w',coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) N p w'=
      coordinateMap f p (eM z) := by
    refine ⟨coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) N (p+1) w,?_⟩
    simp only [coordinateDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rw [hw,familyMap_coordinates]
  obtain ⟨y,hy⟩ := hreflect (eM z) hcycle hbound
  refine ⟨(coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M (p+1)).symm y,?_⟩
  apply eM.injective
  exact hy

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Tor comparison commutes with the actual coefficient map.
This is needed when an injectivity statement concerns a specific multiplier,
rather than merely the dimensions of the two Tor modules. -/
theorem finitePolynomialTorIso_naturality (p : ℕ) (f : M ⟶ N) :
    torMap p f ≫ (finitePolynomialTorIso p N).hom =
      (finitePolynomialTorIso p M).hom ≫ HomologicalComplex.homologyMap (familyMap f) p := by
  let P := finitePolynomialResolution (V := V) (k := k)
  let F := (tensoringRight (ModuleCat (MvPolynomial V k))).obj M
  let G := (tensoringRight (ModuleCat (MvPolynomial V k))).obj N
  let α : F ⟶ G := (tensoringRight (ModuleCat (MvPolynomial V k))).map f
  let H := HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k))
    (ComplexShape.down ℕ) p
  let a := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex
  have hbase : torMap p f = (P.isoLeftDerivedObj F p).hom ≫ H.map a ≫
      (P.isoLeftDerivedObj G p).inv := by
    change (NatTrans.leftDerived α p).app
      (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) = _
    exact P.leftDerived_app_eq α p
  have hchain : (finiteCoefficientComplexIso M).hom ≫ familyMap f =
      a ≫ (finiteCoefficientComplexIso N).hom := by
    exact (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).naturality
      (finiteVariableKoszulIso (V := V) (k := k)).hom
  have htransport := transported_homology_naturality H
    (P.isoLeftDerivedObj F p) (P.isoLeftDerivedObj G p) a
    (finiteCoefficientComplexIso M).hom (finiteCoefficientComplexIso N).hom
    (familyMap f) hchain
  change torMap p f ≫ ((P.isoLeftDerivedObj G p).hom ≫
      H.map (finiteCoefficientComplexIso N).hom) =
    ((P.isoLeftDerivedObj F p).hom ≫ H.map (finiteCoefficientComplexIso M).hom) ≫
      H.map (familyMap f)
  rw [hbase]
  exact htransport

/-- Boundary reflection for the literal coefficient map implies injection
of Mathlib's actual `Tor'(k,−).map`, through its proved natural comparison. -/
theorem torMap_injective_of_coordinate_reflection (p : ℕ) (f : M ⟶ N)
    (hreflect : ∀ z : Set.powersetCard V p →₀ M, coordinatePrevious M p z=0 →
      (∃ w : Set.powersetCard V (p+1) →₀ N,
        coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) N p w=coordinateMap f p z) →
      ∃ w : Set.powersetCard V (p+1) →₀ M,
        coordinateDifferential (MvPolynomial.X : V → MvPolynomial V k) M p w=z) :
    Function.Injective (torMap p f) := by
  intro x y hxy
  apply (ModuleCat.mono_iff_injective (finitePolynomialTorIso p M).hom).mp inferInstance
  apply family_homologyMap_injective_of_coordinate_reflection p f hreflect
  have hx := congrArg (fun h => ModuleCat.Hom.hom h x) (finitePolynomialTorIso_naturality p f)
  have hy := congrArg (fun h => ModuleCat.Hom.hom h y) (finitePolynomialTorIso_naturality p f)
  change (finitePolynomialTorIso p N).hom (torMap p f x)=
    HomologicalComplex.homologyMap (familyMap f) p ((finitePolynomialTorIso p M).hom x) at hx
  change (finitePolynomialTorIso p N).hom (torMap p f y)=
    HomologicalComplex.homologyMap (familyMap f) p ((finitePolynomialTorIso p M).hom y) at hy
  exact hx.symm.trans ((congrArg (finitePolynomialTorIso p N).hom hxy).trans hy)

end FourPapers.PolynomialTorNaturality

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialTorHomogeneousMap -/
section

/-! # The internal degree of the actual polynomial Tor map

A degree-q Tor class is a class represented by an actual homogeneous Koszul
cycle, whose exterior-p coefficients have degree q-p. Naturality transports
the very same cycle under the coefficient map, so a homogeneous coefficient
map gives the asserted degree shift on the actual derived functor.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.PolynomialTorNaturality
open CategoryTheory CommAlg.Koszul
universe u
variable {V k : Type u} [CommRing k] [Nontrivial k] [Fintype V] [LinearOrder V]
variable {M N : ModuleCat.{u} (MvPolynomial V k)}

/-- The standard homogeneous-cycle description of the degree-q part of the
actual Tor object. P specifies the actual coefficient degree subsets. -/
def HasDegree (P : ℤ → Set M) (q : ℤ) (p : ℕ) (z : finitePolynomialTor p M) : Prop :=
  ∃ x : (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).cycles p,
    (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homologyπ p x=
      (finitePolynomialTorIso p M).hom z ∧
    ∀ F : Set.powersetCard V p,
      coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p
        ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).iCycles p x) F∈
          P (q-(p:ℤ))

/-- Naturality preserves the actual homogeneous representative, with the
specified integer degree shift. Neither Tor object is redefined. -/
theorem torMap_hasDegree (P : ℤ → Set M) (Q : ℤ → Set N) (δ : ℤ)
    (f : M ⟶ N) (hdegree : ∀ r x,x∈P r→f x∈Q (r+δ))
    (p : ℕ) (q : ℤ) (z : finitePolynomialTor p M) (hz : HasDegree P q p z) :
    HasDegree Q (q+δ) p (torMap p f z) := by
  obtain ⟨x,hx,hP⟩ := hz
  refine ⟨HomologicalComplex.cyclesMap (familyMap f) p x,?_,?_⟩
  · have hπ := congrArg (fun a => ModuleCat.Hom.hom a x)
      (HomologicalComplex.homologyπ_naturality (familyMap f) p)
    change HomologicalComplex.homologyMap (familyMap f) p
      ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homologyπ p x)=
      (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) N).homologyπ p
        (HomologicalComplex.cyclesMap (familyMap f) p x) at hπ
    have hT := congrArg (fun a => ModuleCat.Hom.hom a z)
      (finitePolynomialTorIso_naturality p f)
    change (finitePolynomialTorIso p N).hom (torMap p f z)=
      HomologicalComplex.homologyMap (familyMap f) p ((finitePolynomialTorIso p M).hom z) at hT
    exact hπ.symm.trans ((congrArg (HomologicalComplex.homologyMap (familyMap f) p) hx).trans hT.symm)
  · intro F
    have hi := congrArg (fun a => ModuleCat.Hom.hom a x)
      (HomologicalComplex.cyclesMap_i (familyMap f) p)
    change (familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) N).iCycles p
      (HomologicalComplex.cyclesMap (familyMap f) p x)=
        (familyMap f).f p
          ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).iCycles p x) at hi
    rw [hi,familyMap_coordinates]
    change f (coefficientCoordinates (MvPolynomial.X : V → MvPolynomial V k) M p
      ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).iCycles p x) F)∈
      Q (q+δ-(p:ℤ))
    rw [show q+δ-(p:ℤ)=(q-(p:ℤ))+δ by omega]
    exact hdegree (q-(p:ℤ)) _ (hP F)

end FourPapers.PolynomialTorNaturality

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialTorPaperNaturality -/
section

/-! # Naturality under swapping the two Tor arguments

The coefficient-first Koszul computation is compared with `Tor(M,k)` by the
braiding before deriving.  This file proves that the comparison respects each
specified module map.  Consequently the injectivity results concern the literal
map of Mathlib's `Tor` functor in the `Tor(M,k)` convention.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.Sublattice

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

section Braided

variable {C : Type*} [Category C] [Abelian C] [HasProjectiveResolutions C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]

/-- Naturality in the module argument of the tensor-order comparison. -/
theorem torPrimeSwapIso_naturality_right (p : ℕ) (X : C) {Y Z : C} (f : Y ⟶ Z) :
    ((Tor' C p).obj X).map f ≫ (torPrimeSwapIso p X Z).hom =
      (torPrimeSwapIso p X Y).hom ≫ ((Tor C p).map f).app X := by
  have h : (tensoringRight C).map f ≫
        (BraidedCategory.tensorLeftIsoTensorRight Z).inv =
      (BraidedCategory.tensorLeftIsoTensorRight Y).inv ≫
        (tensoringLeft C).map f := by
    apply NatTrans.ext
    funext W
    exact BraidedCategory.braiding_inv_naturality_right W f
  have hd := congrArg
    (fun a : (tensoringRight C).obj Y ⟶ (tensoringLeft C).obj Z =>
      NatTrans.leftDerived a p) h
  simp only [NatTrans.leftDerived_comp] at hd
  have he := congrArg (fun a => a.app X) hd
  change (NatTrans.leftDerived ((tensoringRight C).map f) p).app X ≫
      (NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight Z).inv p).app X =
    (NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight Y).inv p).app X ≫
      (NatTrans.leftDerived ((tensoringLeft C).map f) p).app X
  simpa only [NatTrans.comp_app] using he

end Braided

end FourPapers.Sublattice

namespace FourPapers.PolynomialTorNaturality

open CategoryTheory CommAlg.Koszul FourPapers.Sublattice

universe u
variable {V k : Type u} [CommRing k] [Nontrivial k] [Fintype V] [LinearOrder V]
variable {M N : ModuleCat.{u} (MvPolynomial V k)}

/-- The map of `Tor^S(-,k)` induced by the specified polynomial-module map. -/
def paperTorMap (p : ℕ) (f : M ⟶ N) :
    ((Tor (ModuleCat (MvPolynomial V k)) p).obj M).obj
        (residueCoefficientModule (V := V) (k := k)) ⟶
      ((Tor (ModuleCat (MvPolynomial V k)) p).obj N).obj
        (residueCoefficientModule (V := V) (k := k)) :=
  ((Tor (ModuleCat (MvPolynomial V k)) p).map f).app
    (residueCoefficientModule (V := V) (k := k))

/-- Changing the residue quotient to the actual coefficient field is natural
in the specified coefficient-module map. -/
theorem finitePolynomialTorCoefficientIso_naturality (p : ℕ) (f : M ⟶ N) :
    torMap p f ≫ (finitePolynomialTorCoefficientIso p N).hom =
      (finitePolynomialTorCoefficientIso p M).hom ≫
        ((Tor' (ModuleCat (MvPolynomial V k)) p).obj
          (residueCoefficientModule (V := V) (k := k))).map f := by
  exact ((Tor' (ModuleCat (MvPolynomial V k)) p).map
    (residueCoefficientIso (V := V) (k := k)).hom).naturality f

/-- The fixed Tor identification intertwines the literal maps in both argument
orders; it therefore preserves map statements, not only dimensions. -/
theorem finitePolynomialTorPaperIso_naturality (p : ℕ) (f : M ⟶ N) :
    torMap p f ≫ (finitePolynomialTorPaperIso p N).hom =
      (finitePolynomialTorPaperIso p M).hom ≫ paperTorMap p f := by
  change torMap p f ≫ (finitePolynomialTorCoefficientIso p N).hom ≫
      (torPrimeSwapIso p (residueCoefficientModule (V := V) (k := k)) N).hom =
    ((finitePolynomialTorCoefficientIso p M).hom ≫
      (torPrimeSwapIso p (residueCoefficientModule (V := V) (k := k)) M).hom) ≫
        paperTorMap p f
  rw [← Category.assoc, finitePolynomialTorCoefficientIso_naturality]
  rw [Category.assoc, torPrimeSwapIso_naturality_right]
  simp only [Category.assoc, paperTorMap]

/-- The inverse comparison carries a literal paper-order Tor map to the
same coefficient map in the fixed Koszul computation. -/
theorem finitePolynomialTorPaperIso_inv_naturality (p : ℕ) (f : M ⟶ N) :
    (finitePolynomialTorPaperIso p M).inv ≫ torMap p f =
      paperTorMap p f ≫ (finitePolynomialTorPaperIso p N).inv := by
  have h := finitePolynomialTorPaperIso_naturality p f
  have he := congrArg
    (fun a => (finitePolynomialTorPaperIso p M).inv ≫ a ≫
      (finitePolynomialTorPaperIso p N).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using he

private theorem injective_under_natural_iso {R : Type u} [Ring R]
    {X Y X' Y' : ModuleCat.{u} R} (f : X ⟶ Y) (g : X' ⟶ Y')
    (e : X ≅ X') (e' : Y ≅ Y') (h : f ≫ e'.hom = e.hom ≫ g)
    (hf : Function.Injective f) : Function.Injective g := by
  intro x y hxy
  apply (ModuleCat.mono_iff_injective e.inv).mp inferInstance
  apply hf
  apply (ModuleCat.mono_iff_injective e'.hom).mp inferInstance
  have hx := congrArg (fun a => ModuleCat.Hom.hom a (e.inv x)) h
  have hy := congrArg (fun a => ModuleCat.Hom.hom a (e.inv y)) h
  change e'.hom (f (e.inv x)) = g (e.hom (e.inv x)) at hx
  change e'.hom (f (e.inv y)) = g (e.hom (e.inv y)) at hy
  have he (z : X') : e.hom (e.inv z) = z := by
    exact congrArg (fun a => ModuleCat.Hom.hom a z) e.inv_hom_id
  rw [he] at hx hy
  exact hx.trans (hxy.trans hy.symm)

/-- Injectivity of the computed map gives injectivity of the literal
`Tor^S(-,k)` map in the manuscript. -/
theorem paperTorMap_injective (p : ℕ) (f : M ⟶ N)
    (hf : Function.Injective (torMap p f)) :
    Function.Injective (paperTorMap p f) :=
  injective_under_natural_iso (torMap p f) (paperTorMap p f)
    (finitePolynomialTorPaperIso p M) (finitePolynomialTorPaperIso p N)
    (finitePolynomialTorPaperIso_naturality p f) hf

end FourPapers.PolynomialTorNaturality

end
end

/- BEGIN EXACT BODY: FourPapers.Common.SignedWeightInitial -/
section

/-!
# Initial ideals for arbitrary signed integer weights

The initial form is the component of maximal weight among the finitely
many nonzero monomials. Its weight may be negative. The initial ideal is
the ideal generated by these initial forms. A component at any upper
bound for the support is either this initial form or zero; this useful
formulation avoids imposing an unnecessary positivity assumption.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.SignedWeightInitial

open Classical MvPolynomial

universe uk ut
variable {k : Type uk} {T : Type ut} [CommRing k] (ω : T → ℤ)

def topWeight (f : MvPolynomial T k) : ℤ :=
  if h : f.support.Nonempty then f.support.sup' h (Finsupp.weight ω) else 0

def initialForm (f : MvPolynomial T k) : MvPolynomial T k :=
  weightedHomogeneousComponent ω (topWeight ω f) f

def initialIdeal (A : Ideal (MvPolynomial T k)) : Ideal (MvPolynomial T k) :=
  Ideal.span (initialForm ω '' (A : Set (MvPolynomial T k)))

theorem topWeight_bound (f : MvPolynomial T k) (a : T →₀ ℕ) (ha : a ∈ f.support) :
    Finsupp.weight ω a ≤ topWeight ω f := by
  rw [topWeight,dif_pos ⟨a,ha⟩]
  exact Finset.le_sup' (Finsupp.weight ω) ha

theorem upperComponent_eq_initialForm_or_zero (f : MvPolynomial T k) (q : ℤ)
    (hq : ∀ a ∈ f.support, Finsupp.weight ω a ≤ q) :
    weightedHomogeneousComponent ω q f = initialForm ω f ∨
      weightedHomogeneousComponent ω q f = 0 := by
  by_cases hs : f.support.Nonempty
  · by_cases he : q = topWeight ω f
    · left
      rw [he]
      rfl
    · right
      apply weightedHomogeneousComponent_eq_zero'
      intro a ha hqa
      have ha' := topWeight_bound ω f a ha
      have htop : topWeight ω f ≤ q := by
        rw [topWeight,dif_pos hs]
        exact Finset.sup'_le hs (Finsupp.weight ω) hq
      exact he (le_antisymm (hqa ▸ ha') htop)
  · right
    have hf : f = 0 := MvPolynomial.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    rw [hf,map_zero]

/-- This is a consequence of the usual maximum-weight initial form. -/
theorem upperComponent_mem_initialIdeal (A : Ideal (MvPolynomial T k))
    (f : MvPolynomial T k) (hf : f ∈ A) (q : ℤ)
    (hq : ∀ a ∈ f.support, Finsupp.weight ω a ≤ q) :
    weightedHomogeneousComponent ω q f ∈ initialIdeal ω A := by
  rcases upperComponent_eq_initialForm_or_zero ω f q hq with he | he
  · rw [he]
    exact Ideal.subset_span ⟨f,hf,rfl⟩
  · rw [he]
    exact Ideal.zero_mem _

theorem component_monomial (q : ℤ) (c : T →₀ ℕ) (r : k) :
    weightedHomogeneousComponent ω q (MvPolynomial.monomial c r) =
      if Finsupp.weight ω c = q then MvPolynomial.monomial c r else 0 := by
  simpa only [eq_comm] using weightedHomogeneousComponent_of_mem
    (m := q) (isWeightedHomogeneous_monomial ω c r rfl)

/-- For a binomial relation whose head lies in the specified monomial
initial ideal and whose tail survives, the selected head has strictly
larger weight. Tied weights are ruled out as well. -/
theorem binomial_weight_strict
    (A B : Ideal (MvPolynomial T k)) (hAB : initialIdeal ω A = B)
    {c e : T →₀ ℕ}
    (hrel : MvPolynomial.monomial c 1 - MvPolynomial.monomial e 1 ∈ A)
    (hc : MvPolynomial.monomial c 1 ∈ B)
    (he : MvPolynomial.monomial e 1 ∉ B) :
    Finsupp.weight ω e < Finsupp.weight ω c := by
  by_contra h
  have hle : Finsupp.weight ω c ≤ Finsupp.weight ω e := le_of_not_gt h
  have hbound : ∀ a ∈
      (MvPolynomial.monomial c (1 : k) - MvPolynomial.monomial e 1).support,
      Finsupp.weight ω a ≤ Finsupp.weight ω e := by
    intro a ha
    by_cases hac : a = c
    · subst a
      exact hle
    · by_cases hae : a = e
      · subst a
        exact le_rfl
      · have hz : (MvPolynomial.monomial c (1 : k) - MvPolynomial.monomial e 1).coeff a = 0 := by
          simp only [MvPolynomial.coeff_sub,MvPolynomial.coeff_monomial,
            Ne.symm hac,Ne.symm hae,if_false,sub_self]
        exact False.elim ((MvPolynomial.mem_support_iff.mp ha) hz)
  have hi := upperComponent_mem_initialIdeal ω A
    (MvPolynomial.monomial c 1 - MvPolynomial.monomial e 1) hrel
    (Finsupp.weight ω e) hbound
  have hcomp : weightedHomogeneousComponent ω (Finsupp.weight ω e)
      (MvPolynomial.monomial c (1 : k) - MvPolynomial.monomial e 1) =
      weightedHomogeneousComponent ω (Finsupp.weight ω e) (MvPolynomial.monomial c (1 : k)) -
      weightedHomogeneousComponent ω (Finsupp.weight ω e) (MvPolynomial.monomial e (1 : k)) :=
    (weightedHomogeneousComponent ω (Finsupp.weight ω e) :
      MvPolynomial T k →ₗ[k] MvPolynomial T k).map_sub _ _
  rw [hAB, hcomp, component_monomial, component_monomial, if_pos rfl] at hi
  apply he
  by_cases hce : Finsupp.weight ω c = Finsupp.weight ω e
  · rw [if_pos hce] at hi
    have ht := B.sub_mem hc hi
    convert ht using 1 <;> abel
  · rw [if_neg hce,zero_sub] at hi
    simpa only [neg_neg] using B.neg_mem hi

end FourPapers.SignedWeightInitial


end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorMultiplicationNaturality -/
section

/-! # Naturality of a finite sum of coefficient multiplications and contractions -/

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.TensorMultiplicationNaturality
open Classical
open scoped TensorProduct
variable {S A B E V : Type*} [CommRing S] [CommRing A] [CommRing B]
  [Algebra S A] [Algebra S B] [AddCommMonoid E] [Module S E] [Fintype V]

def differential (x : V → A) (c : V → Module.End S E) : Module.End S (A ⊗[S] E) :=
  ∑ v, TensorProduct.map (LinearMap.mulLeft S (x v)) (c v)

/-- An algebra isomorphism carrying each coefficient to the corresponding
coefficient commutes with the literal tensor differential. -/
theorem congr_differential (e : A ≃ₐ[S] B) (x : V → A) (y : V → B)
    (c : V → Module.End S E) (h : ∀ v, e (x v) = y v) (z : A ⊗[S] E) :
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E) (differential x c z) =
      differential y c (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E) z) := by
  have he : (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E)).toLinearMap.comp
      (differential x c) = (differential y c).comp
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, differential, LinearMap.sum_apply, TensorProduct.map_tmul,
      LinearMap.mulLeft_apply, LinearEquiv.coe_coe, map_sum, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply]
    apply Finset.sum_congr rfl
    intro v _
    apply congrArg (fun t : B => t ⊗ₜ[S] c v b)
    calc
      _ = e (x v) * e a := e.map_mul _ _
      _ = _ := by rw [h v]
  exact LinearMap.congr_fun he z

/-- The subalgebra form keeps the inherited additive structures fixed
before specializing the subalgebras to large concrete generator images. -/
theorem subalgebra_congr_differential {T : Type*} [CommRing T] [Algebra S T]
    (P Q : Subalgebra S T) (e : P ≃ₐ[S] Q) (x : V → P) (y : V → Q)
    (c : V → Module.End S E) (h : ∀ v, e (x v) = y v) (z : P ⊗[S] E) :
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E)
      ((∑ v, TensorProduct.map (LinearMap.mulLeft S (x v)) (c v)) z) =
      (∑ v, TensorProduct.map (LinearMap.mulLeft S (y v)) (c v))
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl S E) z) :=
  congr_differential e x y c h z

/-- Naturality in purely linear form, retaining the supplied additive
and module structures without reconstructing them from a ring. -/
theorem linear_congr_differential {U W : Type*} [AddCommMonoid U] [Module S U]
    [AddCommMonoid W] [Module S W] (e : U ≃ₗ[S] W)
    (x : V → Module.End S U) (y : V → Module.End S W)
    (c : V → Module.End S E) (h : ∀ v a, e (x v a) = y v (e a)) (z : U ⊗[S] E) :
    TensorProduct.congr e (LinearEquiv.refl S E) ((∑ v, TensorProduct.map (x v) (c v)) z) =
      (∑ v, TensorProduct.map (y v) (c v))
        (TensorProduct.congr e (LinearEquiv.refl S E) z) := by
  have he : (TensorProduct.congr e (LinearEquiv.refl S E)).toLinearMap.comp
      (∑ v, TensorProduct.map (x v) (c v)) =
      (∑ v, TensorProduct.map (y v) (c v)).comp
        (TensorProduct.congr e (LinearEquiv.refl S E)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, map_sum, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    apply Finset.sum_congr rfl
    intro v _
    exact congrArg (fun t : W => t ⊗ₜ[S] c v b) (h v a)
  exact LinearMap.congr_fun he z

end FourPapers.TensorMultiplicationNaturality

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedMonoidFiber -/
section

/-!
# The zero-degree algebra is the genuine graded monoid quotient

The quotient is taken by the actual ideal of positive-degree monomials.
If every positive-degree exponent factors by one of specified generators,
that kernel is proved equal to the ideal generated by those generators.
This supplies the special-fiber step without assuming a toric presentation.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.GradedMonoidFiber

open Classical AddMonoidAlgebra

variable {M k : Type*} [AddCommMonoid M] [CommRing k] (degree : M →+ ℕ)

abbrev ZeroMonoid := AddMonoidHom.mker degree

def monomialProjection : Multiplicative M →* AddMonoidAlgebra k (ZeroMonoid degree) where
  toFun a := if ha : degree a.toAdd=0 then single ⟨a.toAdd,ha⟩ 1 else 0
  map_one' := by
    change (if ha : degree 0=0 then
      single (⟨0,ha⟩ : ZeroMonoid degree) (1 : k) else 0)=1
    simp only [map_zero,dif_pos]
    rfl
  map_mul' a b := by
    change (if h : degree (a.toAdd+b.toAdd)=0 then
      single (⟨a.toAdd+b.toAdd,h⟩ : ZeroMonoid degree) (1 : k) else 0)=_
    by_cases ha : degree a.toAdd=0 <;> by_cases hb : degree b.toAdd=0
    · simp only [map_add,ha,hb,zero_add,dif_pos,single_mul_single,mul_one]
      rfl
    · have hab : degree (a.toAdd+b.toAdd)≠0 := by simpa only [map_add,ha,zero_add] using hb
      simp only [dif_neg hab,dif_pos ha,dif_neg hb,mul_zero]
    · have hab : degree (a.toAdd+b.toAdd)≠0 := by simpa only [map_add,hb,add_zero] using ha
      simp only [dif_neg hab,dif_neg ha,dif_pos hb,zero_mul]
    · have hab : degree (a.toAdd+b.toAdd)≠0 := by
        intro h
        rw [map_add] at h
        exact ha (Nat.add_eq_zero_iff.mp h).1
      simp only [dif_neg hab,dif_neg ha,dif_neg hb,zero_mul]

def projection : AddMonoidAlgebra k M →ₐ[k] AddMonoidAlgebra k (ZeroMonoid degree) :=
  AddMonoidAlgebra.lift k _ M (monomialProjection (k := k) degree)

@[simp] theorem projection_single (a : M) (c : k) :
    projection degree (single a c) =
      if ha : degree a=0 then single ⟨a,ha⟩ c else 0 := by
  rw [projection,AddMonoidAlgebra.lift_single]
  change c • (if ha : degree a=0 then
    single (⟨a,ha⟩ : ZeroMonoid degree) (1 : k) else 0)=_
  by_cases ha : degree a=0
  · simp only [dif_pos ha,smul_single,smul_eq_mul,mul_one]
  · simp only [dif_neg ha,smul_zero]

def sectionMap : AddMonoidAlgebra k (ZeroMonoid degree) →ₐ[k] AddMonoidAlgebra k M :=
  AddMonoidAlgebra.mapDomainAlgHom k k (AddMonoidHom.mker degree).subtype

@[simp] theorem sectionMap_single (a : ZeroMonoid degree) (c : k) :
    sectionMap degree (single a c)=single a.val c :=
  AddMonoidAlgebra.mapDomain_single

theorem projection_section (z : AddMonoidAlgebra k (ZeroMonoid degree)) :
    projection degree (sectionMap degree z)=z := by
  induction z using AddMonoidAlgebra.induction_on with
  | of a =>
      change projection degree (sectionMap degree (single a 1))=single a 1
      have ha : degree a.val = 0 := a.property
      rw [sectionMap_single,projection_single]
      exact dif_pos ha
  | add x y hx hy => simp only [map_add,hx,hy]
  | smul r x hx => simp only [map_smul,hx]

theorem projection_surjective : Function.Surjective (projection (k := k) degree) :=
  fun z => ⟨sectionMap degree z,projection_section degree z⟩

def positiveIdeal : Ideal (AddMonoidAlgebra k M) :=
  Ideal.span {f | ∃ a : M, degree a≠0 ∧ f=single a 1}

theorem subtract_projection_mem (x : AddMonoidAlgebra k M) :
    x-sectionMap degree (projection degree x) ∈ positiveIdeal degree := by
  induction x using AddMonoidAlgebra.induction_on with
  | of a =>
      change single a 1-sectionMap degree (projection degree (single a 1)) ∈ positiveIdeal degree
      by_cases ha : degree a=0
      · rw [projection_single,dif_pos ha,sectionMap_single,sub_self]
        exact Ideal.zero_mem _
      · rw [projection_single,dif_neg ha,map_zero,sub_zero]
        exact Ideal.subset_span ⟨a,ha,rfl⟩
  | add x y hx hy =>
      simpa only [map_add,add_sub_add_comm] using Ideal.add_mem _ hx hy
  | smul r x hx =>
      simpa only [map_smul,smul_sub] using
        (positiveIdeal (k := k) degree).smul_of_tower_mem r hx

theorem projection_ker : RingHom.ker (projection (k := k) degree).toRingHom=positiveIdeal degree := by
  apply le_antisymm
  · intro x hx
    have hh : projection degree x=0 := hx
    simpa only [hh,map_zero,sub_zero] using subtract_projection_mem degree x
  · apply Ideal.span_le.mpr
    rintro f ⟨a,ha,rfl⟩
    change projection degree (single a 1)=0
    rw [projection_single,dif_neg ha]

def quotientEquiv : (AddMonoidAlgebra k M ⧸ positiveIdeal degree) ≃ₐ[k]
    AddMonoidAlgebra k (ZeroMonoid degree) :=
  (Ideal.quotientEquivAlgOfEq k (projection_ker degree).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (projection_surjective degree))

/-- The positive-degree kernel is generated by genuine degree-positive
monoid factors, once their factorization property has been proved. -/
theorem positiveIdeal_eq_generatorIdeal (G : Set M)
    (hpos : ∀ g∈G, degree g≠0)
    (hfactor : ∀ a, degree a≠0 → ∃ g∈G, ∃ b, a=g+b) :
    positiveIdeal (k := k) degree = Ideal.span ((fun g : M => single g (1 : k)) '' G) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨a,ha,rfl⟩
    obtain ⟨g,hg,b,rfl⟩ := hfactor a ha
    rw [show single (g+b) (1 : k)=single g 1*single b 1 by
      simp only [single_mul_single,mul_one]]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨g,hg,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro f ⟨g,hg,rfl⟩
    exact Ideal.subset_span ⟨g,hpos g hg,rfl⟩

end FourPapers.GradedMonoidFiber

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.AffineDomainDimension -/
section

/-!
# Krull dimension of an affine domain from an actual transcendence basis

The comparison is proved from prime chains, integral going-up and
incomparability, and Mathlib's Noether normalization. It does not replace
Krull dimension by a combinatorial rank definition.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical CategoryTheory Algebra

theorem ringKrullDim_eq_of_integral_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) : ringKrullDim S=ringKrullDim R := by
  algebraize [f]
  letI : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have hsurj := Algebra.IsIntegral.comap_surjective R S
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under hPQ
  · rw [ringKrullDim,Order.krullDim]
    apply iSup_le
    intro c
    obtain ⟨P,hP⟩ := hsurj c.head
    letI : P.asIdeal.LiesOver c.head.asIdeal :=
      ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨C,hC,hhead,hmap⟩ := Ideal.exists_ltSeries_of_hasGoingUp c P.asIdeal
    rw [← hC]
    exact Order.LTSeries.length_le_krullDim C

/-- The integer dimension of an affine domain equals the size of any
finite actual transcendence basis. Both sides use Mathlib's established
invariants and algebraic-independence notion. -/
theorem ringKrullDim_eq_card_of_transcendenceBasis
    {k A I : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Fintype I] {x : I → A}
    (hx : IsTranscendenceBasis k x) : ringKrullDim A=Fintype.card I := by
  obtain ⟨s,g,hg,hint⟩ := _root_.exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A=s := by
    rw [ringKrullDim_eq_of_integral_injective g.toRingHom hint hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
    simp only [Nat.card_fin,zero_add]
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have hy := (IsTranscendenceBasis.mvPolynomial (Fin s) k).algebraMap_comp
    (A := A)
  have hcard := hx.lift_cardinalMk_eq hy
  have hs : Fintype.card I=s := by
    simpa only [Cardinal.mk_fintype,Cardinal.lift_natCast,Fintype.card_fin,
      Nat.cast_inj] using hcard
  rw [hdim,hs]

theorem ringKrullDim_eq_nat_of_trdeg
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {n : ℕ} (hn : Algebra.trdeg k A=(n : Cardinal)) :
    ringKrullDim A=n := by
  obtain ⟨s,g,hg,hint⟩ := _root_.exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have hy := (IsTranscendenceBasis.mvPolynomial (Fin s) k).algebraMap_comp (A := A)
  have hs : (s : Cardinal)=Algebra.trdeg k A := by
    simpa only [Cardinal.mk_fintype,Fintype.card_fin,Cardinal.lift_natCast,
      Cardinal.lift_id,Cardinal.lift_uzero] using hy.lift_cardinalMk_eq_trdeg
  have he : s=n := by exact_mod_cast hs.trans hn
  rw [ringKrullDim_eq_of_integral_injective g.toRingHom hint hg,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field]
  simp only [Nat.card_fin,zero_add,he]

end FourPapers

end
end
end


end

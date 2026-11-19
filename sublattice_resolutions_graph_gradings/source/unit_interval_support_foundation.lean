module
public import shared_results.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalPowerSupport -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotient_boundary_homogeneous (B : Family V) (α : Exponent V) (p : ℕ)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hz : z ∈ totalFacePiece (quotientKoszulFaces B α) p)
    (hfill : ∃ y, quotientTotalDifferential B α y = z) :
    ∃ y, y ∈ totalFacePiece (quotientKoszulFaces B α) (p+1) ∧
      quotientTotalDifferential B α y = z := by
  obtain ⟨y, hy⟩ := hfill
  let b := totalFaceBasis (k := k) (quotientKoszulFaces B α)
  let degree := fun F : {F // quotientKoszulFaces B α F} => F.val.card
  refine ⟨Grading.projection b degree (p+1) y, ?_, ?_⟩
  · rw [totalFacePiece_eq_basis_span]
    exact Grading.projection_mem b degree (p+1) y
  · have h := LinearMap.congr_fun (quotientTotalDifferential_degree_projection (k := k) B α p) y
    change quotientTotalDifferential B α (Grading.projection b degree (p+1) y) =
      Grading.projection b degree p (quotientTotalDifferential B α y) at h
    rw [h, hy]
    apply Grading.projection_eq_self
    change z ∈ Grading.Piece (totalFaceBasis (k := k) (quotientKoszulFaces B α))
      (fun F => F.val.card) p
    unfold Grading.Piece
    rw [← totalFacePiece_eq_basis_span]
    exact hz

variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

/-- Equation (6.2), proved before taking dimensions: every actual homogeneous
cycle outside the required congruence has a homogeneous filling, in every
positive power and over every commutative coefficient ring. -/
theorem unitInterval_power_cycle_boundary (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hp : (p : ZMod d) + (m : ZMod d) ≠ (α.degree : ZMod d))
    (z : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α))
    (hzp : z ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) p)
    (hz : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) z = 0) :
    ∃ y, y ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) (p+1) ∧
      idealTotalDifferential
        (koszulFaces_downward (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) y = z := by
  apply allPowerCycle_boundary_of_blocks hE.latticeClosed m hm α p _ z hzp hz
  intro w x hxp hx
  apply quotient_boundary_homogeneous _ _ p x hxp
  have hdeg := congrArg Finsupp.degree (tsub_add_cancel_of_le w.property)
  simp only [map_add, finiteChainShift_degree] at hdeg
  have hmod := congrArg (fun q : ℕ => (q : ZMod d)) hdeg
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self,
    zero_add, mul_one] at hmod
  have hne : (p : ZMod d) ≠ ((α-finiteChainShift (UnitIntervalRows d N) w.val).degree : ZMod d) := by
    intro heq
    exact hp (heq.symm ▸ hmod)
  cases m with
  | zero => omega
  | succ m =>
    exact unitInterval_chain_coefficient_residue_boundary hE w.val _ (p : ZMod d) x
      (faceResidueSpace_of_homogeneous _ p d hxp) hx hne

theorem unitInterval_power_faces_exact (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hp : (p : ZMod d) + (m : ZMod d) ≠ (α.degree : ZMod d)) :
    Simplicial.ExactIn (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) p := by
  intro z hzp hz
  let x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α) :=
    ⟨z, chains_mem_basisSpan hzp⟩
  obtain ⟨y, hyp, hy⟩ := unitInterval_power_cycle_boundary hE m hm α p hp x hzp (Subtype.ext hz)
  exact ⟨y.val, hyp, congrArg Subtype.val hy⟩

/-- The vanishing statement concerns the genuine polynomial-ideal Koszul
complex and its actual categorical homology. -/
theorem unitInterval_power_homology_zero (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hp : (p : ZMod d) + (m : ZMod d) ≠ (α.degree : ZMod d)) :
    IsZero ((homogeneousComplex (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α).homology p) :=
  (((Simplicial.chainComplex_exactAt_iff _ p).mpr
    (unitInterval_power_faces_exact hE m hm α p hp)).of_iso
      (homogeneousFacesIso _ α)).isZero_homology

/-- For a fixed ordinary degree the vanishing alternative is uniform across
all fine degrees. This is the exact input needed before applying the filtered
homology gap theorem; pointwise alternatives would not suffice. -/
theorem unitInterval_power_uniform_homology_gap (hE : UnitIntervalFacetFamily E)
    (hd : 2 ≤ d) (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    (∀ α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)), α.degree = q →
      IsZero ((homogeneousComplex (k := k)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α).homology p)) ∨
    (∀ α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)), α.degree = q →
      IsZero ((homogeneousComplex (k := k)
        (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α).homology (p+1))) := by
  by_cases hp : (p : ZMod d) + (m : ZMod d) = (q : ZMod d)
  · right
    intro α hα
    apply unitInterval_power_homology_zero hE m hm α (p+1)
    intro hbad
    rw [hα] at hbad
    simp only [Nat.cast_add, Nat.cast_one] at hbad
    have hone : (1 : ZMod d) = 0 := by
      linear_combination hbad - hp
    have he := ZMod.one_eq_zero_iff.mp hone
    omega
  · left
    intro α hα
    apply unitInterval_power_homology_zero hE m hm α p
    simpa only [hα] using hp

section Field
variable {K : Type u} [Field K]

/-- The full fine-graded support congruence (6.2) for the usual derived-Tor
Betti numbers, for all positive powers and every field. -/
theorem unitInterval_power_betti_congruence (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hp : bettiNumber (k := K)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α p ≠ 0) :
    (p : ZMod d) + (m : ZMod d) = (α.degree : ZMod d) := by
  by_contra hn
  have hnon := (bettiNumber_pos_iff_faces (k := K)
    (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) α p).mp (Nat.pos_of_ne_zero hp)
  exact ((Simplicial.nonzeroHomology_iff_not_exactIn _ p).mp hnon)
    (unitInterval_power_faces_exact (k := K) hE m hm α p hn)

end Field
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_power_homology_zero
#print axioms FourPapers.Sublattice.unitInterval_power_betti_congruence

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalOrdinaryGap -/
section

/-!
# Actual ordinary-degree cycle fillings for the higher-row transfer

Fine-degree exactness is transported through the genuine Koszul face
equivalence. The finite homogeneous support decomposition then assembles
the fillings in ordinary degree. Thus the adjacent-degree alternative is
uniform in the entire ordinary strand, including homological degree zero.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

/-- Every actual ordinary-degree cycle outside (6.2) has an actual filling
of the same ordinary degree. This statement is valid over every coefficient
ring, before any dimensions are taken. -/
theorem unitInterval_power_ordinary_exact (hE : UnitIntervalFacetFamily E)
    (m : ℕ) (hm : 0 < m) (q p : ℕ)
    (hp : (p : ZMod d) + (m : ZMod d) ≠ (q : ZMod d)) :
    MonomialOrdinaryExact (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p := by
  apply monomialOrdinaryExact_of_fine_exact
  intro α hα
  apply unitInterval_power_faces_exact (k := k) hE m hm α p
  simpa only [hα] using hp

/-- The exact two adjacent ordinary-strand alternative needed by the
filtered comparison, uniformly in all fine/leading degrees. Here `d+1` is
the number of matrix rows, so `2 ≤ d` is the paper's `3 ≤ row count`. -/
theorem unitInterval_power_ordinary_gap (hE : UnitIntervalFacetFamily E)
    (hd : 2 ≤ d) (m : ℕ) (hm : 0 < m) (q p : ℕ) :
    MonomialOrdinaryExact (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q p ∨
    MonomialOrdinaryExact (k := k)
      (exponentPowerFamily (finiteRowFamily (UnitIntervalRows d N) E) m) q (p+1) := by
  by_cases hp : (p : ZMod d) + (m : ZMod d) = (q : ZMod d)
  · right
    apply unitInterval_power_ordinary_exact (k := k) hE m hm q (p+1)
    intro hbad
    simp only [Nat.cast_add, Nat.cast_one] at hbad
    have hone : (1 : ZMod d) = 0 := by linear_combination hbad - hp
    have he := ZMod.one_eq_zero_iff.mp hone
    omega
  · exact Or.inl (unitInterval_power_ordinary_exact (k := k) hE m hm q p hp)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.unitInterval_power_ordinary_exact
#print axioms FourPapers.Sublattice.unitInterval_power_ordinary_gap

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredClassLifting -/
section

/-! # Homology-class lifting and actual cycle lifting

An associated graded cycle can be corrected by an actual boundary whenever its
homology class is the leading class of an actual cycle. Thus multiplicative
generation only needs to lift homology classes, not chosen cycle representatives.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.FilteredHomology

variable {K X Y Z : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

theorem liftsCycles_of_leadingHomologyClass_surjective
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0)
    (hsurj : ∀ n, Function.Surjective (leadingHomologyClass F G H f g hf hg hfg n)) :
    LiftsCycles G H g := by
  intro n y hy hgy
  let y' : Grade G n := Submodule.Quotient.mk (⟨y, hy⟩ : G.level (n + 1))
  have hy' : gradeMap G H g hg n y' = 0 := by
    change (Submodule.Quotient.mk
      (levelMap G H g hg (n + 1) ⟨y, hy⟩) : Grade H n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hgy
  let z : LinearMap.ker (gradeMap G H g hg n) := ⟨y', hy'⟩
  obtain ⟨w, hw⟩ := hsurj n
    (homologyClass _ _ (gradeMap_comp F G H f g hf hg hfg n) z)
  change homologyClass _ _ (gradeMap_comp F G H f g hf hg hfg n)
      (cycleToGradeCycle G H g hg n w) =
    homologyClass _ _ (gradeMap_comp F G H f g hf hg hfg n) z at hw
  obtain ⟨a, ha⟩ := (homologyClass_eq_iff _ _
    (gradeMap_comp F G H f g hf hg hfg n) _ _).mp hw
  obtain ⟨a, rfl⟩ := (lowerInLevel F n).mkQ_surjective a
  refine ⟨w.val.val - f a.val, (G.level (n + 1)).sub_mem w.property
    (hf (n + 1) a.val a.property), ?_, ?_⟩
  · have hga : g (f a.val) = 0 := LinearMap.congr_fun hfg a.val
    rw [map_sub, w.val.property, hga, sub_self]
  · have heq : (Submodule.Quotient.mk
        (⟨w.val.val - f a.val, (G.level (n + 1)).sub_mem w.property
          (hf (n + 1) a.val a.property)⟩ : G.level (n + 1)) : Grade G n) = y' := by
      change (Submodule.Quotient.mk (cycleToLevel G g n w) : Grade G n) -
        Submodule.Quotient.mk (levelMap F G f hf (n + 1) a) = y'
      change (Submodule.Quotient.mk (levelMap F G f hf (n + 1) a) : Grade G n) =
        Submodule.Quotient.mk (cycleToLevel G g n w) - y' at ha
      rw [ha]
      abel
    have hd := (Submodule.Quotient.eq (lowerInLevel G n)).mp heq.symm
    exact hd

theorem leadingHomologyClass_surjective_iff_liftsCycles
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0) :
    (∀ n, Function.Surjective (leadingHomologyClass F G H f g hf hg hfg n)) ↔
      LiftsCycles G H g :=
  ⟨liftsCycles_of_leadingHomologyClass_surjective F G H f g hf hg hfg,
    fun h n => leadingHomologyClass_surjective F G H f g hf hg hfg n h⟩

/-- If actual cycles span the kernel modulo actual boundaries, a linear map
onto their homology classes is onto all homology. This form accepts a spanning
statement in the ambient chain module, without first rebuilding its kernel as
a separate basis space. -/
theorem homology_surjective_of_cycle_spanning
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (L : V →ₗ[K] Homology f g hfg) (S : Set Y)
    (hcycle : ∀ y ∈ S, g y = 0)
    (hspan : LinearMap.ker g ≤ Submodule.span K S ⊔ LinearMap.range f)
    (hlift : ∀ (y : Y) (hy : y ∈ S),
      homologyClass f g hfg ⟨y, hcycle y hy⟩ ∈ LinearMap.range L) :
    Function.Surjective L := by
  let T : Submodule K Y :=
    ((LinearMap.range L).comap (homologyClass f g hfg)).map (LinearMap.ker g).subtype
  have hS : Submodule.span K S ≤ T := by
    apply Submodule.span_le.mpr
    intro y hy
    exact ⟨⟨y, hcycle y hy⟩, hlift y hy, rfl⟩
  have hB : LinearMap.range f ≤ T := by
    rintro y ⟨x, rfl⟩
    refine ⟨boundaryMap f g hfg x, ?_, rfl⟩
    change homologyClass f g hfg (boundaryMap f g hfg x) ∈ LinearMap.range L
    have hz : homologyClass f g hfg (boundaryMap f g hfg x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
    rw [hz]
    exact (LinearMap.range L).zero_mem
  have hker : LinearMap.ker g ≤ T := hspan.trans (sup_le hS hB)
  intro u
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective u
  obtain ⟨w, hw, he⟩ := hker z.property
  have heq : w = z := Subtype.ext he
  subst w
  exact hw

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyGap -/
section

/-! # Cycle lifting from a gap in adjacent leading homology groups -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredHomology

variable {R W X Y Z : Type*} [CommRing R]
  [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- For a fixed ordinary degree, either the entire leading homology in the
source degree or the entire leading homology in the following degree vanishes.
In either case every leading cycle has a genuine cycle lift. -/
theorem liftsCycles_of_homology_gap
    (E : Filtration (K := R) W) (F : Filtration (K := R) X)
    (G : Filtration (K := R) Y) (H : Filtration (K := R) Z)
    (e : W →ₗ[R] X) (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (he : Preserves E F e) (hf : Preserves F G f) (hg : Preserves G H g)
    (hef : f.comp e = 0) (hfg : g.comp f = 0)
    (hgap : (∀ n, Subsingleton (GradedHomology E F G e f he hf hef n)) ∨
      (∀ n, Subsingleton (GradedHomology F G H f g hf hg hfg n))) :
    LiftsCycles F G f := by
  rcases hgap with hzero | hzero
  · apply liftsCycles_of_leadingHomologyClass_surjective E F G e f he hf hef
    intro n x
    letI := hzero n
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact liftsCycles_of_gradedHomology_subsingleton F G H f g hf hg hfg hzero

end FourPapers.FilteredHomology

end
end
end


end

module
public import Mathlib
public import characterizations
@[expose] public noncomputable section
open scoped BigOperators
namespace PalomarPolymatroidal.Simplicial
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
/-- The actual exterior algebra of the coordinate vector space. -/
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
/-- Its standard exterior basis indexed by coordinate subsets. -/
def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
/-- Actual augmented chains on the displayed faces in exterior degree i. -/
def Chains (F : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | F s ∧ s.card = i})
/-- The signed augmented boundary is literal exterior contraction by the sum
of the coordinate functionals. -/
abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
/-- Every actual cycle in this degree is filled by a chain in the next degree. -/
def ExactIn (F : Finset V → Prop) (i : ℕ) : Prop :=
  ∀ z : Ambient V k, z ∈ Chains F i → boundary z = 0 →
    ∃ y : Ambient V k, y ∈ Chains F (i + 1) ∧ boundary y = z
end PalomarPolymatroidal.Simplicial
namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The squarefree exponent carried by an exterior coordinate subset. -/
def faceExponent (s : Finset V) : Exponent V := ∑ j ∈ s, Finsupp.single j 1
/-- The literal multidegree-a ideal Koszul faces: the residual monomial lies
in the displayed actual monomial ideal. -/
def koszulFaces (B : Family V) (a : Exponent V) (s : Finset V) : Prop :=
  faceExponent s ≤ a ∧ ∃ b ∈ B, b ≤ a - faceExponent s
end PalomarPolymatroidal
namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Castelnuovo–Mumford regularity computed from actual augmented Koszul
homology: its degree bound holds for every nonexact component and is attained. -/
def KoszulRegularity (B : Family V) (r : ℕ) : Prop :=
  (∀ i a, ¬Simplicial.ExactIn (k := k) (koszulFaces B a) i → a.degree ≤ r + i) ∧
    ∃ i a, ¬Simplicial.ExactIn (k := k) (koszulFaces B a) i ∧ a.degree = r + i
/-- The actual quotient J/I, using the canonical integral-closure ideal J. -/
abbrev ClosureDifference (B : Family V) (d : ℕ) :=
  (monomialIdeal k (lowerBaseFamily (lowerRank B) d)) ⧸
    Submodule.comap (monomialIdeal k (lowerBaseFamily (lowerRank B) d)).subtype
      (monomialIdeal k B)
/-- The canonical additive group of the actual submodule quotient J/I. -/
instance closureDifferenceAddCommGroup (B : Family V) (d : ℕ) :
    AddCommGroup (ClosureDifference (k := k) B d) :=
  Submodule.Quotient.addCommGroup (R := MvPolynomial V k)
    (M := monomialIdeal k (lowerBaseFamily (lowerRank B) d))
    (Submodule.comap (monomialIdeal k (lowerBaseFamily (lowerRank B) d)).subtype
      (monomialIdeal k B))
/-- The canonical polynomial-module structure on the actual quotient J/I. -/
instance closureDifferenceModule (B : Family V) (d : ℕ) :
    Module (MvPolynomial V k) (ClosureDifference (k := k) B d) :=
  Submodule.Quotient.module (R := MvPolynomial V k)
    (M := monomialIdeal k (lowerBaseFamily (lowerRank B) d))
    (Submodule.comap (monomialIdeal k (lowerBaseFamily (lowerRank B) d)).subtype
      (monomialIdeal k B))
/-- The actual monomials in J minus I, with coefficient one. -/
def Holes (B : Family V) (d : ℕ) : Set (Exponent V) :=
  {a | MvPolynomial.monomial a (1 : k) ∈
      monomialIdeal k (lowerBaseFamily (lowerRank B) d) ∧
    MvPolynomial.monomial a (1 : k) ∉ monomialIdeal k B}
/-- Multiplication by the qth power of the actual homogeneous maximal ideal. -/
def maximalPower (B : Family V) (q : ℕ) : Ideal (MvPolynomial V k) :=
  (variableIdeal (k := k) Finset.univ) ^ q * monomialIdeal k B
end PalomarPolymatroidal
namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The genuine retained-variable derived-Tor Betti number vanishes exactly
when the displayed actual exterior Koszul cycle condition is exact. -/
private theorem exactIn_iff_betti_zero (B : Family V) (a : Exponent V) (i : ℕ) :
    Simplicial.ExactIn (k := k) (koszulFaces B a) i ↔
      CommAlg.Koszul.bettiNumber (k := k) B a i = 0 := by
  have positive : 0 < CommAlg.Koszul.bettiNumber (k := k) B a i ↔
      ¬Simplicial.ExactIn (k := k) (koszulFaces B a) i :=
    (CommAlg.Koszul.bettiNumber_pos_iff_faces B a i).trans
      (CommAlg.Simplicial.nonzeroHomology_iff_not_exactIn _ _)
  constructor
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact (positive.mp hp) h
  · intro hz
    by_contra h
    have hp := positive.mpr h
    omega

end PalomarPolymatroidal
namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem regularity_agrees (B : Family V) (r : ℕ) :
    KoszulRegularity (k := k) B r ↔ Characterizations.IsTorRegularity (k := k) B r := by
  simp only [KoszulRegularity, Characterizations.IsTorRegularity, exactIn_iff_betti_zero]

private theorem holes_agree {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    Holes (k := k) B d = Characterizations.holeSet B := by
  have hl := Characterizations.locallyEquigenerated_of_proper_polymatroidal hd hloc
  ext a
  simp only [Holes, Characterizations.holeSet, Set.mem_setOf_eq,
    CommAlg.Polymatroid.monomial_mem_iff,
    Characterizations.contains_canonicalLowerBases_iff hB hl hd]

private theorem maximalPower_polymatroidal_iff {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (q : ℕ) :
    IsPolymatroidalIdeal (maximalPower (k := k) B q) ↔
      IsPolymatroidal (Characterizations.thickening B q) := by
  change IsPolymatroidalIdeal
    ((Characterizations.coordinatePrime k Finset.univ)^q * monomialIdeal k B) ↔ _
  rw [← Characterizations.thickening_ideal_eq]
  constructor
  · rintro ⟨C,hC,hI⟩
    have he := Characterizations.antichain_generators_unique
      (k := k) (Characterizations.thickening_equigenerated hd q).antichain
      hC.1.choose_spec.antichain hI
    exact he.symm ▸ hC
  · intro hp
    exact ⟨_,hp,rfl⟩

theorem minimal_closure_finiteLength {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) ∧
      monomialIdeal k B ≤ monomialIdeal k (lowerBaseFamily (lowerRank B) d) ∧
      ({f : MvPolynomial V k | CommAlg.IntegralOverIdeal (monomialIdeal k B) f} =
        (monomialIdeal k (lowerBaseFamily (lowerRank B) d) : Set (MvPolynomial V k))) ∧
      IsFiniteLength (MvPolynomial V k) (ClosureDifference (k := k) B d) := by
  exact Characterizations.minimal_local_closure_finiteLength (k := k) hB hd hloc

theorem maximal_hole_regularity {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hne : monomialIdeal k B ≠ monomialIdeal k (lowerBaseFamily (lowerRank B) d)) :
    ∃ t : ℕ, (∃ a ∈ Holes (k := k) B d, a.degree = t) ∧
      (∀ b ∈ Holes (k := k) B d, b.degree ≤ t) ∧ d ≤ t ∧
      KoszulRegularity (k := k) B (t + 1) := by
  have hfamily : B ≠ lowerBaseFamily (lowerRank B) d := by
    intro he
    apply hne
    rw [he]
  obtain ⟨t,ht,hmax,hdt,hreg,_⟩ :=
    Characterizations.minimal_local_obstruction (k := k) hB hd hloc hfamily
  exact ⟨t, by simpa only [holes_agree hB hd hloc] using ht,
    by simpa only [holes_agree hB hd hloc] using hmax,
    hdt, (regularity_agrees B (t+1)).mpr hreg⟩

theorem least_power_regularity_difference {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    ∃ r : ℕ, KoszulRegularity (k := k) B r ∧
      IsLeast {q : ℕ | IsPolymatroidalIdeal (maximalPower (k := k) B q)} (r - d) := by
  obtain ⟨r,hreg,hq⟩ :=
    Characterizations.least_polymatroidal_power_eq_regularity_difference (k := k) hB hd hloc
  refine ⟨r,(regularity_agrees B r).mpr hreg,?_⟩
  simpa only [maximalPower_polymatroidal_iff hd] using hq
end PalomarPolymatroidal

namespace PalomarPolymatroidal.Simplicial
open CategoryTheory
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
/-- Closure under taking coordinate subsets. -/
def Downward (F : Finset V → Prop) : Prop := ∀ ⦃s t⦄, t ⊆ s → F s → F t
/-- Actual exterior contraction preserves downward-closed face chains. -/
theorem boundary_mem {F : Finset V → Prop} (hF : Downward F) (i : ℕ)
    (z : Ambient V k) (hz : z ∈ Chains F (i + 1)) : boundary z ∈ Chains F i := by
  exact CommAlg.Simplicial.boundary_mem hF hz
/-- The literal boundary restricted to the actual face-chain submodules. -/
def chainDifferential {F : Finset V → Prop} (hF : Downward F) (i : ℕ) :
    Chains (k := k) F (i + 1) →ₗ[k] Chains (k := k) F i :=
  (boundary.domRestrict (Chains F (i + 1))).codRestrict _
    (fun z => boundary_mem hF i z.val z.property)
/-- The actual restricted exterior differential squares to zero. -/
theorem chainDifferential_comp {F : Finset V → Prop} (hF : Downward F) (i : ℕ) :
    chainDifferential (k := k) hF i ∘ₗ chainDifferential hF (i + 1) = 0 := by
  ext z
  exact CommAlg.Simplicial.boundary_boundary z.val
/-- The actual augmented chain complex, including the empty face in degree zero. -/
def chainComplex {F : Finset V → Prop} (hF : Downward F) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (Chains (k := k) F i))
    (fun i => ModuleCat.ofHom (chainDifferential hF i))
    (fun i => ModuleCat.hom_ext (chainDifferential_comp hF i))
end PalomarPolymatroidal.Simplicial
namespace PalomarPolymatroidal
open Classical Finset CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The residual-monomial Koszul face family is genuinely downward closed. -/
theorem koszulFaces_downward (B : Family V) (a : Exponent V) :
    Simplicial.Downward (koszulFaces B a) := by
  exact CommAlg.Koszul.koszulFaces_downward B a
/-- Dimension of actual homogeneous augmented Koszul-chain homology. -/
def koszulBetti (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k ((Simplicial.chainComplex (k := k) (koszulFaces_downward B a)).homology i)
/-- The ordinary total-degree sum of the actual fine Koszul dimensions. -/
def totalKoszulBetti (B : Family V) (i j : ℕ) : ℕ :=
  ∑ b ∈ (Finsupp.finite_of_degree_eq (σ := V) j).toFinset, koszulBetti (k := k) B b i
/-- All degree-d monomials, except the displayed exponent a. -/
def deletedVeronese (a : Exponent V) : Family V :=
  ((Finsupp.finite_of_degree_eq (σ := V) a.degree).toFinset).erase a
/-- Every earlier homological position is linear and the displayed one has
actual nonzero Koszul homology in a strictly nonlinear degree. -/
def FirstNonlinear (B : Family V) (d r : ℕ) : Prop :=
  (∀ i < r, ∀ b, b.degree ≠ d + i → Simplicial.ExactIn (k := k) (koszulFaces B b) i) ∧
    ∃ b, d + r < b.degree ∧ ¬Simplicial.ExactIn (k := k) (koszulFaces B b) r
private theorem koszulBetti_eq_source (B : Family V) (a : Exponent V) (i : ℕ) :
    koszulBetti (k := k) B a i = CommAlg.Koszul.bettiNumber (k := k) B a i := by
  exact (Characterizations.Strands.bettiNumber_eq_face_homology_finrank B a i).symm
private theorem totalKoszulBetti_eq_source (B : Family V) (i j : ℕ) :
    totalKoszulBetti (k := k) B i j = Characterizations.Strands.totalBettiNumber (k := k) B i j := by
  simp only [totalKoszulBetti, Characterizations.Strands.totalBettiNumber, koszulBetti_eq_source]
private theorem deleted_eq_source (a : Exponent V) :
    deletedVeronese a = Characterizations.deletedVeronese a := by
  ext b
  simp [deletedVeronese, Characterizations.mem_deletedVeronese]
private theorem firstNonlinear_agrees (B : Family V) (d r : ℕ) :
    FirstNonlinear (k := k) B d r ↔ Characterizations.Isolators.FirstNonlinear (k := k) B d r := by
  simp only [FirstNonlinear, Characterizations.Isolators.FirstNonlinear,
    exactIn_iff_betti_zero, Nat.pos_iff_ne_zero]

/-- Proposition4.3: all proper localizations are the unit ideal, the complete
nonlinear fine strand has the stated zero-or-one dimensions, and the total
nonlinear strand has the exact binomial coefficient, including out-of-range zero. -/
theorem deleted_generator_nonlinear_strand (a : Exponent V) (ha : 2 ≤ a.support.card) :
    (∀ U : Finset V, U ⊂ Finset.univ →
      monomialLocalization k (monomialIdeal k (deletedVeronese a)) U = ⊤) ∧
    (∀ i b, b.degree ≠ a.degree + i →
      koszulBetti (k := k) (deletedVeronese a) b i =
        if ∃ T : Finset V, a.support ⊆ T ∧ T.card = i + 1 ∧ b = a + faceExponent T
          then 1 else 0) ∧
    (∀ i, totalKoszulBetti (k := k) (deletedVeronese a) i (a.degree + i + 1) =
      if a.support.card ≤ i + 1 then
        Nat.choose (Fintype.card V - a.support.card) (i + 1 - a.support.card) else 0) ∧
    (∀ i j, j ≠ a.degree + i → j ≠ a.degree + i + 1 →
      totalKoszulBetti (k := k) (deletedVeronese a) i j = 0) := by
  simpa only [deleted_eq_source, koszulBetti_eq_source, totalKoszulBetti_eq_source] using
    (Characterizations.Strands.deleted_generator_nonlinear_strand (k := k) a ha)
/-- Proposition4.7(i): a unique bad localization, all localizations pure,
at the smallest possible degree codimension+2. -/
theorem exists_pure_isolator (U : Finset V) (hm : 2 ≤ U.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card + 2) ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  exact Characterizations.Isolators.exists_pure_isolator (k := k) U hm
/-- Proposition4.7(ii): the unique bad localization fails equigeneration,
at the smallest possible degree codimension+1. -/
theorem exists_mixed_isolator (U : Finset V) (hm : 2 ≤ U.card) (hk : 1 ≤ Uᶜ.card) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B (Uᶜ.card + 1) ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  exact Characterizations.Isolators.exists_mixed_isolator (k := k) U hm hk
/-- Proposition4.7: no unique bad localization can occur below codimension+1
or in degree zero or one. -/
theorem unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U → HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    2 ≤ d ∧ Uᶜ.card + 1 ≤ d := by
  exact Characterizations.Isolators.unique_bad_degree_lower_bound (k := k) hB hd U hbad hgood
/-- Proposition4.7: purity at every localization forces the sharper codimension+2 minimum. -/
theorem pure_unique_bad_degree_lower_bound {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hgood : ∀ R : Finset V, R ≠ U → HasLinearResolution (monomialLocalization k (monomialIdeal k B) R)) :
    Uᶜ.card + 2 ≤ d := by
  exact Characterizations.Isolators.pure_unique_bad_degree_lower_bound (k := k) hB hd hl U hbad hgood
/-- Proposition4.10: every admissible U is the unique bad localization with
exact first nonlinear position min(d-1-codim(U),|U|-1), all localizations pure. -/
theorem exists_sharp_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ) (hd : 2 ≤ d)
    (hk : Uᶜ.card ≤ d - 2) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧ LocallyEquigenerated B ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) ∧
      Equigenerated (localFamily B U) (d - Uᶜ.card) ∧
      FirstNonlinear (k := k) (localFamily B U) (d - Uᶜ.card)
        (min (d - 1 - Uᶜ.card) (U.card - 1)) := by
  simpa only [firstNonlinear_agrees] using
    (Characterizations.Isolators.exists_sharp_isolator (k := k) U hm d hd hk)
/-- Proposition4.10's outer band: its generation test is individually necessary. -/
theorem exists_outer_band_isolator (U : Finset V) (hm : 2 ≤ U.card) (d : ℕ)
    (hd : 2 ≤ d) (hk : Uᶜ.card = d - 1) :
    ∃ B : Family V, B.Nonempty ∧ Equigenerated B d ∧
      (¬ ∃ e, Equigenerated (localFamily B U) e) ∧
      (∀ R, HasLinearResolution (monomialLocalization k (monomialIdeal k B) R) ↔ R ≠ U) := by
  exact Characterizations.Isolators.exists_outer_band_isolator (k := k) U hm d hd hk
end PalomarPolymatroidal

namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- Equation (2.4): actual ideal-integral closure is the intersection of the
ordinary coordinate-prime powers prescribed by the lower rank function. -/
theorem integral_closure_prime_power_factors {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (f : MvPolynomial V k) :
    CommAlg.IntegralOverIdeal (monomialIdeal k B) f ↔
      f ∈ ⨅ U : Finset V, (variableIdeal (k := k) U) ^ lowerRank B U := by
  exact Characterizations.integralClosure_eq_primePower_intersection (k := k) hB hanti hl hd f
/-- Corollary 2.12: polymatroidality is equivalent to local equigeneration
and an actual intersection presentation by ordinary coordinate-prime powers.
Exponent zero permits missing factors, including the empty-set convention. -/
theorem intersection_type_iff {B : Family V} (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ LocallyEquigenerated B ∧
      ∃ e : Finset V → ℕ, monomialIdeal k B =
        ⨅ U : Finset V, (variableIdeal (k := k) U) ^ e U := by
  exact Characterizations.polymatroidal_iff_intersectionType_localEquigenerated (k := k) hB hanti
end PalomarPolymatroidal

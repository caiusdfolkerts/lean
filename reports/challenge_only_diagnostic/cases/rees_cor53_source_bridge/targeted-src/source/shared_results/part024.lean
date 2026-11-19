module
public import graph_foundation.part014
public import shared_results.part023

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedKoszulDiagonal -/
section

/-!
# The minimum-color diagonal is the actual mixed-product Koszul complex

For an arbitrary sequence x of base-ring elements, this identifies the
literal color-m strand of K(x,z;K^|m|) with K(x;product I_c^(m_c)).
The maps use coefficient extraction, inclusion of exterior basis faces,
and the actual signed Koszul differential. All commutative coefficient
rings and homological degree zero are included.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.OrderedKoszulEmbedding FourPapers.FilteredHomology

universe u
variable {C V R : Type u} [Fintype C] [LinearOrder C] [Fintype V] [LinearOrder V]
  [CommRing R]

abbrev ColorVariables := C ⊕ₗ V

def baseColorEmbedding : V ↪o ColorVariables (C := C) (V := V) where
  toFun v := toLex (Sum.inr v)
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.Lex.inr_le_inr_iff

/-- Include a base-variable exterior face in the ordered colored variables.
Fixing the target type explicitly keeps the two order dictionaries aligned. -/
abbrev baseColorFace (p : ℕ) : Set.powersetCard V p ↪
    Set.powersetCard (ColorVariables (C := C) (V := V)) p :=
  face (W := ColorVariables (C := C) (V := V))
    (baseColorEmbedding (C := C) (V := V)) p

def exteriorColor (F : Finset (ColorVariables (C := C) (V := V))) : C →₀ ℕ :=
  faceExponent F.toLeft

@[simp] lemma exteriorColor_degree (F : Finset (ColorVariables (C := C) (V := V))) :
    (exteriorColor F).degree=F.toLeft.card := by
  simp [exteriorColor,faceExponent]

@[simp] lemma exteriorColor_baseFace (p : ℕ) (F : Set.powersetCard V p) :
    exteriorColor (baseColorFace (C := C) (V := V) p F).val=0 := by
  ext c
  simp [exteriorColor,baseColorFace,face,baseColorEmbedding,faceExponent_apply]
  intro v hv h
  cases h

def coloredSequence (x : V → R) : ColorVariables (C := C) (V := V) → MvPolynomial C R :=
  Sum.elim X (fun v => MvPolynomial.C (x v))

def mixedCoefficientLift (I : C → Ideal R) (a : C →₀ ℕ) :
    powerProduct I a →ₗ[R] ↥(coloredIdeal I ^ a.degree) where
  toFun f := ⟨monomial a f.val,monomial_powerProduct_mem_coloredPower I a f.val f.property⟩
  map_add' f g := Subtype.ext (map_add (monomial a) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (monomial a) r f.val)

lemma mixedCoefficientLift_injective (I : C → Ideal R) (a : C →₀ ℕ) :
    Function.Injective (mixedCoefficientLift I a) := by
  intro f g he
  apply Subtype.ext
  have hh := congrArg (fun p : ↥(coloredIdeal I ^ a.degree) => p.val.coeff a) he
  change (monomial a f.val).coeff a = (monomial a g.val).coeff a at hh
  simpa only [coeff_monomial,if_true] using hh

def mixedKoszulMap (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ) :
    (Set.powersetCard V p →₀ powerProduct I a) →ₗ[R]
      (Set.powersetCard (ColorVariables (C := C) (V := V)) p →₀ ↥(coloredIdeal I ^ a.degree)) :=
  coordinates (W := ColorVariables (C := C) (V := V))
    (baseColorEmbedding (C := C) (V := V)) (mixedCoefficientLift I a) p

@[simp] lemma mixedKoszulMap_single (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (F : Set.powersetCard V p) (f : powerProduct I a) :
    mixedKoszulMap I a p (Finsupp.single F f)=
      Finsupp.single (baseColorFace (C := C) (V := V) p F) (mixedCoefficientLift I a f) :=
  coordinates_single _ _ _ _ _

lemma mixedKoszulMap_apply_baseFace (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (z : Set.powersetCard V p →₀ powerProduct I a) (F : Set.powersetCard V p) :
    mixedKoszulMap I a p z (baseColorFace (C := C) (V := V) p F)=mixedCoefficientLift I a (z F) := by
  change Finsupp.mapDomain (baseColorFace (C := C) (V := V) p)
    (Finsupp.mapRange (mixedCoefficientLift I a) (map_zero _) z)
      (baseColorFace (C := C) (V := V) p F)=_
  rw [Finsupp.mapDomain_apply_of_injective (baseColorFace (C := C) (V := V) p).injective]
  rfl

lemma mixedKoszulMap_apply_not_baseFace (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (z : Set.powersetCard V p →₀ powerProduct I a)
    (F : Set.powersetCard (ColorVariables (C := C) (V := V)) p)
    (hF : F ∉ Set.range (baseColorFace (C := C) (V := V) p)) :
    mixedKoszulMap I a p z F=0 :=
  Finsupp.mapDomain_of_notMem_range _ _ hF

def mixedColorKoszulPiece (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ) :
    Submodule R
      (Set.powersetCard (ColorVariables (C := C) (V := V)) p →₀ ↥(coloredIdeal I ^ a.degree)) where
  carrier := {z | ∀ F b, b+exteriorColor F.val≠a → (z F).val.coeff b=0}
  zero_mem' := by simp
  add_mem' hz hw := by intro F b hb; simp [hz F b hb,hw F b hb]
  smul_mem' r z hz := by intro F b hb; simp [hz F b hb]

lemma mixedColorKoszulPiece_no_color (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (z : mixedColorKoszulPiece (V := V) I a p)
    (F : Set.powersetCard (ColorVariables (C := C) (V := V)) p)
    (hF : F.val.toLeft≠∅) : z.val F=0 := by
  apply Subtype.ext
  ext b
  change (z.val F).val.coeff b = 0
  by_cases hb : b+exteriorColor F.val=a
  · have hh := congrArg Finsupp.degree hb
    simp only [map_add,exteriorColor_degree] at hh
    have hp : 0<F.val.toLeft.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
    exact coloredIdeal_power_coeff_below I a.degree (z.val F).val
      (z.val F).property b (by omega)
  · exact z.property F b hb

lemma mixedColorKoszulPiece_pure (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (z : mixedColorKoszulPiece (V := V) I a p)
    (F : Set.powersetCard (ColorVariables (C := C) (V := V)) p)
    (hF : F.val.toLeft=∅) : (z.val F).val=monomial a ((z.val F).val.coeff a) := by
  apply pureColorPiece_eq_monomial
  intro b hb
  apply z.property F b
  simpa only [exteriorColor,hF,faceExponent_empty,add_zero] using hb

lemma baseFace_range_iff (p : ℕ)
    (F : Set.powersetCard (ColorVariables (C := C) (V := V)) p) :
    F∈Set.range (baseColorFace (C := C) (V := V) p) ↔ F.val.toLeft=∅ := by
  constructor
  · rintro ⟨G,rfl⟩
    ext c
    simp [baseColorFace,face,baseColorEmbedding]
    intro v hv h
    cases h
  · intro hF
    have hc : F.val.toRight.card=p := by
      have hh := Finset.card_toLeft_add_card_toRight (u := F.val)
      rw [hF,Finset.card_empty,zero_add,F.property] at hh
      exact hh
    refine ⟨⟨F.val.toRight,hc⟩,?_⟩
    apply Subtype.ext
    have hh := Finset.toLeft_disjSum_toRight (u := F.val)
    rw [hF,Finset.empty_disjSum] at hh
    exact hh

theorem mixedKoszulMap_mem_piece (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ)
    (z : Set.powersetCard V p →₀ powerProduct I a) :
    mixedKoszulMap I a p z ∈ mixedColorKoszulPiece (V := V) I a p := by
  intro F b hb
  by_cases hF : F∈Set.range (baseColorFace (C := C) (V := V) p)
  · obtain ⟨G,rfl⟩ := hF
    rw [mixedKoszulMap_apply_baseFace]
    have hba : a≠b := by
      intro he
      apply hb
      simpa only [exteriorColor_baseFace,add_zero] using he.symm
    change (monomial a (z G).val).coeff b = 0
    rw [coeff_monomial, if_neg hba]
  · rw [mixedKoszulMap_apply_not_baseFace I a p z F hF]
    simp

theorem mixedKoszulMap_range (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ) :
    LinearMap.range (mixedKoszulMap (V := V) I a p)=mixedColorKoszulPiece (V := V) I a p := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    exact mixedKoszulMap_mem_piece I a p z
  · intro z hz
    let f (F : Set.powersetCard V p) : powerProduct I a :=
      ⟨(z (baseColorFace (C := C) (V := V) p F)).val.coeff a,
        coloredIdeal_power_minimal_coeff I a.degree _
          (z (baseColorFace (C := C) (V := V) p F)).property a rfl⟩
    let y : Set.powersetCard V p →₀ powerProduct I a := Finsupp.equivFunOnFinite.symm f
    refine ⟨y,?_⟩
    apply Finsupp.ext
    intro F
    by_cases hF : F∈Set.range (baseColorFace (C := C) (V := V) p)
    · obtain ⟨G,rfl⟩ := hF
      rw [mixedKoszulMap_apply_baseFace]
      apply Subtype.ext
      exact (mixedColorKoszulPiece_pure I a p ⟨z,hz⟩ _
        ((baseFace_range_iff p _).mp ⟨G,rfl⟩)).symm
    · rw [mixedKoszulMap_apply_not_baseFace I a p y F hF]
      exact (mixedColorKoszulPiece_no_color I a p ⟨z,hz⟩ F
        (fun h => hF ((baseFace_range_iff p F).mpr h))).symm

def mixedKoszulDiagonalEquiv (I : C → Ideal R) (a : C →₀ ℕ) (p : ℕ) :
    (Set.powersetCard V p →₀ powerProduct I a) ≃ₗ[R] mixedColorKoszulPiece (V := V) I a p :=
  (LinearEquiv.ofInjective (mixedKoszulMap I a p)
    (coordinates_injective (W := ColorVariables (C := C) (V := V))
      (baseColorEmbedding (C := C) (V := V)) (mixedCoefficientLift I a)
      (mixedCoefficientLift_injective I a) p)).trans
    (LinearEquiv.ofEq _ _ (mixedKoszulMap_range I a p))

@[simp] lemma mixedKoszulDiagonalEquiv_val (I : C → Ideal R)
    (a : C →₀ ℕ) (p : ℕ) (z : Set.powersetCard V p →₀ powerProduct I a) :
    (mixedKoszulDiagonalEquiv (V := V) I a p z).val = mixedKoszulMap I a p z := rfl

theorem mixedKoszulMap_differential (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) (z : Set.powersetCard V (p+1) →₀ powerProduct I a) :
    mixedKoszulMap I a p (coordinateDifferential x (ModuleCat.of R (powerProduct I a)) p z)=
      coordinateDifferential (coloredSequence x)
        (ModuleCat.of (MvPolynomial C R) ↥(coloredIdeal I ^ a.degree)) p
          (mixedKoszulMap I a (p+1) z) := by
  apply differential_commutes (W := ColorVariables (C := C) (V := V))
    (baseColorEmbedding (C := C) (V := V)) (mixedCoefficientLift I a)
  intro v f
  apply Subtype.ext
  change monomial a (x v * f.val) = MvPolynomial.C (x v) * monomial a f.val
  rw [C_mul_monomial]

def mixedColorKoszulDifferential (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) : mixedColorKoszulPiece (V := V) I a (p+1) →ₗ[R] mixedColorKoszulPiece (V := V) I a p :=
  (((coordinateDifferential (coloredSequence x)
    (ModuleCat.of (MvPolynomial C R) ↥(coloredIdeal I ^ a.degree)) p).restrictScalars R).domRestrict
      (mixedColorKoszulPiece (V := V) I a (p+1))).codRestrict _ (by
    intro z
    have hz : z.val ∈ LinearMap.range (mixedKoszulMap (V := V) I a (p+1)) := by
      rw [mixedKoszulMap_range]
      exact z.property
    obtain ⟨y, hy⟩ := hz
    change coordinateDifferential (coloredSequence x)
      (ModuleCat.of (MvPolynomial C R) ↥(coloredIdeal I ^ a.degree)) p z.val ∈ _
    rw [← hy, ← mixedKoszulMap_differential]
    exact mixedKoszulMap_mem_piece I a p _)

@[simp] lemma mixedColorKoszulDifferential_val (I : C → Ideal R)
    (a : C →₀ ℕ) (x : V → R) (p : ℕ)
    (z : mixedColorKoszulPiece (V := V) I a (p+1)) :
    (mixedColorKoszulDifferential I a x p z).val =
      coordinateDifferential (coloredSequence x)
        (ModuleCat.of (MvPolynomial C R) ↥(coloredIdeal I ^ a.degree)) p z.val := rfl

@[simp] theorem mixedKoszulDiagonalEquiv_differential (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) (z : Set.powersetCard V (p+1) →₀ powerProduct I a) :
    mixedKoszulDiagonalEquiv (V := V) I a p
        (coordinateDifferential x (ModuleCat.of R (powerProduct I a)) p z)=
      mixedColorKoszulDifferential I a x p (mixedKoszulDiagonalEquiv (V := V) I a (p+1) z) := by
  apply Subtype.ext
  rw [mixedKoszulDiagonalEquiv_val, mixedColorKoszulDifferential_val,
    mixedKoszulDiagonalEquiv_val]
  exact mixedKoszulMap_differential I a x p z

lemma mixedColorKoszulDifferential_comp (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) :
    (mixedColorKoszulDifferential I a x p).comp
      (mixedColorKoszulDifferential I a x (p+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (mixedColorKoszulDifferential I a x p
    (mixedColorKoszulDifferential I a x (p+1) z)).val = 0
  rw [mixedColorKoszulDifferential_val, mixedColorKoszulDifferential_val]
  exact LinearMap.congr_fun (coordinateDifferential_comp (coloredSequence x)
    (ModuleCat.of (MvPolynomial C R) ↥(coloredIdeal I ^ a.degree)) p) z.val

instance mixedColorKoszulPiece_addCommGroup (I : C → Ideal R)
    (a : C →₀ ℕ) (p : ℕ) :
    AddCommGroup ↥(mixedColorKoszulPiece (V := V) I a p) :=
  Submodule.addCommGroup (R := R)
    (M := Set.powersetCard (ColorVariables (C := C) (V := V)) p →₀
      ↥(coloredIdeal I ^ a.degree)) (mixedColorKoszulPiece (V := V) I a p)

instance mixedColorKoszulPiece_module (I : C → Ideal R)
    (a : C →₀ ℕ) (p : ℕ) :
    Module R ↥(mixedColorKoszulPiece (V := V) I a p) :=
  Submodule.module (R := R)
    (M := Set.powersetCard (ColorVariables (C := C) (V := V)) p →₀
      ↥(coloredIdeal I ^ a.degree)) (mixedColorKoszulPiece (V := V) I a p)

/-- This is the actual color-m subcomplex of the full polynomial Koszul
complex of K^|m|. Its terms were defined intrinsically by coefficients. -/
def mixedColorKoszulComplex (I : C → Ideal R) (a : C →₀ ℕ) (x : V → R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun p : ℕ => ModuleCat.of R
    (mixedColorKoszulPiece (C := C) (V := V) (R := R) I a p))
    (fun p => ModuleCat.ofHom (mixedColorKoszulDifferential I a x p))
    (fun p => ModuleCat.hom_ext (mixedColorKoszulDifferential_comp I a x p))

@[simp] lemma mixedColorKoszulComplex_d (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) :
    (mixedColorKoszulComplex I a x).d (p+1) p =
      ModuleCat.ofHom (mixedColorKoszulDifferential I a x p) := by
  simp only [mixedColorKoszulComplex, ChainComplex.of_d]

/-- The chain isomorphism, with all variable actions and exterior signs
preserved. In particular it includes homological degree zero. -/
def mixedKoszulDiagonalIso (I : C → Ideal R) (a : C →₀ ℕ) (x : V → R) :
    coordinateComplex x (ModuleCat.of R (powerProduct I a)) ≅
      mixedColorKoszulComplex I a x :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (mixedKoszulDiagonalEquiv (V := V) I a p).toModuleIso) (by
      intro p q hpq
      obtain rfl : p=q+1 := hpq.symm
      rw [coordinateComplex_d, mixedColorKoszulComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (mixedKoszulDiagonalEquiv_differential I a x q z).symm)

def mixedKoszulHomologyDiagonalIso (I : C → Ideal R) (a : C →₀ ℕ)
    (x : V → R) (p : ℕ) :
    (familyCoefficientComplex x (ModuleCat.of R (powerProduct I a))).homology p ≅
      (mixedColorKoszulComplex I a x).homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) p).mapIso
    (coordinateComplexIso x (ModuleCat.of R (powerProduct I a)) ≪≫
      mixedKoszulDiagonalIso I a x)

section Polynomial
variable {k : Type u} [CommRing k]

/-- The diagonal really computes derived Tor of the mixed product over the
original polynomial ring. No field or coefficient-domain assumption remains. -/
def mixedProductTorDiagonalIso (I : C → Ideal (MvPolynomial V k)) (a : C →₀ ℕ)
    (p : ℕ) :
    (((Tor (ModuleCat (MvPolynomial V k)) p).obj
      (ModuleCat.of (MvPolynomial V k) (powerProduct I a))).obj
        (residueCoefficientModule (V := V) (k := k))) ≅
      (mixedColorKoszulComplex I a (MvPolynomial.X : V → MvPolynomial V k)).homology p := by
  by_cases hk : Nontrivial k
  · letI := hk
    exact (finitePolynomialTorPaperIso p
        (ModuleCat.of (MvPolynomial V k) (powerProduct I a))).symm ≪≫
      finitePolynomialTorIso p (ModuleCat.of (MvPolynomial V k) (powerProduct I a)) ≪≫
      mixedKoszulHomologyDiagonalIso I a (MvPolynomial.X : V → MvPolynomial V k) p
  · have hs : Subsingleton k := by
      rcases subsingleton_or_nontrivial k with hs | hn
      · exact hs
      · exact (hk hn).elim
    letI := hs
    exact zeroCoefficientModuleIso _ _

end Polynomial
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem55Transfer -/
section

/-! # Actual mixed-ideal Betti transfer in the original monomial order

The canonical Gröbner data are constructed from the literal ideals, rather
than supplied as extra hypotheses.  Generation for the monomial multi-Rees
algebra is the separate diagonal theorem.  This file supplies its complete
filtered consequence, including the original multi-Rees generation clause.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n))
  (M : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
    powerProduct (coloredIdeals (k := K) n E) a)


def canonicalMixedGenerators (a : ULift.{u} (Fin r) →₀ ℕ) :
    Set (MvPolynomial (FiniteVariable.{u} n) K) :=
  ((powerProduct J a : Ideal (MvPolynomial (FiniteVariable.{u} n) K)) :
    Set (MvPolynomial (FiniteVariable.{u} n) K))

theorem canonicalMixedGroebner (a : ULift.{u} (Fin r) →₀ ℕ) :
    M.IsGroebnerBasis (canonicalMixedGenerators n J a) (powerProduct J a) :=
  M.isGroebnerBasis_self (powerProduct J a)

theorem canonicalMixedUnitLeading (a : ULift.{u} (Fin r) →₀ ℕ) :
    ∀ f ∈ canonicalMixedGenerators n J a, f ≠ 0 → IsUnit (M.leadingCoeff f) :=
  fun f _ hf => M.isUnit_leadingCoeff.mpr hf

def mixedPowerQuotientData (a : ULift.{u} (Fin r) →₀ ℕ) :
    QuotientGroebnerData (FiniteVariable.{u} n) K where
  order := M
  ideal := powerProduct J a
  generators := canonicalMixedGenerators n J a
  groebner := canonicalMixedGroebner n M J a
  unitLeading := canonicalMixedUnitLeading n M J a
  family := mixedRowPowerFamily n E a
  standard b := by
    have hh := monomial_mem_initial_iff_not_standard M (powerProduct J a)
      (canonicalMixedGenerators n J a) (canonicalMixedGroebner n M J a)
      (canonicalMixedUnitLeading n M J a) b
    change monomial b (1 : K) ∈ FourPapers.initialIdeal M (powerProduct J a) ↔ _ at hh
    rw [hinit a, ← mixedRowPowerFamily_ideal n E K a, monomial_mem_iff] at hh
    simpa only [QuotientAllowed, not_not] using (not_congr hh).symm

theorem powerProduct_unit (c : ULift.{u} (Fin r)) :
    powerProduct J (Finsupp.single c 1) = J c := by
  simpa only [pow_one] using powerProduct_single J c 1

/-- The first-color premise concerns exactly the original ideal `J c`. -/
theorem mixedPowerQuotientData_unit_ideal (c : ULift.{u} (Fin r)) :
    (mixedPowerQuotientData n E M J hinit (Finsupp.single c 1)).ideal = J c :=
  powerProduct_unit n J c

variable (hJ : ∀ c, (J c).IsHomogeneous
  (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

include hJ in
theorem homogeneousMixedProduct (a : ULift.{u} (Fin r) →₀ ℕ) :
    (powerProduct J a).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))) := by
  unfold powerProduct
  apply Finset.prod_induction
    (fun c => (J c) ^ a c)
    (fun P : Ideal (MvPolynomial (FiniteVariable.{u} n) K) => P.IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
  · intro P Q hP hQ
    exact hP.mul hQ
  · simpa only [Ideal.one_eq_top] using
      Ideal.IsHomogeneous.top (weightedHomogeneousSubmodule K
        (fun _ : FiniteVariable.{u} n => (1 : ℕ)))
  · intro c hc
    induction a c with
    | zero => simpa only [pow_zero, Ideal.one_eq_top] using
        Ideal.IsHomogeneous.top (weightedHomogeneousSubmodule K
          (fun _ : FiniteVariable.{u} n => (1 : ℕ)))
    | succ s ih => rw [pow_succ]; exact ih.mul (hJ c)

def mixedPowerBettiNumber (a : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) : ℕ :=
  ordinaryIdealBettiNumber (mixedPowerQuotientData n E M J hinit a)
    (homogeneousMixedProduct n J hJ a) p q

def mixedMonomialBettiNumber (a : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) : ℕ :=
  ordinaryMonomialBettiNumber (k := K) (mixedRowPowerFamily n E a) q p

def coordinateUnitDegrees : Set (ULift.{u} (Fin r) →₀ ℕ) :=
  Set.range (fun c => Finsupp.single c 1)

local notation "G" => canonicalMixedGenerators n J
local notation "hG" => canonicalMixedGroebner n M J
local notation "hu" => canonicalMixedUnitLeading n M J
local notation "I" => coloredIdeals (k := K) n E

theorem mixed_unit_ordered_lifts
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (ha : a ∈ coordinateUnitDegrees (r := r)) (p : ℕ) :
    MixedTransfer.PowerOrderedCoordinateLifts M J G hG hu a p := by
  obtain ⟨c, rfl⟩ := ha
  have hh := actualIdeal_ordered_lifts_of_betti_eq
    (mixedPowerQuotientData n E M J hinit (Finsupp.single c 1))
    (homogeneousMixedProduct n J hJ (Finsupp.single c 1)) (hβ c) p
  apply (MixedTransfer.nativePowerOrderedLifts_iff M J G hG hu (Finsupp.single c 1) p).mp
  simpa only [ActualIdealOrderedLifts, MixedTransfer.NativePowerOrderedLifts,
    MixedTransfer.nativePowerCoefficientBasis, actualIdealCoefficientBasis,
    actualIdealDegree, mixedPowerQuotientData] using hh

variable (hgen : Algebra.adjoin K
  (selectedHomologyClasses
    (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := K) n E))
    (MixedTransfer.Auxiliary.initialSelectedPiece M J
      (coloredIdeals (k := K) n E) hinit
      (canonicalMixedGenerators n J) (canonicalMixedGroebner n M J)
      (canonicalMixedUnitLeading n M J)
      (coordinateUnitDegrees (r := r)))) = ⊤)

include hgen in
theorem mixed_all_ordered_lifts
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) :
    ActualIdealOrderedLifts (mixedPowerQuotientData n E M J hinit a) p := by
  have hh := MixedTransfer.all_mixed_ordered_coordinate_lifts M J G hG hu I hinit
    (coordinateUnitDegrees (r := r)) hgen
    (mixed_unit_ordered_lifts n E M J hinit hJ hβ) a p
  have hn := (MixedTransfer.nativePowerOrderedLifts_iff M J G hG hu a p).mpr hh
  simpa only [ActualIdealOrderedLifts, MixedTransfer.NativePowerOrderedLifts,
    MixedTransfer.nativePowerCoefficientBasis, actualIdealCoefficientBasis,
    actualIdealDegree, mixedPowerQuotientData] using hn

include hgen in
theorem mixed_betti_equality_of_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) :
    mixedPowerBettiNumber n E M J hinit hJ a p q =
      mixedMonomialBettiNumber (K := K) n E a p q :=
  ordinaryIdealBettiNumber_eq_monomial_of_ordered_lifts
    (mixedPowerQuotientData n E M J hinit a) (homogeneousMixedProduct n J hJ a)
    (mixed_all_ordered_lifts n E M J hinit hJ hgen hβ a) p q

include hgen in
theorem mixed_generation_of_monomial_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) :
    Algebra.adjoin K
      (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
        (MixedTransfer.Auxiliary.selectedPiece M J G hG hu
          (coordinateUnitDegrees (r := r)))) = ⊤ :=
  MixedTransfer.mixed_homology_generated_of_selected_lifts M J G hG hu I hinit
    (coordinateUnitDegrees (r := r)) hgen
    (mixed_unit_ordered_lifts n E M J hinit hJ hβ)

/-- The integer grading is the proved regrading of the actual derived Tor. -/
def mixedIntegerPowerBettiNumber (a : ULift.{u} (Fin r) →₀ ℕ)
    (p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber (mixedPowerQuotientData n E M J hinit a)
    (homogeneousMixedProduct n J hJ a) p q

theorem mixedMonomialIdeal_homogeneous (a : ULift.{u} (Fin r) →₀ ℕ) :
    (monomialIdeal K (mixedRowPowerFamily n E a)).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro f ⟨b,hb,rfl⟩
  exact ⟨Finsupp.weight (fun _ : FiniteVariable.{u} n => (1 : ℕ)) b,
    isWeightedHomogeneous_monomial _ b (1 : K) rfl⟩

/-- The comparison number is also a homogeneous submodule of actual Tor,
for the literal monomial mixed ideal. -/
def mixedIntegerMonomialBettiNumber (a : ULift.{u} (Fin r) →₀ ℕ)
    (p : ℕ) (q : ℤ) : ℕ :=
  ordinaryIntegerIdealBettiNumber
    (canonicalQuotientGroebnerData M (monomialIdeal K (mixedRowPowerFamily n E a)))
    (mixedMonomialIdeal_homogeneous (K := K) n E a) p q

@[simp] theorem mixedIntegerPowerBettiNumber_nat
    (a : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ a p (q : ℤ) =
      mixedPowerBettiNumber n E M J hinit hJ a p q :=
  ordinaryIntegerIdealBettiNumber_nat _ _ p q

@[simp] theorem mixedIntegerMonomialBettiNumber_nat
    (a : ULift.{u} (Fin r) →₀ ℕ) (p q : ℕ) :
    mixedIntegerMonomialBettiNumber (K := K) n E M a p (q : ℤ) =
      mixedMonomialBettiNumber (K := K) n E a p q := by
  unfold mixedIntegerMonomialBettiNumber
  rw [ordinaryIntegerIdealBettiNumber_nat]
  exact canonicalMonomialBettiNumber_eq M _
    (mixedMonomialIdeal_homogeneous (K := K) n E a) q p

include hgen in
theorem mixed_integer_betti_equality_of_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E M a p q := by
  by_cases hq : 0 ≤ q
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq
    rw [← he, mixedIntegerPowerBettiNumber_nat, mixedIntegerMonomialBettiNumber_nat]
    exact mixed_betti_equality_of_generation n E M J hinit hJ hgen hβ a p q.toNat
  · have hn : q < 0 := lt_of_not_ge hq
    unfold mixedIntegerPowerBettiNumber mixedIntegerMonomialBettiNumber
    rw [ordinaryIntegerIdealBettiNumber_negative _ _ p q hn,
      ordinaryIntegerIdealBettiNumber_negative _ _ p q hn]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem55 -/
section

/-! # Theorem 5.5: all mixed powers and multi-Rees generation

The only input Betti equalities are those of the original ideals, whose
canonical unit-color presentations are proved literally equal to them.
The monomial generation assertion is supplied by the minimum-color
diagonal construction, not added as a hypothesis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n)) (hE : ColoredLatticeClosed n E)
  (M : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
    powerProduct (coloredIdeals (k := K) n E) a)
  (hJ : ∀ c, (J c).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))


local notation "G" => canonicalMixedGenerators n J
local notation "hG" => canonicalMixedGroebner n M J
local notation "hu" => canonicalMixedUnitLeading n M J
local notation "I" => coloredIdeals (k := K) n E

include hE in
/-- **Theorem 5.5, Betti assertion.** Every mixed exponent, every
homological degree, and every integer internal degree are retained. -/
theorem theorem55_betti
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E M a p q :=
  mixed_integer_betti_equality_of_generation n E M J hinit hJ
    (mixedReesHomology_generated_in_unit_colors hE M J hinit G hG hu) hβ a p q

include hE in
/-- **Theorem 5.5, generation assertion.** The literal multi-Rees Koszul
homology of the original ideals is generated in coordinate-unit colors. -/
theorem theorem55_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) :
    Algebra.adjoin K
      (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
        (MixedTransfer.Auxiliary.selectedPiece M J G hG hu
          (coordinateUnitDegrees (r := r)))) = ⊤ :=
  mixed_generation_of_monomial_generation n E M J hinit hJ
    (mixedReesHomology_generated_in_unit_colors hE M J hinit G hG hu) hβ

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.theorem55_betti
#print axioms FourPapers.Sublattice.theorem55_generation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrdinaryBettiPresentationIndependence -/
section

/-! # Presentation and exterior orientation do not alter ordinary Betti numbers -/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]

/-- Identity on polynomial variables, with the signed exterior coordinate
map retained, compares arbitrary presentations and arbitrary orientations. -/
theorem ordinaryIdealBettiNumber_presentation
    (l₁ l₂ : LinearOrder V) (P Q : QuotientGroebnerData V K)
    (hP : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (hQ : Q.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))
    (hI : P.ideal=Q.ideal) (p q : ℕ) :
    (haveI := l₁; ordinaryIdealBettiNumber P hP p q)=
      (haveI := l₂; ordinaryIdealBettiNumber Q hQ p q) := by
  have he : P.ideal.map (MvPolynomial.rename (Equiv.refl V)).toRingHom=Q.ideal := by
    change P.ideal.map (MvPolynomial.rename id).toRingHom = Q.ideal
    rw [MvPolynomial.rename_id]
    change Ideal.map (RingHom.id (MvPolynomial V K)) P.ideal = Q.ideal
    simpa only [Ideal.map_id] using hI
  exact @ordinaryIdealBettiNumber_rename K V V _ _ l₁ _ l₂ P Q hP hQ
    (Equiv.refl V) he p q

theorem monomialFamily_homogeneous (B : Family V) :
    (monomialIdeal K B).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))) := by
  apply Ideal.homogeneous_span
  rintro f ⟨a,ha,rfl⟩
  exact ⟨Finsupp.weight (fun _ : V => (1 : ℕ)) a,
    isWeightedHomogeneous_monomial _ a (1 : K) rfl⟩

theorem ordinaryMonomialBettiNumber_presentation
    (l₁ l₂ : LinearOrder V) (M : MonomialOrder V) (B C : Family V)
    (hI : monomialIdeal K B=monomialIdeal K C) (q p : ℕ) :
    (haveI := l₁; ordinaryMonomialBettiNumber (k := K) B q p)=
      (haveI := l₂; ordinaryMonomialBettiNumber (k := K) C q p) := by
  have hB := monomialFamily_homogeneous (K := K) B
  have hC := monomialFamily_homogeneous (K := K) C
  calc
    _ = (haveI := l₁; ordinaryIdealBettiNumber
        (canonicalQuotientGroebnerData M (monomialIdeal K B)) hB p q) := by
      letI := l₁
      exact (canonicalMonomialBettiNumber_eq M B hB q p).symm
    _ = (haveI := l₂; ordinaryIdealBettiNumber
        (canonicalQuotientGroebnerData M (monomialIdeal K C)) hC p q) :=
      ordinaryIdealBettiNumber_presentation l₁ l₂ _ _ hB hC hI p q
    _ = _ := by
      letI := l₂
      exact canonicalMonomialBettiNumber_eq M C hC q p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedFirstPowerPremise -/
section

/-!
# The individual first-power premise in Theorem 5.5

The coordinate-unit mixed product is the literal original ideal. These
comparisons identify its Betti numbers with those of a canonical presentation
of that ideal, and identify the corresponding monomial product with `I_c`.
The last equivalence includes every integer internal degree: negative pieces
vanish in the actual derived Tor, rather than being discarded from the premise.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n))
  (M : MonomialOrder (FiniteVariable.{u} n))
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
    powerProduct (coloredIdeals (k := K) n E) a)
  (hJ : ∀ c, (J c).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))

/-- The unit-color product has exactly the Betti table of the supplied `J_c`. -/
theorem mixedPowerBettiNumber_unit (c : ULift.{u} (Fin r)) (p q : ℕ) :
    mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      ordinaryIdealBettiNumber (canonicalQuotientGroebnerData M (J c)) (hJ c) p q := by
  apply ordinaryIdealBettiNumber_presentation
    (finiteVariableLinearOrder n) (finiteVariableLinearOrder n)
  exact mixedPowerQuotientData_unit_ideal n E M J hinit c

include M in
/-- The monomial unit-color product is `I_c`, with its actual ideal Tor. -/
theorem mixedMonomialBettiNumber_unit (c : ULift.{u} (Fin r)) (p q : ℕ) :
    mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q =
      ordinaryMonomialBettiNumber (k := K) (finiteRowFamily n (E c.down)) q p := by
  have hI : monomialIdeal K (mixedRowPowerFamily n E (Finsupp.single c 1)) =
      monomialIdeal K (finiteRowFamily n (E c.down)) := by
    rw [mixedRowPowerFamily_ideal, powerProduct_unit]
    change finiteSublatticeIdeal n (k := K) (E c.down) = _
    exact finiteSublatticeIdeal_eq_monomialIdeal n (E c.down)
  exact ordinaryMonomialBettiNumber_presentation
    (finiteVariableLinearOrder n) (finiteVariableLinearOrder n) M _ _ hI q p

/-- The finite family of first-color hypotheses is precisely `β(J_c)=β(I_c)`. -/
theorem mixed_first_power_premise_iff :
    (∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) ↔
    (∀ c p q, ordinaryIdealBettiNumber
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p q =
      ordinaryMonomialBettiNumber (k := K) (finiteRowFamily n (E c.down)) q p) := by
  simp_rw [mixedPowerBettiNumber_unit n E M J hinit hJ,
    mixedMonomialBettiNumber_unit n E M]

/-- Passing from natural to integer internal degrees loses no hypothesis.
The left side is the paper's individual first-power Betti equality. -/
theorem mixed_first_power_integer_iff :
    (∀ c p (q : ℤ), ordinaryIntegerIdealBettiNumber
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p q =
      integerMonomialTorBettiNumber (K := K) M (finiteRowFamily n (E c.down)) p q) ↔
    (∀ c p q, mixedPowerBettiNumber n E M J hinit hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) := by
  rw [mixed_first_power_premise_iff n E M J hinit hJ]
  constructor
  · intro h c p q
    exact (ordinaryIntegerIdealBettiNumber_nat
      (canonicalQuotientGroebnerData M (J c)) (hJ c) p q).symm.trans
      ((h c p (q : ℤ)).trans (integerMonomialTorBettiNumber_nat
        (K := K) M (finiteRowFamily n (E c.down)) p q))
  · intro h c p q
    by_cases hq : 0 ≤ q
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact (ordinaryIntegerIdealBettiNumber_nat
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p a).trans
        ((h c p a).trans (integerMonomialTorBettiNumber_nat
          (K := K) M (finiteRowFamily n (E c.down)) p a).symm)
    · have hneg : q < 0 := lt_of_not_ge hq
      exact (ordinaryIntegerIdealBettiNumber_negative
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p q hneg).trans
        (integerMonomialTorBettiNumber_negative
          (K := K) M (finiteRowFamily n (E c.down)) p q hneg).symm

/-- Theorem 5.5 with the literal individual-ideal premise in all integer degrees. -/
theorem theorem55_betti_of_individual_integer_premise
    (hE : ColoredLatticeClosed n E)
    (hβ : ∀ c p (q : ℤ), ordinaryIntegerIdealBettiNumber
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p q =
      integerMonomialTorBettiNumber (K := K) M (finiteRowFamily n (E c.down)) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hinit hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E M a p q :=
  theorem55_betti n E hE M J hinit hJ
    ((mixed_first_power_integer_iff n E M J hinit hJ).mp hβ) a p q

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedReesTorComparison -/
section

/-!
# The literal multi-Rees algebra and its derived Tor

The coefficientwise presentation used by mixed propagation is identified with
`multiReesAlgebra J` by unchanged polynomial values. This identification
preserves multiplication, each color coefficient, and the actual Koszul
differential. The resulting homology equivalence is an algebra equivalence.
The homologically graded complex computes Mathlib's derived Tor for the
original polynomial-ring action.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CategoryTheory
open IntegerFiltered.MultiplicativeFiltration
open scoped TensorProduct

universe u
variable {K V C : Type u} [CommRing K] [Nontrivial K]
  [Fintype V] [LinearOrder V] [Fintype C] [DecidableEq C]
  (J : C → Ideal (MvPolynomial V K))

/-- The conventional subalgebra of `S[t_c]`, regarded as a `K`-algebra. -/
abbrev LiteralMixedRees := ((multiReesAlgebra J).restrictScalars K)

instance literalMixedPolynomialAlgebra :
    Algebra (MvPolynomial V K) (LiteralMixedRees J) :=
  Subalgebra.algebra (multiReesAlgebra J)

instance literalMixedPolynomialScalarTower :
    IsScalarTower K (MvPolynomial V K) (LiteralMixedRees J) where
  smul_assoc a b x := Subtype.ext (smul_assoc a b x.val)

/-- The original polynomial action is its usual constant-color inclusion. -/
def literalMixedPolynomialAction : MvPolynomial V K →+* LiteralMixedRees J :=
  algebraMap (MvPolynomial V K) (LiteralMixedRees J)

@[simp] theorem literalMixedPolynomialAction_val (f : MvPolynomial V K) :
    (literalMixedPolynomialAction J f).val = MvPolynomial.C f := rfl

def literalMixedBaseVariable (v : V) : LiteralMixedRees J :=
  literalMixedPolynomialAction J (MvPolynomial.X v)

/-- The presentation equivalence preserves the actual degree-zero variables. -/
@[simp] theorem mixedCoefficientEquiv_baseVariable (v : V) :
    MixedTransfer.coefficientReesMultiEquiv J (MixedTransfer.idealReesBaseVariable J v) =
      literalMixedBaseVariable J v := by
  apply Subtype.ext
  rfl

/-- Literal color monomials with coefficients in the prescribed mixed ideal. -/
def literalMixedSingle (a : C →₀ ℕ) (f : MixedTransfer.idealPowerPiece J a) :
    LiteralMixedRees J :=
  ⟨MvPolynomial.monomial a f.val,
    (monomial_mem_multiReesAlgebra J a f.val).mpr f.property⟩

/-- Each color degree is preserved, including the coordinate-unit degrees. -/
theorem mixedCoefficientEquiv_single (a : C →₀ ℕ)
    (f : MixedTransfer.idealPowerPiece J a) :
    MixedTransfer.coefficientReesMultiEquiv J (MixedTransfer.idealReesSingle J a f) =
      literalMixedSingle J a f := by
  apply Subtype.ext
  rfl

/-- The actual tensor-exterior Koszul algebra on the standard multi-Rees ring. -/
def literalMixedKoszulDGA :
    ParityDifferential K (LiteralMixedRees J ⊗[K] Simplicial.Ambient V K) :=
  TensorExteriorKoszul.parityDifferential (literalMixedBaseVariable J)

/-- This is multiplicative on the nose; the exterior factor is unchanged. -/
def mixedLiteralTensorEquiv : MixedTransfer.IdealReesKoszul J ≃ₐ[K]
    (LiteralMixedRees J ⊗[K] Simplicial.Ambient V K) :=
  TensorKoszulCoefficientEquiv.algebra (MixedTransfer.coefficientReesMultiEquiv J)

/-- Both the coefficient color and the exterior degree are retained. -/
theorem mixedLiteralTensorEquiv_single (a : C →₀ ℕ)
    (f : MixedTransfer.idealPowerPiece J a) (F : Finset V) :
    mixedLiteralTensorEquiv J
        (MixedTransfer.idealReesSingle J a f ⊗ₜ[K] Simplicial.basis F) =
      literalMixedSingle J a f ⊗ₜ[K] Simplicial.basis F := by
  change MixedTransfer.coefficientReesMultiEquiv J
      (MixedTransfer.idealReesSingle J a f) ⊗ₜ[K] Simplicial.basis F = _
  rw [mixedCoefficientEquiv_single]

theorem mixedLiteralTensorEquiv_differential (z : MixedTransfer.IdealReesKoszul J) :
    mixedLiteralTensorEquiv J ((MixedTransfer.idealReesKoszulDGA J).d z) =
      (literalMixedKoszulDGA J).d (mixedLiteralTensorEquiv J z) :=
  TensorKoszulCoefficientEquiv.differential
    (MixedTransfer.coefficientReesMultiEquiv J)
    (MixedTransfer.idealReesBaseVariable J) (literalMixedBaseVariable J)
    (mixedCoefficientEquiv_baseVariable J) z

/-- The homology algebra in Theorem 5.5 is the homology algebra of the
literal multi-Rees Koszul DGA, with its actual multiplication. -/
def mixedLiteralHomologyEquiv :
    (MixedTransfer.idealReesKoszulDGA J).Homology ≃ₐ[K]
      (literalMixedKoszulDGA J).Homology :=
  ParityDifferential.homologyEquiv _ _ (mixedLiteralTensorEquiv J)
    (mixedLiteralTensorEquiv_differential J)

/-- Selected color submodules transport by the unchanged coefficient values. -/
theorem mixedLiteralHomologyEquiv_selected
    (W : Submodule K (MixedTransfer.IdealReesKoszul J)) :
    mixedLiteralHomologyEquiv J ''
        selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J) W =
      selectedHomologyClasses (literalMixedKoszulDGA J)
        (W.map (mixedLiteralTensorEquiv J).toLinearMap) := by
  apply ParityDifferential.homologyEquiv_classesFrom
  intro x
  constructor
  · rintro ⟨y,hy,he⟩
    exact (mixedLiteralTensorEquiv J).injective he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- Algebra generation transports to the literal multi-Rees algebra with
exactly the same selected color degrees. -/
theorem literalMixed_homology_generated
    (W : Submodule K (MixedTransfer.IdealReesKoszul J))
    (hgen : Algebra.adjoin K
      (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J) W) = ⊤) :
    Algebra.adjoin K (selectedHomologyClasses (literalMixedKoszulDGA J)
      (W.map (mixedLiteralTensorEquiv J).toLinearMap)) = ⊤ :=
  adjoin_eq_top_of_algEquiv (mixedLiteralHomologyEquiv J) _ _
    (mixedLiteralHomologyEquiv_selected J W).subset hgen

/-- The DGA differential is the original polynomial-variable action. -/
theorem literalMixedDifferential_eq_polynomial :
    (literalMixedKoszulDGA J).d =
      TensorExteriorKoszul.differential (K := K) (M := LiteralMixedRees J)
        (MvPolynomial.X : V → MvPolynomial V K) := by
  change TensorExteriorKoszul.differential (K := K) (R := LiteralMixedRees J)
    (M := LiteralMixedRees J) (literalMixedBaseVariable J) = _
  unfold TensorExteriorKoszul.differential
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  apply LinearMap.ext
  intro a
  exact (Algebra.smul_def (MvPolynomial.X v) a).symm

/-- The homological grading is exterior cardinality, with the actual
polynomial-variable differential. -/
abbrev LiteralMixedKoszulComplex :=
  TensorExteriorKoszul.complex (K := K) (M := LiteralMixedRees J)
    (MvPolynomial.X : V → MvPolynomial V K)

theorem literalMixedKoszulComplex_differential_val (p : ℕ)
    (x : TensorExteriorKoszul.piece (K := K) (V := V)
      (M := LiteralMixedRees J) (p+1)) :
    (TensorExteriorKoszul.pieceDifferential
      (MvPolynomial.X : V → MvPolynomial V K) p x).val =
        (literalMixedKoszulDGA J).d x.val := by
  rw [TensorExteriorKoszul.pieceDifferential_val, literalMixedDifferential_eq_polynomial]

/-- In every homological degree, this is Mathlib's actual derived
`Tor^S(S[J_c t_c], K)` for the standard coefficient-ring action.
The next equivalence also identifies Mathlib's `Tor'` convention, which
resolves the residue module in the first slot. -/
def mixedDerivedTorIso (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).obj
      (((Tor (ModuleCat (MvPolynomial V K)) p).obj
        (ModuleCat.of (MvPolynomial V K) (LiteralMixedRees J))).obj
          (residueCoefficientModule (V := V) (k := K))) ≅
      (LiteralMixedKoszulComplex J).homology p :=
  TensorExteriorKoszul.polynomialTorIso p

/-- The equivalent convention that resolves the residue module in the
first slot, as in the displayed `Tor^S(K, S[J_c t_c])` of Theorem 5.5. -/
def mixedDerivedLeftTorIso (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).obj
      (((Tor' (ModuleCat (MvPolynomial V K)) p).obj
        (residueCoefficientModule (V := V) (k := K))).obj
          (ModuleCat.of (MvPolynomial V K) (LiteralMixedRees J))) ≅
      (LiteralMixedKoszulComplex J).homology p :=
  (ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).mapIso
    (torPrimeSwapIso p (residueCoefficientModule (V := V) (k := K))
      (ModuleCat.of (MvPolynomial V K) (LiteralMixedRees J))) ≪≫
    mixedDerivedTorIso J p

end FourPapers.Sublattice

namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n))

/-- The standalone generation assertion of Theorem 5.5 on the standard
multi-Rees algebra itself, with the unchanged coordinate-unit color pieces. -/
theorem theorem55_literal_monomial_generation (hE : ColoredLatticeClosed n E) :
    Algebra.adjoin K
      (selectedHomologyClasses (literalMixedKoszulDGA (coloredIdeals (k := K) n E))
        ((actualMixedUnitColorPiece (E := E) (k := K)).map
          (mixedLiteralTensorEquiv (coloredIdeals (k := K) n E)).toLinearMap)) = ⊤ :=
  literalMixed_homology_generated _ _ (theorem55_monomial_generation hE)

/-- The deformed multi-Rees generation assertion with precisely the
individual-ideal Betti premise over every integer internal degree. -/
theorem theorem55_literal_generation
    (hE : ColoredLatticeClosed n E)
    (M : MonomialOrder (FiniteVariable.{u} n))
    (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (hinit : ∀ a, FourPapers.initialIdeal M (powerProduct J a) =
      powerProduct (coloredIdeals (k := K) n E) a)
    (hJ : ∀ c, (J c).IsHomogeneous
      (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ c p (q : ℤ), ordinaryIntegerIdealBettiNumber
        (canonicalQuotientGroebnerData M (J c)) (hJ c) p q =
      integerMonomialTorBettiNumber (K := K) M (finiteRowFamily n (E c.down)) p q) :
    Algebra.adjoin K (selectedHomologyClasses (literalMixedKoszulDGA J)
      ((MixedTransfer.Auxiliary.selectedPiece M J
        (canonicalMixedGenerators n J) (canonicalMixedGroebner n M J)
        (canonicalMixedUnitLeading n M J) (coordinateUnitDegrees (r := r))).map
          (mixedLiteralTensorEquiv J).toLinearMap)) = ⊤ :=
  literalMixed_homology_generated J _
    (theorem55_generation n E hE M J hinit hJ
      ((mixed_first_power_integer_iff n E M J hinit hJ).mp hβ))

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedFiniteTransfer -/
section

/-! # Full finite and nested mixed transfer: Corollaries 5.6 and 5.7

The initial-ideal premises are respectively the single colored identity
and the individual nested identities. All mixed identities used in the
Betti and generation conclusions are derived from those premises.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open IntegerFiltered.MultiplicativeFiltration
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {K : Type u} [Field K] {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n)) (hE : ColoredLatticeClosed n E)
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (hJ : ∀ c, (J c).IsHomogeneous
    (weightedHomogeneousSubmodule K (fun _ : FiniteVariable.{u} n => (1 : ℕ))))


section Finite
variable (M : MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)))
  (hinit : FourPapers.initialIdeal M (coloredDeformedIdeal J) =
    finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E))
local notation "o" => coloredRestrictedOrder M
local notation "hi" => corollary56_initial J E M hE hinit

/-- The all-mixed Betti conclusion of Corollary 5.6. -/
theorem corollary56_betti
    (hβ : ∀ c p q, mixedPowerBettiNumber n E o J hi hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E o J hi hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E o a p q :=
  theorem55_betti n E hE o J hi hJ hβ a p q

/-- The coordinate-unit generation conclusion of Corollary 5.6. -/
theorem corollary56_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E o J hi hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) :
    Algebra.adjoin K (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
      (MixedTransfer.Auxiliary.selectedPiece o J (canonicalMixedGenerators n J)
        (canonicalMixedGroebner n o J) (canonicalMixedUnitLeading n o J)
        (coordinateUnitDegrees (r := r)))) = ⊤ :=
  theorem55_generation n E hE o J hi hJ hβ
end Finite

section Nested
variable (M : MonomialOrder (FiniteVariable.{u} n)) (hmono : Monotone J)
  (hinit : ∀ c, FourPapers.initialIdeal M (J c) = coloredIdeals (k := K) n E c)
local notation "hi" => corollary57_original_initial J E M hE hmono hinit

/-- The all-mixed Betti conclusion of Corollary 5.7. -/
theorem corollary57_betti
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hi hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q)
    (a : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerPowerBettiNumber n E M J hi hJ a p q =
      mixedIntegerMonomialBettiNumber (K := K) n E M a p q :=
  theorem55_betti n E hE M J hi hJ hβ a p q

/-- The coordinate-unit generation conclusion of Corollary 5.7. -/
theorem corollary57_generation
    (hβ : ∀ c p q, mixedPowerBettiNumber n E M J hi hJ (Finsupp.single c 1) p q =
      mixedMonomialBettiNumber (K := K) n E (Finsupp.single c 1) p q) :
    Algebra.adjoin K (selectedHomologyClasses (MixedTransfer.idealReesKoszulDGA J)
      (MixedTransfer.Auxiliary.selectedPiece M J (canonicalMixedGenerators n J)
        (canonicalMixedGroebner n M J) (canonicalMixedUnitLeading n M J)
        (coordinateUnitDegrees (r := r)))) = ⊤ :=
  theorem55_generation n E hE M J hi hJ hβ
end Nested
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary56_betti
#print axioms FourPapers.Sublattice.corollary56_generation
#print axioms FourPapers.Sublattice.corollary57_betti
#print axioms FourPapers.Sublattice.corollary57_generation
#print axioms FourPapers.Sublattice.mixed_first_power_integer_iff
#print axioms FourPapers.Sublattice.theorem55_betti_of_individual_integer_premise
#print axioms FourPapers.Sublattice.mixedLiteralHomologyEquiv
#print axioms FourPapers.Sublattice.mixedDerivedTorIso
#print axioms FourPapers.Sublattice.mixedDerivedLeftTorIso
#print axioms FourPapers.Sublattice.theorem55_literal_monomial_generation
#print axioms FourPapers.Sublattice.theorem55_literal_generation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedStrictSupportBetti -/
section

/-! # Mixed Betti numbers and the positive-binomial formula

The first equality below is a dimension formula for the actual mixed ideal,
including the empty product. Grouping its chains by their strict supports
gives the multivariate positive-binomial formula following (5.2). A missing
color is assigned coefficient zero when all color multiplicities are positive.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg.Polymatroid CommAlg.Koszul
open FourPapers.MultichainCounting FourPapers.ColoredMultiplicityCounting
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}

@[simp] theorem chainBaseShift_degree {M : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) M) :
    (chainBaseShift E w).degree = M*d := by
  simp [chainBaseShift, finiteRowExponent_degree]

/-- Fine-degree Betti numbers of the literal mixed-product ideal. -/
theorem mixedBetti_admissible {k : Type u} [Field k]
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    bettiNumber (k := k) (mixedRowPowerFamily n E m) a p =
      ∑ w : MixedAdmissibleChain (E := E) m a,
        quotientBettiNumber (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-chainBaseShift E w.val) p := by
  letI (w : MixedAdmissibleChain (E := E) m a) : Module.Finite k
      (quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
        (a-chainBaseShift E w.val) p) :=
    Module.Finite.equiv (quotientPaperGradedTorIso (k := k)
      (sameColorChainCoefficientFamily E w.val) (a-chainBaseShift E w.val) p).toLinearEquiv
  unfold bettiNumber
  rw [← (gradedTorIso (k := k) (mixedRowPowerFamily n E m) a p).toLinearEquiv.finrank_eq,
    (paperGradedTorIso (k := k) (mixedRowPowerFamily n E m) a p).toLinearEquiv.finrank_eq,
    (corollary72_natural (k := k) hE m a p).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro w _
  rw [← (quotientPaperGradedTorIso (k := k)
    (sameColorChainCoefficientFamily E w.val) (a-chainBaseShift E w.val) p).toLinearEquiv.finrank_eq]
  exact (quotientBettiNumber_eq_homology (k := k) _ _ _).symm

/-- Remove precisely the ordinary degree of the chain's monomial product. -/
def ordinaryMixedAdmissibleChainEquiv (m : ULift.{u} (Fin r) →₀ ℕ) (q : ℕ) :
    (Σ a : OrdinaryFineIndex (FiniteVariable.{u} n) (m.degree*d+q),
      MixedAdmissibleChain (E := E) m a.val) ≃
        (MixedColorChain (E := E) m × OrdinaryFineIndex (FiniteVariable.{u} n) q) where
  toFun x := ⟨⟨x.2.val,x.2.property.1⟩,⟨x.1.val-chainBaseShift E x.2.val,by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le x.2.property.2)
    rw [map_add,chainBaseShift_degree,x.1.property] at h
    omega⟩⟩
  invFun x := ⟨⟨x.2.val+chainBaseShift E x.1.val,by
    rw [map_add,chainBaseShift_degree,x.2.property]
    omega⟩,⟨x.1.val,x.1.property,by
      intro v
      simp only [Finsupp.add_apply]
      omega⟩⟩
  left_inv x := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact tsub_add_cancel_of_le x.2.property.2
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact add_tsub_cancel_right _ _

/-- Equation (5.2) summed in an ordinary degree, including zero exponents. -/
theorem ordinaryMixedBetti_chain_sum {k : Type u} [Field k]
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k) (mixedRowPowerFamily n E m) (m.degree*d+q) p =
      ∑ w : MixedColorChain (E := E) m,
        ordinaryQuotientBettiNumber (k := k) (sameColorChainCoefficientFamily E w.val) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  simp_rw [mixedBetti_admissible hE,ordinaryQuotientBettiNumber_eq_sum]
  rw [← Fintype.sum_sigma (f := fun x :
    Σ a : OrdinaryFineIndex (FiniteVariable.{u} n) (m.degree*d+q),
      MixedAdmissibleChain (E := E) m a.val =>
        quotientBettiNumber (k := k) (sameColorChainCoefficientFamily E x.2.val)
          (x.1.val-chainBaseShift E x.2.val) p)]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (ordinaryMixedAdmissibleChainEquiv (E := E) m q) _ _ (fun _ => rfl)

/-- The normalized negative ordinary degrees are all zero. -/
theorem ordinaryMixedBetti_zero_below {k : Type u} [Field k]
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ) (Q p : ℕ)
    (hQ : Q < m.degree*d) :
    ordinaryMonomialBettiNumber (k := k) (mixedRowPowerFamily n E m) Q p = 0 := by
  rw [ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [mixedBetti_admissible hE]
  apply Finset.sum_eq_zero
  intro w _
  have h := Finsupp.degree_mono w.property.2
  rw [chainBaseShift_degree,a.property] at h
  omega

def coloredSupportColor (a : coloredFamily n E) : ULift.{u} (Fin r) :=
  ULift.up (a.val 0)

def coloredStrictSupportCoefficientFamily (s : StrictSupport (coloredFamily n E)) :
    Family (FiniteVariable.{u} n) :=
  s.val.biUnion fun a => finitePredecessorFamily n (E (a.val 0))
    (fun i => a.val i.succ)

lemma sameColorChainCoefficientFamily_support {M : ℕ} (hM : 0 < M)
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) M) :
    sameColorChainCoefficientFamily E w =
      coloredStrictSupportCoefficientFamily (tupleSupport hM w) := by
  ext g
  constructor
  · intro hg
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_biUnion.mpr ⟨w.val i,(tupleSupport_mem hM w _).mpr ⟨i,rfl⟩,hi⟩
  · intro hg
    obtain ⟨a,ha,hg⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨i,rfl⟩ := (tupleSupport_mem hM w a).mp ha
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hg⟩

lemma chainColorCount_apply {M : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) M)
    (c : ULift.{u} (Fin r)) :
    chainColorCount E w c = tupleColorCount (coloredSupportColor.{u} (E := E)) w c := by
  rw [tupleColorCount_sum]
  simp only [chainColorCount,Finsupp.finsetSum_apply,Finsupp.single_apply,coloredSupportColor]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- The paper's exact color condition is the literal multiplicity condition. -/
def mixedColorTupleEquiv (m : ULift.{u} (Fin r) →₀ ℕ) :
    MixedColorChain (E := E) m ≃
      {w : MonotoneTuple (coloredFamily n E) m.degree //
        ∀ c, tupleColorCount (coloredSupportColor.{u} (E := E)) w c = m c} where
  toFun w := ⟨w.val,by intro c; rw [← chainColorCount_apply,w.property]⟩
  invFun w := ⟨w.val,by ext c; rw [chainColorCount_apply]; exact w.property c⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The strict support contributes only if it contains every color. -/
def coloredStrictSupportBettiCoefficient {k : Type u} [Field k] (q p : ℕ)
    (s : StrictSupport (coloredFamily n E)) : ℕ :=
  if Function.Surjective (fun a : s.val => coloredSupportColor.{u} (E := E) a.val) then
    ordinaryQuotientBettiNumber (k := k) (coloredStrictSupportCoefficientFamily s) q p
  else 0

def coloredStrictSupportBinomialDegree (s : StrictSupport (coloredFamily n E))
    (c : ULift.{u} (Fin r)) : ℕ :=
  Fintype.card {a : s.val // coloredSupportColor.{u} (E := E) a.val = c}-1

/-- Prescribed-color counting transported along the total degree equality.
The length change is proved with abstract finite types, before specializing
it to a colored lattice and its homology coefficients. -/
private theorem coloredTuple_sum_finsuppDegree
    {A C : Type*} [Fintype A] [Fintype C] [PartialOrder A]
    (color : A → C) (m : C →₀ ℕ) (hm : ∀ c, 0 < m c)
    (hM : 0 < m.degree) (f : StrictSupport A → ℕ) :
    (∑ w : {w : MonotoneTuple A m.degree // ∀ c, tupleColorCount color w c = m c},
      f (tupleSupport hM w.val)) =
      ∑ s : StrictSupport A,
        (∏ c, (m c-1).choose (Fintype.card {a : s.val // color a.val = c}-1)) *
          (if Function.Surjective (fun a : s.val => color a.val) then f s else 0) := by
  have he := Finsupp.degree_eq_sum m
  generalize hlen : m.degree = M at hM ⊢
  have hlen' : M = ∑ c, m c := hlen.symm.trans he
  clear hlen
  subst M
  exact sum_by_colored_strict_support color m hm hM f

/-- Reindex prescribed-color tuples while every finite carrier is abstract.
The concrete lattice is introduced only after the sum identity is proved. -/
private theorem coloredTuple_sum_equiv
    {A C W : Type*} [Fintype A] [Fintype C] [Fintype W] [PartialOrder A]
    (color : A → C) (m : C →₀ ℕ) (hm : ∀ c, 0 < m c) (hM : 0 < m.degree)
    (e : W ≃ {w : MonotoneTuple A m.degree // ∀ c, tupleColorCount color w c = m c})
    (f : StrictSupport A → ℕ) :
    (∑ w : W, f (tupleSupport hM (e w).val)) =
      ∑ s : StrictSupport A,
        (if Function.Surjective (fun a : s.val => color a.val) then f s else 0) *
          ∏ c, (m c-1).choose (Fintype.card {a : s.val // color a.val = c}-1) := by
  have heq := Fintype.sum_equiv e
    (fun w : W => f (tupleSupport hM (e w).val))
    (fun w : {w : MonotoneTuple A m.degree // ∀ c, tupleColorCount color w c = m c} =>
      f (tupleSupport hM w.val)) (fun _ => rfl)
  refine heq.trans ((coloredTuple_sum_finsuppDegree color m hm hM f).trans ?_)
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency true in
/-- The abstract counting identity applied to the actual colored chains. -/
private theorem mixedColorChain_sum_strictSupport
    (m : ULift.{u} (Fin r) →₀ ℕ) (hm : ∀ c, 0 < m c)
    (hM : 0 < m.degree) (f : StrictSupport (coloredFamily n E) → ℕ) :
    (∑ w : MixedColorChain (E := E) m, f (tupleSupport hM w.val)) =
      ∑ s : StrictSupport (coloredFamily n E),
        (if Function.Surjective (fun a : s.val => coloredSupportColor.{u} (E := E) a.val)
          then f s else 0) *
          ∏ c, (m c-1).choose (coloredStrictSupportBinomialDegree s c) := by
  have h := coloredTuple_sum_equiv (coloredSupportColor.{u} (E := E)) m hm hM
    (mixedColorTupleEquiv (E := E) m) f
  simp only [mixedColorTupleEquiv, Equiv.coe_fn_mk] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro s _
  simp only [coloredStrictSupportBinomialDegree, ← Nat.card_eq_fintype_card]
  split_ifs <;> rfl

/-- The exact positive-binomial formula following equation (5.2). -/
theorem mixed_positive_binomial_formula {k : Type u} [Field k]
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ)
    (hm : ∀ c, 0 < m c) (hM : 0 < m.degree) (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := k) (mixedRowPowerFamily n E m) (m.degree*d+q) p =
      ∑ s : StrictSupport (coloredFamily n E),
        coloredStrictSupportBettiCoefficient (k := k) q p s *
          ∏ c, (m c-1).choose (coloredStrictSupportBinomialDegree s c) := by
  rw [ordinaryMixedBetti_chain_sum hE]
  simp_rw [sameColorChainCoefficientFamily_support hM]
  exact mixedColorChain_sum_strictSupport m hm hM
    (fun s => ordinaryQuotientBettiNumber (k := k) (coloredStrictSupportCoefficientFamily s) q p)

/-- A single rational multivariate polynomial, valid for every positive
exponent vector, with the actual quotient Betti numbers as basis coefficients. -/
def normalizedMixedBettiPolynomial {k : Type u} [Field k] (q p : ℕ) :
    MvPolynomial (ULift.{u} (Fin r)) ℚ :=
  MultivariatePositiveBinomial.polynomial
    (coloredStrictSupportBettiCoefficient (k := k) (E := E) q p)
    coloredStrictSupportBinomialDegree

theorem mixed_positive_polynomial {k : Type u} [Field k]
    (hE : ColoredLatticeClosed n E) (m : ULift.{u} (Fin r) →₀ ℕ)
    (hm : ∀ c, 0 < m c) (hM : 0 < m.degree) (q p : ℕ) :
    MvPolynomial.eval (fun c => (m c : ℚ))
      (normalizedMixedBettiPolynomial (k := k) (E := E) q p) =
        (ordinaryMonomialBettiNumber (k := k)
          (mixedRowPowerFamily n E m) (m.degree*d+q) p : ℚ) := by
  rw [normalizedMixedBettiPolynomial,
    MultivariatePositiveBinomial.polynomial_eval _ _ m hm,
    mixed_positive_binomial_formula hE m hm hM]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.ordinaryMixedBetti_chain_sum
#print axioms FourPapers.Sublattice.mixed_positive_binomial_formula
#print axioms FourPapers.Sublattice.mixed_positive_polynomial

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixCharacteristic -/
section

/-! # Characteristic independence of mixed prefix products

The coefficient quotients are the actual same-color predecessor colons.
Their equality with the original chain colons is proved by divisibility,
and the change of exterior orientation is an explicit signed chain map.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

theorem quotientBettiNumber_eq_of_contains {k V : Type u} [Field k]
    [Fintype V] [LinearOrder V] {B C : Family V}
    (h : ∀ α,Contains B α ↔ Contains C α) (α : Exponent V) (p : ℕ) :
    quotientBettiNumber (k := k) B α p=quotientBettiNumber (k := k) C α p := by
  rw [quotientBettiNumber_eq_homology,quotientBettiNumber_eq_homology]
  exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
    (quotientHomogeneousIsoOfContains h α)).toLinearEquiv.finrank_eq

variable {d N r : ℕ} {E : Finset (FiniteTuple (UnitIntervalRows d N))}
local notation "n" => UnitIntervalRows d N

theorem unitInterval_coefficient_betti_field_independent_reoriented
    (K L : Type u) [Field K] [Field L] (hE : UnitIntervalFacetFamily E)
    {m : ℕ} (w : FiniteMultichain n E m)
    (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    quotientBettiNumber (k := K) (finiteChainCoefficientFamily n w) α p=
      quotientBettiNumber (k := L) (finiteChainCoefficientFamily n w) α p := by
  exact unitInterval_coefficient_betti_field_independent K L hE w α p

theorem initialColumnPrefix_coefficient_field_independent
    (K L : Type u) [Field K] [Field L] (hE : UnitIntervalFacetFamily E)
    (c : Fin r → ℕ) {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n)
      (coloredFamily n (initialColumnPrefixes E c)) m)
    (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    quotientBettiNumber (k := K) (sameColorChainCoefficientFamily (initialColumnPrefixes E c) w) α p=
      quotientBettiNumber (k := L) (sameColorChainCoefficientFamily (initialColumnPrefixes E c) w) α p := by
  rw [quotientBettiNumber_eq_of_contains (initialColumnPrefix_chain_contains c w hE),
    quotientBettiNumber_eq_of_contains (initialColumnPrefix_chain_contains c w hE)]
  exact unitInterval_coefficient_betti_field_independent_reoriented K L hE
    (initialColumnPrefix_baseChain c w) α p

/-- Fine Betti tables of every mixed monomial prefix product are
independent of the field, with zero multiplicities and the empty product included. -/
theorem initialColumnPrefix_mixed_fine_field_independent
    (K L : Type u) [Field K] [Field L] (hE : UnitIntervalFacetFamily E)
    (c : Fin r → ℕ) (hc : Monotone c) (m : ULift.{u} (Fin r) →₀ ℕ)
    (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    bettiNumber (k := K) (mixedRowPowerFamily n (initialColumnPrefixes E c) m) α p=
      bettiNumber (k := L) (mixedRowPowerFamily n (initialColumnPrefixes E c) m) α p := by
  rw [mixedBetti_admissible (initialColumnPrefixes_colored hE c hc),
    mixedBetti_admissible (initialColumnPrefixes_colored hE c hc)]
  apply Finset.sum_congr rfl
  intro w hw
  exact initialColumnPrefix_coefficient_field_independent K L hE c w.val _ p

/-- The ordinary mixed tables inherit the same characteristic independence. -/
theorem initialColumnPrefix_mixed_ordinary_field_independent
    (K L : Type u) [Field K] [Field L] (hE : UnitIntervalFacetFamily E)
    (c : Fin r → ℕ) (hc : Monotone c) (m : ULift.{u} (Fin r) →₀ ℕ)
    (q p : ℕ) :
    ordinaryMonomialBettiNumber (k := K) (mixedRowPowerFamily n (initialColumnPrefixes E c) m) q p=
      ordinaryMonomialBettiNumber (k := L) (mixedRowPowerFamily n (initialColumnPrefixes E c) m) q p := by
  rw [ordinaryMonomialBettiNumber_eq_sum,ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_congr rfl
  intro α hα
  exact initialColumnPrefix_mixed_fine_field_independent K L hE c hc m α.val p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixIntegerCharacteristic -/
section

/-! # Integer ordinary degrees in the mixed prefix comparison -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open CategoryTheory CommAlg.Koszul
universe u
variable {K : Type u} [Field K] {d N r : ℕ}
  {E : Finset (FiniteTuple (UnitIntervalRows d N))}
local notation "n" => UnitIntervalRows d N
variable (hE : UnitIntervalFacetFamily E) (c : Fin r → ℕ) (hc : Monotone c)

include hE hc in
theorem initialColumnPrefix_mixed_integer_monomial_field_independent
    (prefixOrder : MonomialOrder (FiniteVariable.{u} n))
    (L : Type u) [Field L] (m : ULift.{u} (Fin r) →₀ ℕ) (p : ℕ) (q : ℤ) :
    mixedIntegerMonomialBettiNumber (K := K) n (initialColumnPrefixes E c) prefixOrder m p q=
      mixedIntegerMonomialBettiNumber (K := L) n (initialColumnPrefixes E c) prefixOrder m p q := by
  by_cases hq : 0≤q
  · have he : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hq
    rw [← he,mixedIntegerMonomialBettiNumber_nat,mixedIntegerMonomialBettiNumber_nat]
    exact initialColumnPrefix_mixed_ordinary_field_independent K L hE c hc m q.toNat p
  · have hn : q < 0 := lt_of_not_ge hq
    have hK : mixedIntegerMonomialBettiNumber (K := K) n
        (initialColumnPrefixes E c) prefixOrder m p q = 0 :=
      ordinaryIntegerIdealBettiNumber_negative
        (canonicalQuotientGroebnerData prefixOrder
          (monomialIdeal K (mixedRowPowerFamily n (initialColumnPrefixes E c) m)))
        (mixedMonomialIdeal_homogeneous (K := K) n (initialColumnPrefixes E c) m) p q hn
    have hL : mixedIntegerMonomialBettiNumber (K := L) n
        (initialColumnPrefixes E c) prefixOrder m p q = 0 :=
      ordinaryIntegerIdealBettiNumber_negative
        (canonicalQuotientGroebnerData prefixOrder
          (monomialIdeal L (mixedRowPowerFamily n (initialColumnPrefixes E c) m)))
        (mixedMonomialIdeal_homogeneous (K := L) n (initialColumnPrefixes E c) m) p q hn
    exact hK.trans hL.symm

include hE hc in
/-- The finest field-independence statement also retains every integer
multidegree. A negative coordinate gives the proved zero submodule of the
actual derived Tor, rather than a missing case in the grading. -/
theorem initialColumnPrefix_mixed_integer_fine_field_independent
    (L : Type u) [Field L] (m : ULift.{u} (Fin r) →₀ ℕ)
    (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    Module.finrank K (mixedProductIntegerGradedTor (k := K)
      (E := initialColumnPrefixes E c) m α p) =
    Module.finrank L (mixedProductIntegerGradedTor (k := L)
      (E := initialColumnPrefixes E c) m α p) := by
  change Module.finrank K (paperIntegerGradedTor (k := K)
      (mixedRowPowerFamily n (initialColumnPrefixes E c) m) α p) =
    Module.finrank L (paperIntegerGradedTor (k := L)
      (mixedRowPowerFamily n (initialColumnPrefixes E c) m) α p)
  by_cases hα : ∀ v, 0 ≤ α v
  · obtain ⟨a, rfl⟩ := (integerExponent_exists_iff α).mpr hα
    rw [paperIntegerGradedTor_nat, paperIntegerGradedTor_nat]
    let B := mixedRowPowerFamily n (initialColumnPrefixes E c) m
    have hK : Module.finrank K (paperGradedTor (k := K) B a p) =
        bettiNumber (k := K) B a p :=
      ((paperGradedTorIso (k := K) B a p).symm ≪≫
        gradedTorIso (k := K) B a p).toLinearEquiv.finrank_eq
    have hL : Module.finrank L (paperGradedTor (k := L) B a p) =
        bettiNumber (k := L) B a p :=
      ((paperGradedTorIso (k := L) B a p).symm ≪≫
        gradedTorIso (k := L) B a p).toLinearEquiv.finrank_eq
    exact hK.trans ((initialColumnPrefix_mixed_fine_field_independent
      K L hE c hc m a p).trans hL.symm)
  · obtain ⟨v, hv⟩ : ∃ v, α v < 0 := by
      simpa only [not_forall, not_le] using hα
    rw [paperIntegerGradedTor_negative _ _ _ hv,
      paperIntegerGradedTor_negative _ _ _ hv]
    simp


end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.initialColumnPrefix_mixed_integer_monomial_field_independent
#print axioms FourPapers.Sublattice.initialColumnPrefix_mixed_integer_fine_field_independent

#check FourPapers.Sublattice.initialColumnPrefix_mixed_integer_monomial_field_independent

end
end
end


end

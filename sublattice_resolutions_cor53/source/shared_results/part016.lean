module
public import graph_foundation.part012
public import shared_results.part015

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesAuxiliaryPieces -/
section

/-! # Literal powers inside the actual Rees Koszul algebra -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer

open Classical CommAlg FourPapers.Sublattice MvPolynomial
open scoped TensorProduct

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))
  (I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (powerProduct J s) = powerProduct I s)
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

namespace Auxiliary

def auxiliaryPiece (s : C →₀ ℕ) : Submodule K (IdealReesKoszul J) :=
  Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' {a | a.1.1 = s})

def selectedPiece (U : Set (C →₀ ℕ)) : Submodule K (IdealReesKoszul J) :=
  Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) '' {a | a.1.1 ∈ U})

def initialAuxiliaryPiece (s : C →₀ ℕ) : Submodule K (IdealReesKoszul I) :=
  Submodule.span K ((initialReesKoszulBasis m J I hinit G hG hu) '' {a | a.1.1 = s})

def initialSelectedPiece (U : Set (C →₀ ℕ)) : Submodule K (IdealReesKoszul I) :=
  Submodule.span K ((initialReesKoszulBasis m J I hinit G hG hu) '' {a | a.1.1 ∈ U})

end Auxiliary

abbrev IdealPowerKoszul (s : C →₀ ℕ) := idealPowerPiece J s ⊗[K] Simplicial.Ambient V K

def idealPowerKoszulBasis (s : C →₀ ℕ) :
    Module.Basis (NonstandardIndex m ((powerProduct J s)) × Finset V) K (IdealPowerKoszul J s) :=
  (groebnerPowerBasis J m G hG hu s).tensorProduct Simplicial.basis

def powerKoszulInclusion (s : C →₀ ℕ) : IdealPowerKoszul J s →ₗ[K] IdealReesKoszul J :=
  TensorProduct.map (idealReesSingle J s) (LinearMap.id : Simplicial.Ambient V K →ₗ[K] _)

def powerKoszulProjection (s : C →₀ ℕ) : IdealReesKoszul J →ₗ[K] IdealPowerKoszul J s :=
  TensorProduct.map
    (coefficientAt (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s)
    (LinearMap.id : Simplicial.Ambient V K →ₗ[K] _)

theorem powerKoszulProjection_inclusion (s : C →₀ ℕ) (x : IdealPowerKoszul J s) :
    powerKoszulProjection J s (powerKoszulInclusion J s x) = x := by
  have he : (powerKoszulProjection J s).comp (powerKoszulInclusion J s) = LinearMap.id := by
    apply TensorProduct.ext'
    intro a z
    change powerKoszulProjection J s (powerKoszulInclusion J s (a ⊗ₜ[K] z)) = a ⊗ₜ[K] z
    simp only [powerKoszulProjection, powerKoszulInclusion, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    change (AddMonoidAlgebra.single s a.val).coeff s = a.val
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  exact LinearMap.congr_fun he x

theorem powerKoszulInclusion_injective (s : C →₀ ℕ) : Function.Injective (powerKoszulInclusion J s) := by
  intro x y h
  have he := congrArg (powerKoszulProjection J s) h
  simpa only [powerKoszulProjection_inclusion] using he

theorem powerKoszulInclusion_basis (s : C →₀ ℕ)
    (a : NonstandardIndex m ((powerProduct J s)) × Finset V) :
    powerKoszulInclusion J s (idealPowerKoszulBasis m J G hG hu s a) =
      groebnerReesKoszulBasis m J G hG hu (⟨s, a.1⟩, a.2) := by
  simp only [idealPowerKoszulBasis, groebnerReesKoszulBasis,
    Module.Basis.tensorProduct_apply', powerKoszulInclusion,
    TensorProduct.map_tmul, LinearMap.id_apply, groebnerPowerBasis_apply,
    groebnerReesBasis_apply]
  rfl

/-- The selected auxiliary component is exactly the image of the tensor
Koszul module of the literal ideal power. -/
theorem auxiliaryPiece_eq_range (s : C →₀ ℕ) :
    Auxiliary.auxiliaryPiece m J G hG hu s = LinearMap.range (powerKoszulInclusion J s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨⟨t, a⟩, F⟩, ht, rfl⟩
    change t = s at ht
    subst t
    exact ⟨idealPowerKoszulBasis m J G hG hu s (a, F), powerKoszulInclusion_basis m J G hG hu s (a, F)⟩
  · rintro x ⟨y, rfl⟩
    have hy := (idealPowerKoszulBasis m J G hG hu s).mem_span y
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [powerKoszulInclusion_basis]
        exact Submodule.subset_span ⟨(⟨s, a.1⟩, a.2), rfl, rfl⟩
    | zero => simpa only [map_zero] using (Auxiliary.auxiliaryPiece m J G hG hu s).zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using
        (Auxiliary.auxiliaryPiece m J G hG hu s).add_mem ihx ihy
    | smul r x hx ih => simpa only [map_smul] using
        (Auxiliary.auxiliaryPiece m J G hG hu s).smul_mem r ih

def idealPowerKoszulDifferential (s : C →₀ ℕ) : Module.End K (IdealPowerKoszul J s) :=
  TensorExteriorKoszul.differential (K := K) (R := MvPolynomial V K)
    (M := idealPowerPiece J s) (MvPolynomial.X : V → MvPolynomial V K)

theorem baseVariable_mul_single (s : C →₀ ℕ) (v : V) (a : idealPowerPiece J s) :
    idealReesBaseVariable J v * idealReesSingle J s a =
      idealReesSingle J s ((MvPolynomial.X v : MvPolynomial V K) • a) := by
  apply Subtype.ext
  change (AddMonoidAlgebra.single 0 (MvPolynomial.X v : MvPolynomial V K) :
      AddMonoidAlgebra (MvPolynomial V K) (C →₀ ℕ)) * AddMonoidAlgebra.single s a.val =
    AddMonoidAlgebra.single s (MvPolynomial.X v * a.val)
  rw [AddMonoidAlgebra.single_mul_single, zero_add]

theorem powerKoszulInclusion_d (s : C →₀ ℕ) (x : IdealPowerKoszul J s) :
    (idealReesKoszulDGA J).d (powerKoszulInclusion J s x) =
      powerKoszulInclusion J s (idealPowerKoszulDifferential J s x) := by
  have he : (idealReesKoszulDGA J).d.comp (powerKoszulInclusion J s) =
      (powerKoszulInclusion J s).comp (idealPowerKoszulDifferential J s) := by
    apply TensorProduct.ext'
    intro a z
    change (idealReesKoszulDGA J).d (powerKoszulInclusion J s (a ⊗ₜ[K] z)) =
      powerKoszulInclusion J s (idealPowerKoszulDifferential J s (a ⊗ₜ[K] z))
    rw [powerKoszulInclusion, TensorProduct.map_tmul, LinearMap.id_apply]
    change TensorExteriorKoszul.differential (idealReesBaseVariable J)
        (idealReesSingle J s a ⊗ₜ[K] z) = _
    rw [TensorExteriorKoszul.differential_tmul]
    change _ = powerKoszulInclusion J s
      (TensorExteriorKoszul.differential (MvPolynomial.X : V → MvPolynomial V K) (a ⊗ₜ[K] z))
    rw [TensorExteriorKoszul.differential_tmul, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change (idealReesBaseVariable J v * idealReesSingle J s a) ⊗ₜ[K] _ =
      powerKoszulInclusion J s ((MvPolynomial.X v • a) ⊗ₜ[K] _)
    rw [powerKoszulInclusion, TensorProduct.map_tmul, LinearMap.id_apply, baseVariable_mul_single]
  exact LinearMap.congr_fun he x

end FourPapers.MixedTransfer

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedKoszulEmbedding -/
section

/-! # Actual Koszul coordinate maps along ordered variable embeddings

The map includes the exact exterior signs. Coefficient modules and their
scalar rings may differ; the required relation is the literal intertwining
of each variable action.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.OrderedKoszulEmbedding
open Classical CategoryTheory CommAlg.Koszul

universe u
variable {K R S V W M N : Type u} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]
  [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  [Module K M] [Module K N] [IsScalarTower K R M] [IsScalarTower K S N]

def face (e : V ↪o W) (p : ℕ) : Set.powersetCard V p ↪ Set.powersetCard W p where
  toFun F := ⟨F.val.map e.toEmbedding,by simpa using F.property⟩
  inj' F G he := Subtype.ext (Finset.map_injective e.toEmbedding (congrArg Subtype.val he))

theorem eraseSign (e : V ↪o W) (F : Finset V) (v : V) :
    TauCeti.ExteriorAlgebra.basisEraseSign (e v) (F.map e.toEmbedding)=
      TauCeti.ExteriorAlgebra.basisEraseSign v F := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt]
  congr 1
  have he : (F.map e.toEmbedding).filter (fun w => w<e v)=
      (F.filter (fun w => w<v)).map e.toEmbedding := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hlt⟩
      exact ⟨z,⟨hz,e.lt_iff_lt.mp hlt⟩,rfl⟩
    · rintro ⟨z,⟨hz,hlt⟩,rfl⟩
      exact ⟨⟨z,hz,rfl⟩,e.lt_iff_lt.mpr hlt⟩
  rw [he,Finset.card_map]

def memberEquiv (e : V ↪o W) (F : Finset V) : F ≃ F.map e.toEmbedding :=
  Finset.equivMap e.toEmbedding F

@[simp] theorem memberEquiv_val (e : V ↪o W) (F : Finset V) (v : F) :
    (memberEquiv e F v).val=e v.val := rfl

theorem face_erase (e : V ↪o W) (p : ℕ) (F : Set.powersetCard V (p+1))
    (v : F.val) :
    face e p (eraseIndex F v)=eraseIndex (face e (p+1) F) (memberEquiv e F.val v) := by
  apply Subtype.ext
  change (F.val.erase v.val).map e.toEmbedding=(F.val.map e.toEmbedding).erase (e v.val)
  ext w
  simp only [Finset.mem_map,Finset.mem_erase]
  constructor
  · rintro ⟨z,⟨hne,hz⟩,rfl⟩
    exact ⟨fun h => hne (e.injective h),⟨z,hz,rfl⟩⟩
  · rintro ⟨hne,z,hz,rfl⟩
    exact ⟨z,⟨fun h => hne (congrArg e h),hz⟩,rfl⟩

def coordinates (e : V ↪o W) (f : M →ₗ[K] N) (p : ℕ) :
    (Set.powersetCard V p →₀ M) →ₗ[K] (Set.powersetCard W p →₀ N) :=
  (Finsupp.lmapDomain N K (face e p)).comp (Finsupp.mapRange.linearMap f)

@[simp] theorem coordinates_single (e : V ↪o W) (f : M →ₗ[K] N) (p : ℕ)
    (F : Set.powersetCard V p) (m : M) :
    coordinates e f p (Finsupp.single F m)=Finsupp.single (face e p F) (f m) := by
  simp [coordinates]

theorem coordinates_injective (e : V ↪o W) (f : M →ₗ[K] N)
    (hf : Function.Injective f) (p : ℕ) : Function.Injective (coordinates e f p) := by
  intro x y h
  have he := Finsupp.mapDomain_injective (face e p).injective h
  ext F
  apply hf
  exact congrArg (fun z => z F) he

theorem differential_commutes (e : V ↪o W) (f : M →ₗ[K] N)
    (x : V → R) (y : W → S)
    (hf : ∀ v m, f (x v • m)=y (e v) • f m) (p : ℕ)
    (z : Set.powersetCard V (p+1) →₀ M) :
    coordinates e f p (coordinateDifferential x (ModuleCat.of R M) p z)=
      coordinateDifferential y (ModuleCat.of S N) p (coordinates e f (p+1) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | single F m =>
      rw [coordinateDifferential_single,map_sum,coordinates_single,coordinateDifferential_single]
      apply Fintype.sum_equiv (memberEquiv e F.val)
      intro v
      rw [coordinates_single,hf,map_zsmul_unit,face_erase]
      apply congrArg (Finsupp.single
        (eraseIndex (face e (p+1) F) (memberEquiv e F.val v)))
      change y (e v.val) • (TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val • f m)=
        y (e v.val) • (TauCeti.ExteriorAlgebra.basisEraseSign (e v.val)
          (F.val.map e.toEmbedding) • f m)
      rw [eraseSign]

end FourPapers.OrderedKoszulEmbedding

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.MinimumDegreeDiagonal -/
section

/-! # The minimum-degree diagonal of an actual differential algebra

A coefficient algebra whose nonzero degree-g terms satisfy μ(g)≤ℓ(g)
has a multiplicative projection to ℓ(g)=μ(g). The projection is a split
map of actual differential algebras, hence also a split map on actual
cycles modulo boundaries. No spectral sequence or Künneth assertion is
used in taking this diagonal.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.MinimumDegreeDiagonal
open Classical
variable {K A Γ : Type*} [CommRing K] [Ring A] [_root_.Algebra K A] [AddCommMonoid Γ]
  (P : Γ → Submodule K A) (h1 : (1:A)∈P 0)
  (hmul : ∀ g h, ∀ x∈P g, ∀ y∈P h, x*y∈P (g+h))
  (ℓ μ : Γ →+ ℕ) (hbelow : ∀ g, ℓ g<μ g → P g=⊥)

abbrev Algebra := gradedCoefficientAlgebra P h1 hmul

def projectionLinear : Algebra P h1 hmul →ₗ[K] Algebra P h1 hmul where
  toFun x := ⟨AddMonoidAlgebra.ofCoeff (x.val.coeff.filter (fun g => ℓ g=μ g)),by
    intro g
    change (if ℓ g=μ g then x.val.coeff g else 0)∈P g
    split_ifs
    · exact x.property g
    · exact (P g).zero_mem⟩
  map_add' x y := by apply Subtype.ext; ext g; simp [Finsupp.filter_apply]
  map_smul' c x := by apply Subtype.ext; ext g; simp [Finsupp.filter_apply]

@[simp] theorem projectionLinear_coeff (x : Algebra P h1 hmul) (g : Γ) :
    (projectionLinear P h1 hmul ℓ μ x).val.coeff g=
      if ℓ g=μ g then x.val.coeff g else 0 := rfl

@[simp] theorem projectionLinear_single (g : Γ) (x : P g) :
    projectionLinear P h1 hmul ℓ μ (coefficientSingle P h1 hmul g x)=
      if ℓ g=μ g then coefficientSingle P h1 hmul g x else 0 := by
  apply Subtype.ext
  ext h
  by_cases he : g=h
  · subst h
    split_ifs <;> simp_all [coefficientSingle_coeff]
  · split_ifs <;> simp_all [coefficientSingle_coeff, Finsupp.single_apply]

lemma coefficientSingle_mul (g h : Γ) (x : P g) (y : P h) :
    coefficientSingle P h1 hmul g x * coefficientSingle P h1 hmul h y=
      coefficientSingle P h1 hmul (g+h) ⟨x.val*y.val,hmul g h _ x.property _ y.property⟩ :=
  Subtype.ext (AddMonoidAlgebra.single_mul_single _ _ _ _)

include hbelow in
lemma nonzero_degree_lower (g : Γ) (x : P g) (hx : x≠0) : μ g≤ℓ g := by
  by_contra h
  have hmem : (x : A) ∈ (⊥ : Submodule K A) :=
    (hbelow g (by omega)).le x.property
  exact hx (Subtype.ext ((Submodule.mem_bot K).mp hmem))

include hbelow in
lemma projectionLinear_single_mul (g h : Γ) (x : P g) (y : P h) :
    projectionLinear P h1 hmul ℓ μ
      (coefficientSingle P h1 hmul g x * coefficientSingle P h1 hmul h y)=
        projectionLinear P h1 hmul ℓ μ (coefficientSingle P h1 hmul g x) *
          projectionLinear P h1 hmul ℓ μ (coefficientSingle P h1 hmul h y) := by
  by_cases hx : x=0
  · subst x; simp
  by_cases hy : y=0
  · subst y; simp
  have hg := nonzero_degree_lower P ℓ μ hbelow g x hx
  have hh := nonzero_degree_lower P ℓ μ hbelow h y hy
  have he : ℓ (g+h)=μ (g+h) ↔ ℓ g=μ g ∧ ℓ h=μ h := by
    simp only [map_add]
    omega
  rw [coefficientSingle_mul,projectionLinear_single,projectionLinear_single,
    projectionLinear_single]
  split_ifs <;> simp_all [coefficientSingle_mul]

include hbelow in
lemma projectionLinear_mul (x y : Algebra P h1 hmul) :
    projectionLinear P h1 hmul ℓ μ (x*y)=
      projectionLinear P h1 hmul ℓ μ x * projectionLinear P h1 hmul ℓ μ y := by
  let sx := fun g => coefficientSingle P h1 hmul g (coefficientAt P h1 hmul g x)
  let sy := fun h => coefficientSingle P h1 hmul h (coefficientAt P h1 hmul h y)
  have hx : (∑g∈x.val.coeff.support,sx g)=x := coefficient_decomposition P h1 hmul x
  have hy : (∑h∈y.val.coeff.support,sy h)=y := coefficient_decomposition P h1 hmul y
  calc
    projectionLinear P h1 hmul ℓ μ (x*y)=
        projectionLinear P h1 hmul ℓ μ
          ((∑g∈x.val.coeff.support,sx g)*(∑h∈y.val.coeff.support,sy h)) := by rw [hx,hy]
    _=∑g∈x.val.coeff.support,∑h∈y.val.coeff.support,
        projectionLinear P h1 hmul ℓ μ (sx g*sy h) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum]
    _=∑g∈x.val.coeff.support,∑h∈y.val.coeff.support,
        projectionLinear P h1 hmul ℓ μ (sx g)*projectionLinear P h1 hmul ℓ μ (sy h) := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      exact projectionLinear_single_mul P h1 hmul ℓ μ hbelow g h _ _
    _=projectionLinear P h1 hmul ℓ μ x * projectionLinear P h1 hmul ℓ μ y := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← map_sum, ← map_sum, hx, hy]

def projection : Algebra P h1 hmul →ₐ[K] Algebra P h1 hmul where
  toFun := projectionLinear P h1 hmul ℓ μ
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by apply Subtype.ext; ext g; simp [projectionLinear,AddMonoidAlgebra.one_def]
  map_mul' := projectionLinear_mul P h1 hmul ℓ μ hbelow
  commutes' c := by
    apply Subtype.ext
    ext g
    simp [projectionLinear, _root_.Algebra.algebraMap_eq_smul_one,
      AddMonoidAlgebra.one_def]

@[simp] theorem projection_idempotent (x : Algebra P h1 hmul) :
    projection P h1 hmul ℓ μ hbelow (projection P h1 hmul ℓ μ hbelow x)=
      projection P h1 hmul ℓ μ hbelow x := by
  apply Subtype.ext
  ext g
  change (if ℓ g=μ g then (if ℓ g=μ g then x.val.coeff g else 0) else 0) =
    if ℓ g=μ g then x.val.coeff g else 0
  split_ifs <;> rfl

/-- The actual minimum-degree subalgebra, with its literal inclusion. -/
def diagonal : Subalgebra K (Algebra P h1 hmul) := (projection P h1 hmul ℓ μ hbelow).range

lemma mem_diagonal_iff (x : Algebra P h1 hmul) :
    x∈diagonal P h1 hmul ℓ μ hbelow ↔ projection P h1 hmul ℓ μ hbelow x=x := by
  constructor
  · rintro ⟨x,rfl⟩; exact projection_idempotent P h1 hmul ℓ μ hbelow x
  · intro hx; exact ⟨x,hx⟩

def retraction : Algebra P h1 hmul →ₐ[K] diagonal P h1 hmul ℓ μ hbelow :=
  (projection P h1 hmul ℓ μ hbelow).rangeRestrict

@[simp] theorem retraction_val (x : diagonal P h1 hmul ℓ μ hbelow) :
    retraction P h1 hmul ℓ μ hbelow x.val=x :=
  Subtype.ext ((mem_diagonal_iff P h1 hmul ℓ μ hbelow x.val).mp x.property)

variable (D : ParityDifferential K A)
  (hd : ∀ g x, x∈P g → D.d x∈P g)
  (hp : ∀ g x, x∈P g → D.parity x∈P g)

def fullDifferential : ParityDifferential K (Algebra P h1 hmul) :=
  D.onMonoidAlgebra.restrict (Algebra P h1 hmul)
    (by intro x hx g; exact hd g _ (hx g))
    (by intro x hx g; exact hp g _ (hx g))

lemma projection_differential (x : Algebra P h1 hmul) :
    (fullDifferential P h1 hmul D hd hp).d (projection P h1 hmul ℓ μ hbelow x)=
      projection P h1 hmul ℓ μ hbelow ((fullDifferential P h1 hmul D hd hp).d x) := by
  apply Subtype.ext
  ext g
  change D.d (if ℓ g=μ g then x.val.coeff g else 0)=
    if ℓ g=μ g then D.d (x.val.coeff g) else 0
  split_ifs <;> simp

lemma projection_parity (x : Algebra P h1 hmul) :
    (fullDifferential P h1 hmul D hd hp).parity (projection P h1 hmul ℓ μ hbelow x)=
      projection P h1 hmul ℓ μ hbelow ((fullDifferential P h1 hmul D hd hp).parity x) := by
  apply Subtype.ext
  ext g
  change D.parity (if ℓ g=μ g then x.val.coeff g else 0)=
    if ℓ g=μ g then D.parity (x.val.coeff g) else 0
  split_ifs <;> simp

def differential : ParityDifferential K (diagonal P h1 hmul ℓ μ hbelow) :=
  (fullDifferential P h1 hmul D hd hp).restrict (diagonal P h1 hmul ℓ μ hbelow)
    (by
      rintro x ⟨y,rfl⟩
      exact ⟨(fullDifferential P h1 hmul D hd hp).d y,
        (projection_differential P h1 hmul ℓ μ hbelow D hd hp y).symm⟩)
    (by
      rintro x ⟨y,rfl⟩
      exact ⟨(fullDifferential P h1 hmul D hd hp).parity y,
        (projection_parity P h1 hmul ℓ μ hbelow D hd hp y).symm⟩)

def homologyProjection : (fullDifferential P h1 hmul D hd hp).Homology →ₐ[K]
    (differential P h1 hmul ℓ μ hbelow D hd hp).Homology :=
  ParityDifferential.homologyMap (fullDifferential P h1 hmul D hd hp)
    (differential P h1 hmul ℓ μ hbelow D hd hp) (retraction P h1 hmul ℓ μ hbelow)
    (fun x => Subtype.ext (projection_differential P h1 hmul ℓ μ hbelow D hd hp x))

theorem homologyProjection_surjective :
    Function.Surjective (homologyProjection P h1 hmul ℓ μ hbelow D hd hp) := by
  intro z
  obtain ⟨x,rfl⟩ := (differential P h1 hmul ℓ μ hbelow D hd hp).classMap_surjective z
  let y : (fullDifferential P h1 hmul D hd hp).cycles :=
    ⟨x.val.val,congrArg Subtype.val x.property⟩
  refine ⟨(fullDifferential P h1 hmul D hd hp).classMap y,?_⟩
  change (differential P h1 hmul ℓ μ hbelow D hd hp).classMap _ = _
  congr 1
  apply Subtype.ext
  exact retraction_val P h1 hmul ℓ μ hbelow x.val

/-- Generation descends through the proved differential-algebra retraction. -/
theorem homology_generated (G : Set (fullDifferential P h1 hmul D hd hp).Homology)
    (hgen : _root_.Algebra.adjoin K G=⊤) :
    _root_.Algebra.adjoin K ((homologyProjection P h1 hmul ℓ μ hbelow D hd hp) '' G)=⊤ := by
  let f := homologyProjection P h1 hmul ℓ μ hbelow D hd hp
  let S := _root_.Algebra.adjoin K (f '' G)
  have hg : _root_.Algebra.adjoin K G≤S.comap f := by
    apply _root_.Algebra.adjoin_le
    intro g hg
    exact _root_.Algebra.subset_adjoin ⟨g,hg,rfl⟩
  rw [hgen] at hg
  apply top_unique
  intro y _
  obtain ⟨x,rfl⟩ := homologyProjection_surjective P h1 hmul ℓ μ hbelow D hd hp y
  exact hg (show x∈(⊤ : Subalgebra K _) from trivial)

end FourPapers.MinimumDegreeDiagonal

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredReesGeneration -/
section

/-! # Generation on the actual colored Rees diagonal

The diagonal algebra and its differential are obtained by a proved
multiplicative coefficient projection from the literal Rees/Koszul
coordinate algebra. Every surviving degree-one generator has exactly
one color, and generation descends through the actual homology map.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}
variable {k : Type u} [CommRing k]

def coloredFineColorDegree : ReesFineDegree.{u} (coloredRows (r := r) n) →+ ℕ :=
  (colorDegree (finiteRowColorVariables (coloredRows (r := r) n) 0)).comp
    (AddMonoidHom.snd _ _)

def coloredFineReesDegree : ReesFineDegree.{u} (coloredRows (r := r) n) →+ ℕ :=
  AddMonoidHom.fst _ _

lemma coloredPowerFace_below_zero
    (g : ReesFineDegree.{u} (coloredRows (r := r) n))
    (hg : coloredFineColorDegree g<coloredFineReesDegree g) :
    PowerFaceModule (E := coloredFamily n E) (k := k) g.1 g.2=⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro x ⟨F,hF,rfl⟩
  have hpower (dec : DecidableEq (FiniteVariable.{u} (coloredRows (r := r) n))) :
      @exponentPowerFamily _ dec
          (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1 =
        @exponentPowerFamily _
          (finiteVariableLinearOrder (coloredRows (r := r) n)).toDecidableEq
          (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1 :=
    congrArg (fun d => @exponentPowerFamily _ d
      (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1)
      (Subsingleton.elim _ _)
  have hF' := hF.2
  rw [hpower] at hF'
  have hlow := colorDegree_power_lower
    (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E))
    (finiteRowColorVariables (coloredRows (r := r) n) 0)
    (finiteRowFamily_colorDegree (coloredRows (r := r) n) (coloredFamily n E) 0)
    g.1 hF'
  have hmono := colorDegree_mono
    (finiteRowColorVariables (coloredRows (r := r) n) 0)
    (tsub_le_self : g.2-faceExponent F≤g.2)
  exact (Nat.not_lt_of_ge (hlow.trans hmono) hg).elim

variable (hE : ColoredLatticeClosed n E)

abbrev coloredReesClosure :
    finiteLatticeClosed (coloredRows (r := r) n) (coloredFamily n E) :=
  (coloredLatticeClosed_iff n E).mp hE

abbrev coloredPowerPieces (g : ReesFineDegree.{u} (coloredRows (r := r) n)) :=
  PowerFaceModule (E := coloredFamily n E) (k := k) g.1 g.2

/-- The literal minimum-color subalgebra of the full Rees/Koszul algebra. -/
abbrev minimumColorReesAlgebra :=
  MinimumDegreeDiagonal.diagonal (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))

def coloredPieceBoundary (g : ReesFineDegree.{u} (coloredRows (r := r) n))
    (x : Simplicial.Ambient (FiniteVariable.{u} (coloredRows (r := r) n)) k)
    (hx : x∈coloredPowerPieces (E := E) g) :
    (exteriorParityDifferential (k := k)).d x∈coloredPowerPieces (E := E) g :=
  boundary_mem_basisSpan
    (koszulFaces_downward (exponentPowerFamily
      (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1) g.2) hx

def coloredPieceParity (g : ReesFineDegree.{u} (coloredRows (r := r) n))
    (x : Simplicial.Ambient (FiniteVariable.{u} (coloredRows (r := r) n)) k)
    (hx : x∈coloredPowerPieces (E := E) g) :
    (exteriorParityDifferential (k := k)).parity x∈coloredPowerPieces (E := E) g :=
  (totalFaceInvolute (koszulFaces (exponentPowerFamily
    (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1) g.2) ⟨x,hx⟩).property

abbrev minimumColorReesDifferential : ParityDifferential k (minimumColorReesAlgebra (k := k) hE) :=
  MinimumDegreeDiagonal.differential (coloredPowerPieces (E := E))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))
    exteriorParityDifferential (coloredPieceBoundary (E := E)) (coloredPieceParity (E := E))

/-- This is the homology map induced by the actual color-diagonal projection. -/
abbrev minimumColorReesHomologyProjection :
    ReesKoszulCoordinateHomology (k := k) (coloredReesClosure hE) →ₐ[k]
      (minimumColorReesDifferential (k := k) hE).Homology :=
  ParityDifferential.homologyMap
    (reesKoszulCoordinateDifferential (k := k) (coloredReesClosure hE))
    (minimumColorReesDifferential (k := k) hE)
    (MinimumDegreeDiagonal.retraction (coloredPowerPieces (E := E) (k := k))
      (powerFace_one_mem (coloredReesClosure hE))
      (powerFace_mul_mem (coloredReesClosure hE))
      coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E)))
    (fun y => Subtype.ext (MinimumDegreeDiagonal.projection_differential
      (coloredPowerPieces (E := E) (k := k))
      (powerFace_one_mem (coloredReesClosure hE))
      (powerFace_mul_mem (coloredReesClosure hE))
      coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))
      exteriorParityDifferential (coloredPieceBoundary (E := E)) (coloredPieceParity (E := E)) y))

/-- The degree-one diagonal classes, represented by actual first-power
cycles having total color degree one. -/
def firstMinimumColorClasses : Set (minimumColorReesDifferential (k := k) hE).Homology :=
  {z | ∃ α : Exponent (FiniteVariable.{u} (coloredRows (r := r) n)),
    colorDegree (finiteRowColorVariables (coloredRows (r := r) n) 0) α=1 ∧
    ∃ x : LinearMap.ker (powerFaceDifferential (E := coloredFamily n E) (k := k) 1 α),
      minimumColorReesHomologyProjection (k := k) hE
        (reesHomologyPieceMap (k := k) (coloredReesClosure hE) (1,α) x)=z}

lemma minimumColorReesHomologyProjection_nonminimal
    (α : Exponent (FiniteVariable.{u} (coloredRows (r := r) n)))
    (hα : colorDegree (finiteRowColorVariables (coloredRows (r := r) n) 0) α≠1)
    (x : LinearMap.ker (powerFaceDifferential (E := coloredFamily n E) (k := k) 1 α)) :
    minimumColorReesHomologyProjection (k := k) hE
      (reesHomologyPieceMap (k := k) (coloredReesClosure hE) (1,α) x)=0 := by
  change (minimumColorReesDifferential (k := k) hE).classMap _=0
  apply ((minimumColorReesDifferential (k := k) hE).classMap_eq_zero _).mpr
  refine ⟨0, ?_⟩
  rw [map_zero]
  apply Subtype.ext
  change 0 = MinimumDegreeDiagonal.projectionLinear
    (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree
    (coefficientSingle (coloredPowerPieces (E := E) (k := k))
      (powerFace_one_mem (coloredReesClosure hE))
      (powerFace_mul_mem (coloredReesClosure hE)) (1,α) x.val)
  rw [MinimumDegreeDiagonal.projectionLinear_single]
  have hc : coloredFineColorDegree (1, α) ≠ coloredFineReesDegree (1, α) := hα
  rw [if_neg hc]

theorem minimumColorReesHomology_generated_of_generation
    (hgen : Algebra.adjoin k (firstReesClasses (k := k) (coloredReesClosure hE))=⊤) :
    Algebra.adjoin k (firstMinimumColorClasses (k := k) hE)=⊤ := by
  have hg := MinimumDegreeDiagonal.homology_generated (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))
    exteriorParityDifferential (coloredPieceBoundary (E := E)) (coloredPieceParity (E := E))
    (firstReesClasses (k := k) (coloredReesClosure hE)) hgen
  change Algebra.adjoin k
    (minimumColorReesHomologyProjection (k := k) hE ''
      firstReesClasses (k := k) (coloredReesClosure hE)) = ⊤ at hg
  apply top_unique
  rw [← hg]
  apply Algebra.adjoin_le
  rintro _ ⟨z,⟨α,x,rfl⟩,rfl⟩
  by_cases ha : colorDegree (finiteRowColorVariables (coloredRows (r := r) n) 0) α=1
  · exact Algebra.subset_adjoin ⟨α,ha,x,rfl⟩
  · rw [minimumColorReesHomologyProjection_nonminimal hE α ha x]
    exact (Algebra.adjoin k (firstMinimumColorClasses (k := k) hE)).zero_mem

section Field
variable (K : Type u) [Field K]

/-- The generation assertion on the actual colored minimum diagonal. The
coefficient and Koszul diagonal isomorphisms identify its degree-one
pieces with Tor of the individual color ideals. -/
theorem minimumColorReesHomology_generated :
    Algebra.adjoin K (firstMinimumColorClasses (k := K) hE)=⊤ :=
  minimumColorReesHomology_generated_of_generation hE
    (reesCoordinateHomology_generated_in_degree_one (coloredReesClosure hE))

end Field

/-- A nonnegative color multidegree of total degree one is a coordinate unit. -/
theorem color_degree_one_eq_unit {C : Type*} [Fintype C] [DecidableEq C]
    (a : C →₀ ℕ) (ha : a.degree=1) : ∃ c, a=Finsupp.single c 1 := by
  have hn : a≠0 := by intro h; rw [h,map_zero] at ha; omega
  obtain ⟨c,hc⟩ := Finsupp.support_nonempty_iff.mpr hn
  have hp : 0<a c := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hc)
  have hle : Finsupp.single c 1≤a := by
    intro j
    by_cases hj : c=j
    · subst j; simpa using Nat.succ_le_iff.mpr hp
    · simp [Finsupp.single_apply,hj]
  exact ⟨c,(eq_of_le_of_degree_eq hle (by simpa using ha.symm)).symm⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedFaceRestriction -/
section

/-! # Signed quotient-face complexes under an ordered variable restriction -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.OrderedFaceRestriction
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice
universe u
variable {k V W : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W] (e : V ↪o W)
  (P : Finset V → Prop) (Q : Finset W → Prop)
  (hmap : ∀ F,Q (F.map e.toEmbedding) ↔ P F)
  (hsurj : ∀ F,Q F → ∃ G : Finset V,F=G.map e.toEmbedding)

def indexEquiv : {F // P F} ≃ {F // Q F} :=
  Equiv.ofBijective (fun F => ⟨F.val.map e.toEmbedding,(hmap F.val).mpr F.property⟩)
    ⟨by
      intro F G h
      exact Subtype.ext (Finset.map_injective e.toEmbedding (congrArg Subtype.val h)),by
      intro F
      obtain ⟨G,hG⟩ := hsurj F.val F.property
      refine ⟨⟨G,(hmap G).mp (hG ▸ F.property)⟩,?_⟩
      exact Subtype.ext hG.symm⟩

@[simp] theorem indexEquiv_val (F : {F // P F}) :
    (indexEquiv e P Q hmap hsurj F).val=F.val.map e.toEmbedding := rfl

def totalEquiv : TotalFaceModule (k := k) P ≃ₗ[k] TotalFaceModule (k := k) Q :=
  (totalFaceBasis (k := k) P).equiv (totalFaceBasis (k := k) Q) (indexEquiv e P Q hmap hsurj)

@[simp] theorem totalEquiv_basis (F : {F // P F}) :
    totalEquiv (k := k) e P Q hmap hsurj (totalFaceBasis (k := k) P F)=
      totalFaceBasis (k := k) Q (indexEquiv e P Q hmap hsurj F) :=
  Module.Basis.equiv_apply _ _ _ _

lemma totalEquiv_preserves (p : ℕ) (x : TotalFaceModule (k := k) P)
    (hx : x∈totalFacePiece P p) : totalEquiv (k := k) e P Q hmap hsurj x∈totalFacePiece Q p := by
  rw [totalFacePiece_eq_basis_span] at hx ⊢
  have hspan : Submodule.span k ((totalFaceBasis (k := k) P) '' {F | F.val.card=p}) ≤
      (Submodule.span k ((totalFaceBasis (k := k) Q) '' {F | F.val.card=p})).comap
        (totalEquiv (k := k) e P Q hmap hsurj).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F,hF,rfl⟩
    change totalEquiv (k := k) e P Q hmap hsurj (totalFaceBasis (k := k) P F)∈Submodule.span k ((totalFaceBasis (k := k) Q) '' {F | F.val.card=p})
    rw [totalEquiv_basis]
    exact Submodule.subset_span ⟨indexEquiv e P Q hmap hsurj F,
      by simpa [indexEquiv] using hF,rfl⟩
  exact hspan hx

lemma totalEquiv_symm_preserves (p : ℕ) (x : TotalFaceModule (k := k) Q)
    (hx : x∈totalFacePiece Q p) : (totalEquiv (k := k) e P Q hmap hsurj).symm x∈totalFacePiece P p := by
  rw [totalFacePiece_eq_basis_span] at hx ⊢
  have hspan : Submodule.span k ((totalFaceBasis (k := k) Q) '' {F | F.val.card=p}) ≤
      (Submodule.span k ((totalFaceBasis (k := k) P) '' {F | F.val.card=p})).comap
        (totalEquiv (k := k) e P Q hmap hsurj).symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F,hF,rfl⟩
    obtain ⟨G,rfl⟩ := (indexEquiv e P Q hmap hsurj).surjective F
    change (totalEquiv (k := k) e P Q hmap hsurj).symm (totalFaceBasis (k := k) Q _ )∈Submodule.span k ((totalFaceBasis (k := k) P) '' {F | F.val.card=p})
    rw [← totalEquiv_basis,LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span ⟨G,by simpa [indexEquiv] using hF,rfl⟩
  exact hspan hx

end FourPapers.OrderedFaceRestriction

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.OrderedFaceRestriction FourPapers.OrderedKoszulEmbedding
universe u
variable {k V W : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W] (e : V ↪o W)
  (B : Family V) (α : Exponent V) (C : Family W) (β : Exponent W)
  (hmap : ∀ F,quotientKoszulFaces C β (F.map e.toEmbedding) ↔ quotientKoszulFaces B α F)
  (hsurj : ∀ F,quotientKoszulFaces C β F → ∃ G : Finset V,F=G.map e.toEmbedding)

abbrev orderedQuotientRestrictionEquiv :=
  totalEquiv (k := k) e (quotientKoszulFaces B α) (quotientKoszulFaces C β) hmap hsurj

lemma quotientRestriction_differential :
    (quotientTotalDifferential (k := k) C β).comp
      (orderedQuotientRestrictionEquiv e B α C β hmap hsurj).toLinearMap=
        (orderedQuotientRestrictionEquiv e B α C β hmap hsurj).toLinearMap.comp
          (quotientTotalDifferential B α) := by
  apply (totalFaceBasis (quotientKoszulFaces B α)).ext
  intro F
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,totalEquiv_basis,
    quotientTotalDifferential_basis,map_sum,indexEquiv_val]
  symm
  apply Fintype.sum_equiv (memberEquiv e F.val)
  intro v
  have herase : (F.val.map e.toEmbedding).erase (e v.val)=
      (F.val.erase v.val).map e.toEmbedding := by
    ext w
    simp only [Finset.mem_erase,Finset.mem_map]
    constructor
    · rintro ⟨hne,z,hz,rfl⟩
      exact ⟨z,⟨fun he => hne (congrArg e he),hz⟩,rfl⟩
    · rintro ⟨z,⟨hne,hz⟩,rfl⟩
      exact ⟨fun he => hne (e.injective he),z,hz,rfl⟩
  by_cases hv : quotientKoszulFaces B α (F.val.erase v.val)
  · have hw : quotientKoszulFaces C β ((F.val.map e.toEmbedding).erase (e v.val)) := by
      rw [herase]; exact (hmap _).mpr hv
    simp only [memberEquiv_val,dif_pos hv,dif_pos hw,map_zsmul_unit,totalEquiv_basis,eraseSign]
    congr 1
    apply congrArg (totalFaceBasis (quotientKoszulFaces C β))
    apply Subtype.ext
    exact herase.symm
  · have hw : ¬quotientKoszulFaces C β ((F.val.map e.toEmbedding).erase (e v.val)) := by
      rw [herase]; exact fun h => hv ((hmap _).mp h)
    simp only [memberEquiv_val,dif_neg hv,dif_neg hw,map_zero]

/-- An isomorphism of the literal quotient Koszul homogeneous complexes. -/
def quotientHomogeneousRestrictionIso :
    quotientHomogeneousComplex (k := k) B α ≅ quotientHomogeneousComplex (k := k) C β :=
  (quotientTotalKoszulIso B α).symm ≪≫
    (quotientTotalData B α).isoOfTotal (quotientTotalData C β)
      (orderedQuotientRestrictionEquiv e B α C β hmap hsurj)
      (totalEquiv_preserves e _ _ hmap hsurj)
      (totalEquiv_symm_preserves e _ _ hmap hsurj)
      (quotientRestriction_differential e B α C β hmap hsurj) ≪≫
    quotientTotalKoszulIso C β

section Ideal
variable (P : Finset V → Prop) (Q : Finset W → Prop)
  (hP : Simplicial.Downward P) (hQ : Simplicial.Downward Q)
  (hmapI : ∀ F,Q (F.map e.toEmbedding) ↔ P F)
  (hsurjI : ∀ F,Q F → ∃ G : Finset V,F=G.map e.toEmbedding)

lemma idealRestriction_differential :
    (idealTotalDifferential (k := k) hQ).comp
      (totalEquiv (k := k) e P Q hmapI hsurjI).toLinearMap=
        (totalEquiv (k := k) e P Q hmapI hsurjI).toLinearMap.comp (idealTotalDifferential hP) := by
  apply (totalFaceBasis (k := k) P).ext
  intro F
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,totalEquiv_basis,
    idealTotalDifferential_basis,map_sum,map_zsmul_unit,totalEquiv_basis,indexEquiv_val]
  symm
  apply Fintype.sum_equiv (memberEquiv e F.val)
  intro v
  simp only [memberEquiv_val,eraseSign]
  congr 1
  apply congrArg (totalFaceBasis (k := k) Q)
  apply Subtype.ext
  exact Finset.map_erase e.toEmbedding F.val v.val

def idealFaceRestrictionIso :
    (idealTotalData (k := k) hP).complex ≅ (idealTotalData (k := k) hQ).complex :=
  (idealTotalData hP).isoOfTotal (idealTotalData hQ)
    (totalEquiv (k := k) e P Q hmapI hsurjI)
    (totalEquiv_preserves e P Q hmapI hsurjI)
    (totalEquiv_symm_preserves e P Q hmapI hsurjI)
    (idealRestriction_differential e P Q hP hQ hmapI hsurjI)

end Ideal
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.KoszulReorientation -/
section

/-! # Changing the exterior orientation without changing the variables

Two linear orders produce different ordered exterior bases. The actual
exterior-algebra identity gives a signed coordinate equivalence; the
sign on each face is a unit. Coefficient and fine-degree labels are
unchanged, and the literal Koszul differentials commute with the map.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.KoszulReorientation
open Classical CommAlg CommAlg.Koszul MvPolynomial CategoryTheory
universe u
variable {K V M : Type u} [CommRing K] [Fintype V]
  [AddCommGroup M] [Module K M]
  (l₁ l₂ : LinearOrder V)

def coordinates (p : ℕ) : (Set.powersetCard V p →₀ M) ≃ₗ[K]
    (Set.powersetCard V p →₀ M) :=
  @TensorExteriorKoszul.renameCoordinates K V V _ _ l₁ _ l₂ (Equiv.refl V)
    M M _ _ _ _ (LinearEquiv.refl K M) p

 theorem coordinates_symm (p : ℕ) :
    (coordinates (K := K) (M := M) l₁ l₂ p).symm=coordinates (K := K) l₂ l₁ p :=
  @TensorExteriorKoszul.renameCoordinates_symm_eq K V V _ _ l₁ _ l₂ (Equiv.refl V)
    M M _ _ _ _ (LinearEquiv.refl K M) p

 theorem coordinates_single (p : ℕ) (F : Set.powersetCard V p) (m : M) :
    ∃ ε : ℤˣ,coordinates (K := K) l₁ l₂ p (Finsupp.single F m)=
      ε • Finsupp.single F m := by
  let ε := @TensorExteriorKoszul.exteriorRenameSign K V V _ _ l₁ _ l₂
    (Equiv.refl V) F.val
  refine ⟨ε,?_⟩
  have h := @TensorExteriorKoszul.renameCoordinates_single K V V _ _ l₁ _ l₂
    (Equiv.refl V) M M _ _ _ _ (LinearEquiv.refl K M) p F m
  simpa only [coordinates,Equiv.coe_refl,Finset.image_id,LinearEquiv.refl_apply] using h

variable [Module (MvPolynomial V K) M] [IsScalarTower K (MvPolynomial V K) M]

 theorem differential (p : ℕ) (x : Set.powersetCard V (p+1) →₀ M) :
    coordinates (K := K) l₁ l₂ p
      (haveI := l₁; coordinateDifferential (X : V → MvPolynomial V K)
        (ModuleCat.of (MvPolynomial V K) M) p x)=
      (haveI := l₂; coordinateDifferential (X : V → MvPolynomial V K)
        (ModuleCat.of (MvPolynomial V K) M) p (coordinates (K := K) l₁ l₂ (p+1) x)) :=
  @TensorExteriorKoszul.renameCoordinates_differential K V V _ _ l₁ _ l₂
    (Equiv.refl V) M M _ _ _ _ (LinearEquiv.refl K M)
    _ _ _ _ (by intro v m; rfl) p x

end FourPapers.KoszulReorientation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientKoszulReorientation -/
section

/-! # Fine quotient Betti numbers do not depend on the exterior order -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice.QuotientReorientation
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
attribute [local irreducible] KoszulReorientation.coordinates
universe u
section Generic
variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  (l₁ l₂ : LinearOrder V) (B : Family V)

 theorem coordinates_mem (α : Exponent V) (p : ℕ)
    (x : Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (hx : x∈(haveI := l₁; quotientPiece (k := k) B α p)) :
    KoszulReorientation.coordinates (K := k) l₁ l₂ p x∈(haveI := l₂; quotientPiece (k := k) B α p) := by
  apply map_mem_piece_of_basis (haveI := l₁; quotientCoefficientBasis (k := k) B p)
    (haveI := l₂; quotientCoefficientBasis (k := k) B p)
    (haveI := l₁; quotientDegree) (haveI := l₂; quotientDegree)
    (KoszulReorientation.coordinates (K := k) l₁ l₂ p).toLinearMap ?_ α hx
  intro a
  letI := l₂
  have hb : quotientCoefficientBasis (k := k) B p a∈
      quotientPiece (k := k) B (quotientDegree a) p :=
    Grading.basis_mem_piece _ _ a
  rw [@quotientCoefficientBasis_apply V k _ l₂ _ B p a.1 a.2] at hb
  change KoszulReorientation.coordinates (K := k) l₁ l₂ p
    ((haveI := l₁; quotientCoefficientBasis (k := k) B p) a) ∈
      (haveI := l₂; quotientPiece (k := k) B (haveI := l₁; quotientDegree a) p)
  rw [@quotientCoefficientBasis_apply V k _ l₁ _ B p a.1 a.2]
  have hd : (haveI := l₁; quotientDegree a)=(haveI := l₂; quotientDegree a) := by
    ext v
    simp only [quotientDegree,Finsupp.add_apply,faceExponent_apply] <;> split_ifs <;> rfl
  rw [hd]
  obtain ⟨ε,hε⟩ := KoszulReorientation.coordinates_single (K := k) l₁ l₂ p a.1
    (quotientMonomial (k := k) B a.2.val)
  rw [hε]
  exact (quotientPiece (k := k) B (quotientDegree a) p).toAddSubgroup.zsmul_mem hb (ε : ℤ)

def pieceEquiv (α : Exponent V) (p : ℕ) :
    (haveI := l₁; quotientPiece (k := k) B α p) ≃ₗ[k]
      (haveI := l₂; quotientPiece (k := k) B α p) where
  toFun x := ⟨KoszulReorientation.coordinates (K := k) l₁ l₂ p x.val,coordinates_mem l₁ l₂ B α p x.val x.property⟩
  invFun x := ⟨(KoszulReorientation.coordinates (K := k) l₁ l₂ p).symm x.val,by
    rw [KoszulReorientation.coordinates_symm]
    exact coordinates_mem l₂ l₁ B α p x.val x.property⟩
  left_inv x := Subtype.ext ((KoszulReorientation.coordinates (K := k) l₁ l₂ p).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((KoszulReorientation.coordinates (K := k) l₁ l₂ p).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

 theorem pieceEquiv_differential (α : Exponent V) (p : ℕ)
    (x : (haveI := l₁; quotientPiece (k := k) B α (p+1))) :
    pieceEquiv l₁ l₂ B α p ((haveI := l₁; quotientHomogeneousDifferential (k := k) B α p) x)=
      (haveI := l₂; quotientHomogeneousDifferential (k := k) B α p)
        (pieceEquiv l₁ l₂ B α (p+1) x) := by
  apply Subtype.ext
  exact KoszulReorientation.differential (K := k) l₁ l₂ p x.val

 def complex (l : LinearOrder V) (α : Exponent V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  haveI := l
  quotientHomogeneousComplex (k := k) B α

/-- The comparison commutes with the full differential in every degree. -/
def complexIso (α : Exponent V) : complex (k := k) B l₁ α ≅ complex (k := k) B l₂ α :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (pieceEquiv l₁ l₂ B α p).toModuleIso) (by
      intro i j hij
      obtain rfl : i=j+1 := hij.symm
      dsimp only [complex]
      simp only [quotientHomogeneousComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (pieceEquiv_differential l₁ l₂ B α j x).symm)


end Generic

variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  (l₁ l₂ : LinearOrder V) (B : Family V)

/-- Actual fine derived-Tor dimensions retain their values under every
choice of ordering of the same polynomial variables. -/
theorem quotientBettiNumber_eq (α : Exponent V) (p : ℕ) :
    (haveI := l₁; quotientBettiNumber (k := k) B α p)=
      (haveI := l₂; quotientBettiNumber (k := k) B α p) := by
  calc
    _ = Module.finrank k ((complex (k := k) B l₁ α).homology p) := by
      letI := l₁
      exact quotientBettiNumber_eq_homology B α p
    _ = Module.finrank k ((complex (k := k) B l₂ α).homology p) :=
      ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
        (complexIso l₁ l₂ B α)).toLinearEquiv.finrank_eq
    _ = _ := by
      letI := l₂
      exact (quotientBettiNumber_eq_homology B α p).symm

end FourPapers.Sublattice.QuotientReorientation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredCoefficientTor -/
section

/-! # Integral coefficient Tor on the colored diagonal

The comparison explicitly removes the color variables from each residual
color-zero coefficient complex. The remaining polynomial quotient is the
sum of the actual same-color predecessor colons.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d r : ℕ} {n : Fin d → ℕ}

def coloredBaseEmbedding : FiniteVariable.{u} n ↪ FiniteVariable.{u} (coloredRows (r := r) n) where
  toFun v := ⟨v.1.succ,v.2⟩
  inj' := by
    intro v w h
    exact Sum.inr_injective ((coloredVariableEquiv n).injective h)

/-- Choose the induced exterior orientation on the old variables. Koszul
homology and the actual derived Tor objects retain their original meaning. -/
def coloredBaseOrder : LinearOrder (FiniteVariable.{u} n) :=
  @LinearOrder.lift' (FiniteVariable.{u} n)
    (FiniteVariable.{u} (coloredRows (r := r) n))
    (finiteVariableLinearOrder (coloredRows (r := r) n))
    (coloredBaseEmbedding (r := r) (n := n)) (coloredBaseEmbedding (r := r) (n := n)).injective

def coloredBaseOrderEmbedding :
    @OrderEmbedding (FiniteVariable.{u} n) (FiniteVariable.{u} (coloredRows (r := r) n))
      (coloredBaseOrder (r := r) (n := n)).toLE
      (finiteVariableLinearOrder (coloredRows (r := r) n)).toLE where
  toEmbedding := coloredBaseEmbedding (r := r) (n := n)
  map_rel_iff' := by intro a b; rfl

lemma coloredFaceExponent (F : Finset (FiniteVariable.{u} n)) :
    faceExponent (F.map (coloredBaseEmbedding (r := r)))=coloredExponent 0 (faceExponent F) := by
  ext ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro c
    simp [faceExponent_apply,coloredBaseEmbedding]
  · intro i c
    rw [coloredExponent_succ 0 (faceExponent F) (⟨i,c⟩ : FiniteVariable.{u} n),
      faceExponent_apply,faceExponent_apply]
    have hmem : (⟨i.succ,c⟩ : FiniteVariable.{u} (coloredRows (r := r) n))∈
        F.map (coloredBaseEmbedding (r := r)) ↔ (⟨i,c⟩ : FiniteVariable.{u} n)∈F := by
      change coloredBaseEmbedding (r := r) (⟨i,c⟩ : FiniteVariable.{u} n)∈
        F.map (coloredBaseEmbedding (r := r)) ↔ _
      exact Finset.mem_map' _
    simp only [hmem]
    by_cases h : (⟨i,c⟩ : FiniteVariable.{u} n)∈F
    · simp only [if_pos h]
    · simp only [if_neg h]

lemma colorZeroFace_range (a : Exponent (FiniteVariable.{u} n))
    (F : Finset (FiniteVariable.{u} (coloredRows (r := r) n)))
    (hF : fullKoszulFaces (coloredExponent 0 a) F) :
    ∃ G : Finset (FiniteVariable.{u} n),F=G.map (coloredBaseEmbedding (r := r)) := by
  let G := Finset.univ.filter fun v => coloredBaseEmbedding (r := r) v∈F
  refine ⟨G,?_⟩
  ext v
  constructor
  · intro hv
    rcases v with ⟨i,j⟩
    revert j
    refine Fin.cases ?_ ?_ i
    · intro c hc
      have h := hF ⟨0,c⟩
      simp only [fullKoszulFaces,faceExponent_apply,if_pos hc,
        coloredExponent_zero,Finsupp.zero_apply] at h
      omega
    · intro i c hc
      exact Finset.mem_map.mpr ⟨⟨i,c⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩,rfl⟩
  · rintro h
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp h
    exact (Finset.mem_filter.mp hv).2

variable (E : Fin r → Finset (FiniteTuple n)) {m : ℕ}
  (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m)
  (a : Exponent (FiniteVariable.{u} n))

lemma coloredCoefficientFaces_iff (F : Finset (FiniteVariable.{u} n)) :
    quotientKoszulFaces (finiteChainCoefficientFamily (coloredRows (r := r) n) w)
      (coloredExponent 0 a) (F.map (coloredBaseEmbedding (r := r))) ↔
      quotientKoszulFaces (sameColorChainCoefficientFamily E w) a F := by
  unfold quotientKoszulFaces fullKoszulFaces forbiddenKoszulFaces
  simp only [coloredFaceExponent,coloredExponent_le_iff,coloredExponent_sub,tsub_self,
    coloredChainCoefficient_contains_zero,le_refl,true_and]

variable {k : Type u} [CommRing k]

/-- Literal chain comparison of the residual coefficient quotient. -/
def coloredCoefficientComplexIso :
    quotientHomogeneousComplex (k := k)
      (finiteChainCoefficientFamily (coloredRows (r := r) n) w) (coloredExponent 0 a) ≅
    quotientHomogeneousComplex (k := k) (sameColorChainCoefficientFamily E w) a := by
  let l := coloredBaseOrder (r := r) (n := n)
  letI := l
  let e := quotientHomogeneousRestrictionIso (k := k) (coloredBaseOrderEmbedding (r := r) (n := n))
    (sameColorChainCoefficientFamily E w) a
    (finiteChainCoefficientFamily (coloredRows (r := r) n) w) (coloredExponent 0 a)
    (by intro F
        exact coloredCoefficientFaces_iff E w a F)
    (fun F hF => colorZeroFace_range a F hF.1)
  exact e.symm ≪≫ QuotientReorientation.complexIso l (finiteVariableLinearOrder n)
    (sameColorChainCoefficientFamily E w) a

/-- The integral comparison in genuine fine-graded derived Tor. -/
def coloredCoefficientTorIso (p : ℕ) :
    ModuleCat.of k (quotientPaperGradedTor (k := k)
      (finiteChainCoefficientFamily (coloredRows (r := r) n) w) (coloredExponent 0 a) p) ≅
    ModuleCat.of k (quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w) a p) :=
  (quotientPaperGradedTorIso _ _ p).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
      (coloredCoefficientComplexIso E w a) ≪≫
    quotientPaperGradedTorIso _ _ p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.EmptyPowerTor -/
section

/-! # The empty-power Tor identity, including every fine degree -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.OrderedFaceRestriction
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma singletonZero_faces (a : Exponent V) (F : Finset V) :
    koszulFaces ({0} : Family V) a F ↔ fullKoszulFaces a F := by
  simp [koszulFaces,Contains,fullKoszulFaces]

lemma emptyQuotient_faces (a : Exponent V) (F : Finset V) :
    quotientKoszulFaces (∅ : Family V) a F ↔ fullKoszulFaces a F := by
  simp [quotientKoszulFaces,forbiddenKoszulFaces,Contains]

def emptyPowerFaceEquiv (a : Exponent V) :
    TotalFaceModule (k := k) (koszulFaces ({0} : Family V) a) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces (∅ : Family V) a) :=
  totalEquiv (OrderEmbedding.id V) _ _
    (fun F => by simpa using (emptyQuotient_faces a F).trans (singletonZero_faces a F).symm)
    (fun F _ => ⟨F,by simp⟩)

lemma emptyPowerFaceEquiv_val (a : Exponent V)
    (x : TotalFaceModule (k := k) (koszulFaces ({0} : Family V) a)) :
    (emptyPowerFaceEquiv a x).val=x.val := by
  have he : (TotalFaceModule (k := k) (quotientKoszulFaces (∅ : Family V) a)).subtype.comp
      (emptyPowerFaceEquiv a).toLinearMap=
        (TotalFaceModule (k := k) (koszulFaces ({0} : Family V) a)).subtype := by
    apply (totalFaceBasis (koszulFaces ({0} : Family V) a)).ext
    intro F
    simp [emptyPowerFaceEquiv,totalEquiv_basis,indexEquiv,totalFaceBasis_val]
  exact LinearMap.congr_fun he x

lemma emptyPowerFaceEquiv_differential (a : Exponent V) :
    (quotientTotalDifferential (k := k) (∅ : Family V) a).comp
      (emptyPowerFaceEquiv a).toLinearMap=
        (emptyPowerFaceEquiv a).toLinearMap.comp
          (idealTotalDifferential (koszulFaces_downward ({0} : Family V) a)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,quotientTotalDifferential_val,
    emptyPowerFaceEquiv_val,idealTotalDifferential_val]
  rw [quotientFaceProjection]
  apply relativeProjection_eq_self
  have hQ : quotientKoszulFaces (∅ : Family V) a=fullKoszulFaces a :=
    funext fun F => propext (emptyQuotient_faces a F)
  have hP : koszulFaces ({0} : Family V) a=fullKoszulFaces a :=
    funext fun F => propext (singletonZero_faces a F)
  rw [show (fun F => fullKoszulFaces a F ∧ ¬forbiddenKoszulFaces (∅ : Family V) a F)=
      fullKoszulFaces a from hQ]
  exact boundary_mem_basisSpan (fullKoszulFaces_downward a) (by simpa only [hP] using x.property)

/-- The zero-th ideal power and the quotient by the zero coefficient ideal
have the same actual fine Koszul complex. -/
def emptyPowerHomogeneousIso (a : Exponent V) :
    homogeneousComplex (k := k) ({0} : Family V) a ≅
      quotientHomogeneousComplex (k := k) (∅ : Family V) a :=
  (idealTotalKoszulIso ({0} : Family V) a).symm ≪≫
    (idealTotalData (koszulFaces_downward ({0} : Family V) a)).isoOfTotal
      (quotientTotalData (∅ : Family V) a) (emptyPowerFaceEquiv a)
      (totalEquiv_preserves (OrderEmbedding.id V) _ _ _ _)
      (totalEquiv_symm_preserves (OrderEmbedding.id V) _ _ _ _)
      (emptyPowerFaceEquiv_differential a) ≪≫
    quotientTotalKoszulIso (∅ : Family V) a

def emptyPowerTorIso (a : Exponent V) (p : ℕ) :
    ModuleCat.of k (paperGradedTor (k := k) ({0} : Family V) a p) ≅
      ModuleCat.of k (quotientPaperGradedTor (k := k) (∅ : Family V) a p) :=
  (paperGradedTorIso _ _ p).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
      (emptyPowerHomogeneousIso a) ≪≫ quotientPaperGradedTorIso _ _ p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealKoszulReorientation -/
section

/-! # The actual fine ideal Koszul complex under a change of exterior order -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice.IdealReorientation
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
attribute [local irreducible] KoszulReorientation.coordinates
universe u
section Generic
variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  (l₁ l₂ : LinearOrder V) (B : Family V)

theorem coordinates_basis_mem (p : ℕ) (a : MonomialIndex B p) :
    KoszulReorientation.coordinates (K := k) l₁ l₂ p
      ((haveI := l₁; monomialCoefficientBasis (k := k) B p) a) ∈
      (haveI := l₂; homogeneousPiece (k := k) B (haveI := l₁; monomialDegree a) p) := by
  letI := l₂
  have hb : monomialCoefficientBasis (k := k) B p a∈
      homogeneousPiece (k := k) B (monomialDegree a) p :=
    Grading.basis_mem_piece _ _ a
  rw [@monomialCoefficientBasis_apply V k _ l₂ _ B p a.1 a.2] at hb
  change KoszulReorientation.coordinates (K := k) l₁ l₂ p
    ((haveI := l₁; monomialCoefficientBasis (k := k) B p) a) ∈
      (haveI := l₂; homogeneousPiece (k := k) B (haveI := l₁; monomialDegree a) p)
  rw [@monomialCoefficientBasis_apply V k _ l₁ _ B p a.1 a.2]
  have hd : (haveI := l₁; monomialDegree a)=(haveI := l₂; monomialDegree a) := by
    ext v
    simp only [monomialDegree,Finsupp.add_apply,faceExponent_apply] <;> split_ifs <;> rfl
  rw [hd]
  have hmb : (haveI := l₁; monomialBasis (k := k) B a.2)=
      monomialBasis (k := k) B a.2 := by
    apply Subtype.ext
    rw [@monomialBasis_val V k _ l₁ _ B a.2,
      @monomialBasis_val V k _ l₂ _ B a.2]
  rw [hmb]
  obtain ⟨ε,hε⟩ := KoszulReorientation.coordinates_single (K := k) l₁ l₂ p a.1
    (monomialBasis (k := k) B a.2)
  rw [hε]
  change (ε : ℤ) • Finsupp.single a.1 (monomialBasis (k := k) B a.2)∈
    homogeneousPiece (k := k) B (monomialDegree a) p
  obtain rfl | rfl := Int.units_eq_one_or ε
  · simpa only [Units.val_one,one_smul] using hb
  · have hn : -Finsupp.single a.1 (monomialBasis (k := k) B a.2)∈
        homogeneousPiece (k := k) B (monomialDegree a) p :=
      (-(⟨Finsupp.single a.1 (monomialBasis (k := k) B a.2),hb⟩ :
        homogeneousPiece (k := k) B (monomialDegree a) p)).property
    simp only [Units.val_neg,Units.val_one]
    have he : (-1 : ℤ) • Finsupp.single a.1 (monomialBasis (k := k) B a.2)=
        -Finsupp.single a.1 (monomialBasis (k := k) B a.2) := by
      apply Finsupp.ext
      intro F
      apply Subtype.ext
      apply MvPolynomial.ext
      intro β
      simp only [Finsupp.smul_apply,Finsupp.neg_apply,Submodule.coe_smul,
        Submodule.coe_neg,MvPolynomial.coeff_smul,MvPolynomial.coeff_neg]
      exact neg_one_zsmul _
    rw [he]
    exact hn


theorem coordinates_mem (α : Exponent V) (p : ℕ)
    (x : Set.powersetCard V p →₀ monomialIdeal k B)
    (hx : x∈(haveI := l₁; homogeneousPiece (k := k) B α p)) :
    KoszulReorientation.coordinates (K := k) l₁ l₂ p x∈
      (haveI := l₂; homogeneousPiece (k := k) B α p) := by
  change x∈Grading.Piece (haveI := l₁; monomialCoefficientBasis (k := k) B p)
    (haveI := l₁; monomialDegree) α at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,ha,rfl⟩ := hx
      have h := coordinates_basis_mem (k := k) l₁ l₂ B p a
      change (haveI := l₁; monomialDegree a)=α at ha
      rw [ha] at h
      exact h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

def pieceEquiv (α : Exponent V) (p : ℕ) :
    (haveI := l₁; homogeneousPiece (k := k) B α p) ≃ₗ[k]
      (haveI := l₂; homogeneousPiece (k := k) B α p) where
  toFun x := ⟨KoszulReorientation.coordinates (K := k) l₁ l₂ p x.val,coordinates_mem l₁ l₂ B α p x.val x.property⟩
  invFun x := ⟨(KoszulReorientation.coordinates (K := k) l₁ l₂ p).symm x.val,by
    rw [KoszulReorientation.coordinates_symm]
    exact coordinates_mem l₂ l₁ B α p x.val x.property⟩
  left_inv x := Subtype.ext ((KoszulReorientation.coordinates (K := k) l₁ l₂ p).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((KoszulReorientation.coordinates (K := k) l₁ l₂ p).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

 theorem pieceEquiv_differential (α : Exponent V) (p : ℕ)
    (x : (haveI := l₁; homogeneousPiece (k := k) B α (p+1))) :
    pieceEquiv l₁ l₂ B α p ((haveI := l₁; homogeneousDifferential (k := k) B α p) x)=
      (haveI := l₂; homogeneousDifferential (k := k) B α p)
        (pieceEquiv l₁ l₂ B α (p+1) x) := by
  apply Subtype.ext
  exact KoszulReorientation.differential (K := k) l₁ l₂ p x.val

 def complex (l : LinearOrder V) (α : Exponent V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  haveI := l
  homogeneousComplex (k := k) B α

/-- The comparison commutes with the full differential in every degree. -/
def complexIso (α : Exponent V) : complex (k := k) B l₁ α ≅ complex (k := k) B l₂ α :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (pieceEquiv l₁ l₂ B α p).toModuleIso) (by
      intro i j hij
      obtain rfl : i=j+1 := hij.symm
      dsimp only [complex]
      simp only [homogeneousComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (pieceEquiv_differential l₁ l₂ B α j x).symm)


end Generic
end FourPapers.Sublattice.IdealReorientation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedTorFormula -/
section

/-! # The mixed integral Tor formula

Every family and quotient in the statement is identified with the actual
mixed-product ideal or the sum of same-color predecessor colons. The proof
uses the integral ordinary-power chain isomorphism and the literal signed
color-diagonal restrictions, retaining the full fine degree.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}

lemma coloredExponent_colorDegree (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    colorDegree (finiteRowColorVariables (coloredRows (r := r) n) 0) (coloredExponent m a)=m.degree := by
  simp only [colorDegree,finiteRowColorVariables,subsetSum,Finset.sum_filter,
    Fintype.sum_sigma,Fin.sum_univ_succ,Finsupp.degree_eq_sum]
  simp [coloredExponent] <;> congr 1 <;> exact Subsingleton.elim _ _

lemma coloredPowerFaces_iff (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (F : Finset (FiniteVariable.{u} n)) :
    koszulFaces (exponentPowerFamily (finiteRowFamily (coloredRows (r := r) n)
      (coloredFamily n E)) m.degree) (coloredExponent m a)
        (F.map (coloredBaseEmbedding (r := r))) ↔
      koszulFaces (mixedRowPowerFamily n E m) a F := by
  unfold koszulFaces
  simp only [coloredFaceExponent,coloredExponent_le_iff,coloredExponent_sub,tsub_zero,
    coloredPower_contains_iff,zero_le,true_and]

lemma coloredPowerFaces_range (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n))
    (F : Finset (FiniteVariable.{u} (coloredRows (r := r) n)))
    (hF : koszulFaces (exponentPowerFamily (finiteRowFamily (coloredRows (r := r) n)
      (coloredFamily n E)) m.degree) (coloredExponent m a) F) :
    ∃ G : Finset (FiniteVariable.{u} n),F=G.map (coloredBaseEmbedding (r := r)) := by
  have hdis := finiteSublattice_colorDiagonal_no_exterior (coloredRows (r := r) n)
    (coloredFamily n E) 0 m.degree (coloredExponent m a) (coloredExponent_colorDegree m a) F hF
  apply colorZeroFace_range a F
  intro v
  rcases v with ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro c
    have hc : (⟨0,c⟩ : FiniteVariable.{u} (coloredRows (r := r) n))∉F := by
      intro hc
      exact Finset.disjoint_left.mp hdis hc (by simp [finiteRowColorVariables])
    simp [faceExponent_apply,hc]
  · intro i c
    exact hF.1 ⟨i.succ,c⟩

variable {k : Type u} [CommRing k]

/-- Literal mixed-ideal strand equals the corresponding colored-power
strand, including coefficient and exterior fine degrees. -/
def mixedHomogeneousColorIso (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    homogeneousComplex (k := k) (mixedRowPowerFamily n E m) a ≅
      homogeneousComplex (k := k) (exponentPowerFamily
        (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) m.degree)
        (coloredExponent m a) := by
  let l := coloredBaseOrder (r := r) (n := n)
  letI := l
  let e := idealFaceRestrictionIso (k := k) (coloredBaseOrderEmbedding (r := r) (n := n))
      (koszulFaces (mixedRowPowerFamily n E m) a)
      (koszulFaces (exponentPowerFamily (finiteRowFamily (coloredRows (r := r) n)
        (coloredFamily n E)) m.degree) (coloredExponent m a))
      (koszulFaces_downward _ _) (koszulFaces_downward _ _)
      (by intro F
          exact coloredPowerFaces_iff (E := E) m a F)
      (coloredPowerFaces_range (E := E) m a)
  exact IdealReorientation.complexIso (finiteVariableLinearOrder n) l
    (mixedRowPowerFamily n E m) a ≪≫
      (idealTotalKoszulIso (mixedRowPowerFamily n E m) a).symm ≪≫ e ≪≫
        idealTotalKoszulIso _ _

/-- The fine-graded Tor of the actual mixed product. The equality
`mixedRowPowerFamily_ideal` identifies its coefficient ideal literally with
`powerProduct (coloredIdeals n E) m` over every coefficient ring. -/
abbrev mixedProductGradedTor (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :=
  paperGradedTor (k := k) (mixedRowPowerFamily n E m) a p

def mixedProductColorTorIso (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (mixedProductGradedTor (E := E) (k := k) m a p) ≅
      ModuleCat.of k (paperGradedTor (k := k) (exponentPowerFamily
        (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) m.degree)
        (coloredExponent m a) p) :=
  (paperGradedTorIso _ _ p).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
      (mixedHomogeneousColorIso (E := E) m a) ≪≫ paperGradedTorIso _ _ p

/-- The paper's exact prescribed-color multichains, with nonnegative
residual fine degree. Terms with negative residual degree are absent. -/
abbrev MixedAdmissibleChain (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :=
  {w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m.degree //
    chainColorCount E w=m ∧ chainBaseShift E w≤a}

def mixedAdmissibleChainEquiv (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    MixedAdmissibleChain (E := E) m a ≃
      AdmissibleChain (coloredRows (r := r) n) (coloredFamily n E) m.degree
        (coloredExponent m a) where
  toFun w := ⟨w.val,(coloredChain_admissible_iff E m a w.val).mpr w.property⟩
  invFun w := ⟨w.val,(coloredChain_admissible_iff E m a w.val).mp w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma coloredChainResidual (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (w : MixedAdmissibleChain (E := E) m a) :
    coloredExponent m a-finiteChainShift (coloredRows (r := r) n) w.val=
      coloredExponent 0 (a-chainBaseShift E w.val) := by
  rw [coloredChainShift,coloredExponent_sub,w.property.1,tsub_self]

/-- The coefficient family in the right-hand side is exactly the sum of
same-color *ideal colons*, not merely a similar monomial ideal. -/
theorem sameColorChainCoefficientFamily_ideal {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    monomialIdeal k (sameColorChainCoefficientFamily E w)=
      ⨆s,finitePredecessorColon n (k := k) (E ((w.val s).val 0))
        (fun i => (w.val s).val i.succ) := by
  simp_rw [finitePredecessorColon_eq]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp ha
    exact (Ideal.mem_iSup_of_mem s (Ideal.subset_span ⟨a,hs,rfl⟩))
  · apply iSup_le
    intro s
    apply Ideal.span_mono
    exact Set.image_mono (fun a ha => Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ s,ha⟩)

/-- **Corollary 7.2, positive total mixed degree.** All coefficient rings,
all prescribed color multiplicities (including zero colors), all fine
degrees, and all homological degrees are retained. -/
def corollary72_positive (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (hm : 0< m.degree)
    (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (mixedProductGradedTor (E := E) (k := k) m a p) ≅
      ModuleCat.of k (∀w : MixedAdmissibleChain (E := E) m a,
        quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-chainBaseShift E w.val) p) := by
  let e := mixedAdmissibleChainEquiv (E := E) m a
  let Q : AdmissibleChain (coloredRows (r := r) n) (coloredFamily n E)
      m.degree (coloredExponent m a) → Type u := fun w =>
    quotientPaperGradedTor (k := k) (finiteChainCoefficientFamily (coloredRows (r := r) n) w.val)
      (coloredExponent m a-finiteChainShift (coloredRows (r := r) n) w.val) p
  refine mixedProductColorTorIso (E := E) m a p ≪≫
    allRingPowerTorIso ((coloredLatticeClosed_iff n E).mp hE)
      m.degree hm (coloredExponent m a) p ≪≫
    (LinearEquiv.piCongrLeft k Q e).symm.toModuleIso ≪≫ ?_
  let eW (w : MixedAdmissibleChain (E := E) m a) :
      ModuleCat.of k (Q (e w)) ≅
        ModuleCat.of k (quotientPaperGradedTor (k := k)
          (sameColorChainCoefficientFamily E w.val) (a-chainBaseShift E w.val) p) := by
    change ModuleCat.of k (quotientPaperGradedTor (k := k)
      (finiteChainCoefficientFamily (coloredRows (r := r) n) w.val)
        (coloredExponent m a-finiteChainShift (coloredRows (r := r) n) w.val) p) ≅ _
    rw [coloredChainResidual]
    exact coloredCoefficientTorIso E w.val (a-chainBaseShift E w.val) p
  exact (LinearEquiv.piCongrRight (fun w => (eW w).toLinearEquiv)).toModuleIso


def emptyColoredChain : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) 0 :=
  ⟨fun i => Fin.elim0 i,by intro i; exact Fin.elim0 i⟩

instance mixedAdmissibleChain_zero_unique (a : Exponent (FiniteVariable.{u} n)) :
    Unique (MixedAdmissibleChain (E := E) 0 a) where
  default := ⟨emptyColoredChain,by simp [chainColorCount,chainBaseShift,emptyColoredChain]⟩
  uniq w := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

@[simp] theorem sameColorChainCoefficientFamily_empty
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) 0) :
    sameColorChainCoefficientFamily E w=∅ := by simp [sameColorChainCoefficientFamily]

@[simp] theorem chainBaseShift_empty
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) 0) :
    chainBaseShift E w=0 := by simp [chainBaseShift]

/-- The unique empty chain gives the identity for the polynomial ring,
with no omitted homological or fine degree. -/
def corollary72_zero (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (mixedProductGradedTor (E := E) (k := k) 0 a p) ≅
      ModuleCat.of k (∀w : MixedAdmissibleChain (E := E) 0 a,
        quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-chainBaseShift E w.val) p) := by
  have hB : mixedRowPowerFamily n E 0=({0} : Family (FiniteVariable.{u} n)) :=
    mixedPowerFamily_zero _
  have e₀ : ModuleCat.of k (mixedProductGradedTor (E := E) (k := k) 0 a p) ≅
      ModuleCat.of k (paperGradedTor (k := k) ({0} : Family (FiniteVariable.{u} n)) a p) := by
    change ModuleCat.of k (paperGradedTor (k := k) (mixedRowPowerFamily n E 0) a p) ≅ _
    rw [hB]
  refine e₀ ≪≫ emptyPowerTorIso (k := k) a p ≪≫ ?_
  have hFam (w : MixedAdmissibleChain (E := E) 0 a) :
      sameColorChainCoefficientFamily E w.val=∅ := sameColorChainCoefficientFamily_empty w.val
  have hShift (w : MixedAdmissibleChain (E := E) 0 a) :
      a-chainBaseShift E w.val=a := by rw [chainBaseShift_empty,tsub_zero]
  let Q : MixedAdmissibleChain (E := E) 0 a → Type u := fun w =>
    quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
      (a-chainBaseShift E w.val) p
  have eQ : ModuleCat.of k (quotientPaperGradedTor (k := k)
      (∅ : Family (FiniteVariable.{u} n)) a p) ≅ ModuleCat.of k (Q default) := by
    dsimp only [Q]
    rw [hFam,hShift]
  exact eQ ≪≫ (LinearEquiv.piUnique k Q).symm.toModuleIso

/-- The natural fine-degree mixed Tor decomposition, for every mixed
exponent including the unique empty product. -/
def corollary72_natural (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (mixedProductGradedTor (E := E) (k := k) m a p) ≅
      ModuleCat.of k (∀w : MixedAdmissibleChain (E := E) m a,
        quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-chainBaseShift E w.val) p) := by
  by_cases hm : m=0
  · subst m
    exact corollary72_zero a p
  · have hp : 0< m.degree := Nat.pos_of_ne_zero (by
      intro hd
      have hh : m=0 := (Finsupp.degree_eq_zero_iff m).mp hd
      exact hm hh)
    exact corollary72_positive hE m hp a p

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredLeadingCoefficients -/
section

/-! # Leading terms and exact color-coefficient extraction -/
section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open scoped MonomialOrder
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {k : Type u} [CommRing k]

lemma coloredExponent_reconstruct
    (b : Exponent (FiniteVariable.{u} (coloredRows (r := r) n))) :
    coloredExponent (colorExponent b) (baseExponent b)=b := by
  ext ⟨i,j⟩
  revert j
  exact Fin.cases (fun _ => rfl) (fun _ _ => rfl) i

lemma coloredExponent_injective :
    Function.Injective (fun b : (ULift.{u} (Fin r)→₀ℕ)×Exponent (FiniteVariable.{u} n) =>
      coloredExponent b.1 b.2) := by
  intro a b h
  apply Prod.ext
  · simpa only [colorExponent_coloredExponent] using congrArg colorExponent h
  · simpa only [baseExponent_coloredExponent] using congrArg baseExponent h

lemma coloredExponent_add (a b : ULift.{u} (Fin r)→₀ℕ)
    (v w : Exponent (FiniteVariable.{u} n)) :
    coloredExponent (a+b) (v+w)=coloredExponent a v+coloredExponent b w := by
  ext ⟨i,j⟩
  revert j
  exact Fin.cases (fun _ => rfl) (fun _ _ => rfl) i

lemma base_mapDomain (a : Exponent (FiniteVariable.{u} n)) :
    a.mapDomain (coloredBaseEmbedding (r := r))=coloredExponent 0 a := by
  ext ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro c
    exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨v,hv⟩; cases hv)
  · intro i c
    exact Finsupp.mapDomain_apply_of_injective (coloredBaseEmbedding (r := r)).injective a ⟨i,c⟩

lemma coloredPolynomialEquiv_coeff
    (f : MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) k))
    (m : ULift.{u} (Fin r)→₀ℕ) (a : Exponent (FiniteVariable.{u} n)) :
    (coloredPolynomialEquiv (k := k) n f).coeff (coloredExponent m a)=(f.coeff m).coeff a := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,MvPolynomial.coeff_add,hf,hg]
  | monomial l f =>
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => simp only [map_add,MvPolynomial.coeff_add,hf,hg]
    | monomial b c =>
      have he : monomial l (monomial b c)=c •
          (monomial l (monomial b 1) :
            MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) k)) := by
        simp [smul_monomial]
      rw [he,map_smul,coloredPolynomialEquiv_monomial,coeff_smul,coeff_monomial]
      by_cases hl : l=m
      · subst l
        by_cases hb : b=a
        · subst b; simp
        · have hh : coloredExponent m b≠coloredExponent m a := by
            intro h
            apply hb
            simpa only [baseExponent_coloredExponent] using congrArg baseExponent h
          simp [coeff_monomial,hb,hh]
      · have hh : coloredExponent l b≠coloredExponent m a := by
          intro h
          apply hl
          simpa only [colorExponent_coloredExponent] using congrArg colorExponent h
        simp [coeff_monomial,hl,hh]

lemma coloredPolynomialEquiv_monomial_factor (m : ULift.{u} (Fin r)→₀ℕ)
    (f : MvPolynomial (FiniteVariable.{u} n) k) :
    coloredPolynomialEquiv (k := k) n (monomial m f)=
      monomial (coloredExponent m 0) 1 * rename (coloredBaseEmbedding (r := r)) f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,hf,hg,mul_add]
  | monomial a c =>
    have he : monomial m (monomial a c)=c •
        (monomial m (monomial a 1) :
          MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) k)) := by
      simp [smul_monomial]
    rw [he,map_smul,coloredPolynomialEquiv_monomial,rename_monomial,base_mapDomain,
      monomial_mul,one_mul]
    simp only [smul_monomial,smul_eq_mul,mul_one]
    rw [show coloredExponent m a = coloredExponent m 0 + coloredExponent 0 a from by
      simpa only [add_zero, zero_add] using coloredExponent_add m 0 0 a]

variable (M : MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)))

def coloredRestrictedOrder : MonomialOrder (FiniteVariable.{u} n) :=
  monomialOrderRestriction M coloredBaseEmbedding

lemma coloredRestrictedOrder_compare (m : ULift.{u} (Fin r)→₀ℕ)
    (a b : Exponent (FiniteVariable.{u} n)) :
    coloredExponent m a ≼[M] coloredExponent m b ↔ a ≼[coloredRestrictedOrder M] b := by
  have ha : coloredExponent m a=coloredExponent m 0+coloredExponent 0 a := by
    simpa using coloredExponent_add m 0 0 a
  have hb : coloredExponent m b=coloredExponent m 0+coloredExponent 0 b := by
    simpa using coloredExponent_add m 0 0 b
  rw [ha,hb,map_add,map_add,add_le_add_iff_left]
  change M.toSyn (coloredExponent 0 a)≤M.toSyn (coloredExponent 0 b) ↔ _
  rw [coloredRestrictedOrder,monomialOrderRestriction_le,base_mapDomain,base_mapDomain]

lemma coloredLeadingTerm_monomial [NoZeroDivisors k]
    (m : ULift.{u} (Fin r)→₀ℕ) (f : MvPolynomial (FiniteVariable.{u} n) k) :
    M.leadingTerm (coloredPolynomialEquiv (k := k) n (monomial m f))=
      coloredPolynomialEquiv (k := k) n (monomial m ((coloredRestrictedOrder M).leadingTerm f)) := by
  rw [coloredPolynomialEquiv_monomial_factor,M.leadingTerm_mul,M.leadingTerm_monomial,
    M.leadingTerm_rename (monomialOrderRestriction_le M coloredBaseEmbedding),
    coloredPolynomialEquiv_monomial_factor]
  rfl

/-- The leading coefficient polynomial in its actual color component has
exactly the base part of the original leading exponent. -/
lemma coloredLeadingCoefficient_degree [Nontrivial k]
    (f : MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) k))
    (hf : f≠0) :
    (coloredRestrictedOrder M).degree
      (f.coeff (colorExponent (M.degree (coloredPolynomialEquiv (k := k) n f))))=
        baseExponent (M.degree (coloredPolynomialEquiv (k := k) n f)) := by
  let q := coloredPolynomialEquiv (k := k) n f
  let c := colorExponent (M.degree q)
  let b := baseExponent (M.degree q)
  have hq : q≠0 := (coloredPolynomialEquiv (k := k) n).map_ne_zero_iff.mpr hf
  have hb : b∈(f.coeff c).support := by
    rw [mem_support_iff,← coloredPolynomialEquiv_coeff]
    change q.coeff (coloredExponent c b)≠0
    rw [coloredExponent_reconstruct]
    exact M.leadingCoeff_ne_zero_iff.mpr hq
  apply (coloredRestrictedOrder M).toSyn.injective
  apply le_antisymm
  · apply (coloredRestrictedOrder M).degree_le_iff.mpr
    intro a ha
    apply (coloredRestrictedOrder_compare M c a b).mp
    have hmem : coloredExponent c a∈q.support := by
      rw [mem_support_iff,coloredPolynomialEquiv_coeff]
      exact mem_support_iff.mp ha
    have he := M.le_degree hmem
    simpa only [c,b,coloredExponent_reconstruct] using he
  · exact (coloredRestrictedOrder M).le_degree hb

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedExteriorMap -/
section

/-! # Exterior-algebra maps for ordered variable inclusions

The map is the ordinary functorial exterior-algebra map. Its equality on
ordered face bases verifies all signs, including in characteristic two.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.OrderedExteriorMap
open Classical CommAlg
universe u
variable {K V W : Type u} [CommRing K] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W] (e : V ↪o W)

def vector : (V → K) →ₗ[K] (W → K) :=
  (Pi.basisFun K V).constr K (fun v => Pi.basisFun K W (e v))

@[simp] lemma vector_basis (v : V) :
    vector (K := K) e (Pi.basisFun K V v) = Pi.basisFun K W (e v) := by
  simp [vector]

def exterior : Simplicial.Ambient V K →ₐ[K] Simplicial.Ambient W K :=
  ExteriorAlgebra.map (vector (K := K) e)

@[simp] lemma exterior_basis (F : Finset V) :
    exterior (K := K) e (Simplicial.basis F) = Simplicial.basis (F.map e.toEmbedding) := by
  have hs : F.sort.map e = (F.map e.toEmbedding).sort :=
    Finset.map_sort e.toEmbedding F (· ≤ ·) (· ≤ ·) (fun _ _ _ _ => e.le_iff_le.symm)
  simp only [exterior, Simplicial.basis, Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    map_list_prod, List.map_map, Function.comp_def, ExteriorAlgebra.map_apply_ι,
    vector_basis]
  rw [← hs]
  simp only [List.map_map, Function.comp_def]

lemma vector_boundary_functional :
    (Fintype.linearCombination K (fun _ : W => (1 : K))).comp (vector (K := K) e) =
      Fintype.linearCombination K (fun _ : V => (1 : K)) := by
  apply (Pi.basisFun K V).ext
  intro v
  change (Fintype.linearCombination K (fun _ : W => (1 : K)))
      (vector (K := K) e ((Pi.basisFun K V) v)) =
    (Fintype.linearCombination K (fun _ : V => (1 : K))) ((Pi.basisFun K V) v)
  rw [vector_basis]
  simp [Pi.basisFun_apply, Fintype.linearCombination_apply_single]

lemma exterior_boundary (z : Simplicial.Ambient V K) :
    exterior e (Simplicial.boundary z) = Simplicial.boundary (exterior e z) := by
  change ExteriorAlgebra.map (vector e)
    (CliffordAlgebra.contractLeft (Fintype.linearCombination K (fun _ : V => (1 : K))) z) =
      CliffordAlgebra.contractLeft (Fintype.linearCombination K (fun _ : W => (1 : K)))
        (ExteriorAlgebra.map (vector e) z)
  rw [ExteriorAlgebra.contractLeft_map, vector_boundary_functional]

end FourPapers.OrderedExteriorMap

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedReesDiagonalBasis -/
section

/-! # Literal tensor coordinates on the minimum-color Rees diagonal

The source basis belongs to the actual mixed-product coefficient ideals.
The target basis is the restricted basis of the actual diagonal range.
The index bijection records both the coefficient monomial and its exterior
face; it uses the proved absence of exterior color variables.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}
variable {k : Type u} [CommRing k]

abbrev MixedCoefficientIndex (E : Fin r → Finset (FiniteTuple n)) :=
  Σ a : ULift.{u} (Fin r) →₀ ℕ, {b : Exponent (FiniteVariable.{u} n) //
    Contains (mixedRowPowerFamily n E a) b}

abbrev MixedTensorIndex (E : Fin r → Finset (FiniteTuple n)) :=
  MixedCoefficientIndex.{u} E × Finset (FiniteVariable.{u} n)

abbrev MinimumColorIndex (E : Fin r → Finset (FiniteTuple n)) :=
  {a : ReesCoordinateBasisIndex.{u} (coloredFamily n E) //
    coloredFineColorDegree a.1 = coloredFineReesDegree a.1}

def mixedPowerIdealEquiv (a : ULift.{u} (Fin r) →₀ ℕ) :
    monomialIdeal k (mixedRowPowerFamily n E a) ≃ₗ[k]
      MixedTransfer.idealPowerPiece (coloredIdeals (k := k) n E) a where
  toFun x := ⟨x.val, by
    change x.val ∈ powerProduct (coloredIdeals (k := k) n E) a
    rw [← mixedRowPowerFamily_ideal]
    exact x.property⟩
  invFun x := ⟨x.val, by rw [mixedRowPowerFamily_ideal]; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mixedPowerMonomialBasis (a : ULift.{u} (Fin r) →₀ ℕ) :
    Module.Basis {b : Exponent (FiniteVariable.{u} n) // Contains (mixedRowPowerFamily n E a) b} k
      (MixedTransfer.idealPowerPiece (coloredIdeals (k := k) n E) a) :=
  (monomialBasis (k := k) (mixedRowPowerFamily n E a)).map (mixedPowerIdealEquiv a)

@[simp] lemma mixedPowerMonomialBasis_val (a : ULift.{u} (Fin r) →₀ ℕ)
    (b : {b : Exponent (FiniteVariable.{u} n) // Contains (mixedRowPowerFamily n E a) b}) :
    (mixedPowerMonomialBasis (k := k) a b).val = monomial b.val 1 := by
  rw [mixedPowerMonomialBasis, Module.Basis.map_apply]
  exact monomialBasis_val _ b

def mixedCoefficientBasis : Module.Basis (MixedCoefficientIndex.{u} E) k
    (MixedTransfer.coefficientRees (coloredIdeals (k := k) n E)) :=
  gradedCoefficientBasis (MixedTransfer.idealPowerPiece (coloredIdeals (k := k) n E))
    (MixedTransfer.idealPowerPiece_one _) (MixedTransfer.idealPowerPiece_mul _)
    (mixedPowerMonomialBasis (E := E) (k := k))

lemma mixedCoefficientBasis_val (a : MixedCoefficientIndex.{u} E) :
    (mixedCoefficientBasis (k := k) a).val = AddMonoidAlgebra.single a.1 (monomial a.2.val 1) := by
  rw [mixedCoefficientBasis, gradedCoefficientBasis_apply, coefficientSingle_val,
    mixedPowerMonomialBasis_val]

/-- An ordered basis of the actual exterior algebra. The induced order is
bound explicitly here; it is not registered as an instance with an
uninferable color parameter. The exterior algebra itself is unchanged. -/
abbrev mixedExteriorBasis (r : ℕ) :
    Module.Basis (Finset (FiniteVariable.{u} n)) k
      (Simplicial.Ambient (FiniteVariable.{u} n) k) := by
  letI := coloredBaseOrder (r := r) (n := n)
  exact Simplicial.basis

/-- The ordinary exterior-algebra map induced by inclusion of the old
variables. In the chosen source basis its face formula has no extra sign. -/
abbrev mixedExteriorMap (r : ℕ) :
    Simplicial.Ambient (FiniteVariable.{u} n) k →ₐ[k]
      Simplicial.Ambient (FiniteVariable.{u} (coloredRows (r := r) n)) k := by
  letI := coloredBaseOrder (r := r) (n := n)
  exact OrderedExteriorMap.exterior coloredBaseOrderEmbedding

lemma mixedExteriorMap_basis (F : Finset (FiniteVariable.{u} n)) :
    mixedExteriorMap (k := k) r (mixedExteriorBasis r F) =
      Simplicial.basis (F.map (coloredBaseEmbedding (r := r))) := by
  letI := coloredBaseOrder (r := r) (n := n)
  exact OrderedExteriorMap.exterior_basis coloredBaseOrderEmbedding F

lemma mixedExteriorMap_boundary (z : Simplicial.Ambient (FiniteVariable.{u} n) k) :
    mixedExteriorMap r (Simplicial.boundary z) =
      Simplicial.boundary (mixedExteriorMap r z) := by
  letI := coloredBaseOrder (r := r) (n := n)
  exact OrderedExteriorMap.exterior_boundary coloredBaseOrderEmbedding z

def mixedTensorBasis : Module.Basis (MixedTensorIndex.{u} E) k
    (MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E)) :=
  (mixedCoefficientBasis (k := k)).tensorProduct (mixedExteriorBasis r)

def mixedMinimumIndex (a : MixedTensorIndex.{u} E) : MinimumColorIndex.{u} E :=
  ⟨⟨(a.1.1.degree, coloredExponent a.1.1 (a.1.2.val + faceExponent a.2)),
    ⟨a.2.map coloredBaseEmbedding, (coloredPowerFaces_iff _ _ _).mpr
      ⟨le_add_of_nonneg_left zero_le, by simpa only [add_tsub_cancel_right] using a.1.2.property⟩⟩⟩,
    coloredExponent_colorDegree _ _⟩

lemma mixedMinimumIndex_injective : Function.Injective (mixedMinimumIndex.{u} (E := E)) := by
  rintro ⟨a,F⟩ ⟨b,G⟩ h
  have hF : F=G := Finset.map_injective coloredBaseEmbedding
    (congrArg (fun x : MinimumColorIndex.{u} E => x.val.2.val) h)
  subst G
  refine Prod.ext ?_ rfl
  have hγ := congrArg (fun x : MinimumColorIndex.{u} E => x.val.1.2) h
  have hc : a.1=b.1 := by
    simpa only [mixedMinimumIndex,colorExponent_coloredExponent] using congrArg colorExponent hγ
  have hb' : a.2.val+faceExponent F=b.2.val+faceExponent F := by
    simpa only [mixedMinimumIndex,baseExponent_coloredExponent] using congrArg baseExponent hγ
  have hb : a.2.val=b.2.val := add_right_cancel hb'
  exact Sigma.subtype_ext hc hb

lemma mixedMinimumIndex_surjective : Function.Surjective (mixedMinimumIndex.{u} (E := E)) := by
  rintro ⟨⟨⟨s,γ⟩,F,hF⟩,hmin⟩
  have hd : (colorExponent γ).degree=s := by
    rw [← coloredExponent_colorDegree (colorExponent γ) (baseExponent γ),
      coloredExponent_reconstruct]
    exact hmin
  have hcolored : koszulFaces (exponentPowerFamily
      (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) (colorExponent γ).degree)
      (coloredExponent (colorExponent γ) (baseExponent γ)) F := by
    simpa only [hd,coloredExponent_reconstruct] using hF
  obtain ⟨G,hG⟩ := coloredPowerFaces_range (E := E) _ _ F hcolored
  subst F
  have hg := (coloredPowerFaces_iff (E := E) (colorExponent γ) (baseExponent γ) G).mp hcolored
  let a : MixedCoefficientIndex.{u} E :=
    ⟨colorExponent γ,⟨baseExponent γ-faceExponent G,hg.2⟩⟩
  refine ⟨(a,G),?_⟩
  apply Subtype.ext
  apply Sigma.subtype_ext
  · apply Prod.ext hd
    change coloredExponent (colorExponent γ) (baseExponent γ-faceExponent G+faceExponent G)=γ
    rw [tsub_add_cancel_of_le hg.1,coloredExponent_reconstruct]
  · rfl

def mixedMinimumIndexEquiv : MixedTensorIndex.{u} E ≃ MinimumColorIndex.{u} E :=
  Equiv.ofBijective mixedMinimumIndex ⟨mixedMinimumIndex_injective,mixedMinimumIndex_surjective⟩

variable (hE : ColoredLatticeClosed n E)

abbrev minimumColorProjection :=
  MinimumDegreeDiagonal.projection (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree (coloredPowerFace_below_zero (E := E))

lemma minimumColorProjection_basis (a : ReesCoordinateBasisIndex.{u} (coloredFamily n E)) :
    minimumColorProjection (k := k) hE (reesCoordinateBasis (coloredReesClosure hE) a) =
      if coloredFineColorDegree a.1=coloredFineReesDegree a.1
      then reesCoordinateBasis (coloredReesClosure hE) a else 0 := by
  rcases a with ⟨g,F⟩
  let x : coloredPowerPieces (E := E) (k := k) g :=
    totalFaceBasis (koszulFaces (exponentPowerFamily
      (finiteRowFamily (coloredRows (r := r) n) (coloredFamily n E)) g.1) g.2) F
  have hs : reesCoordinateBasis (k := k) (coloredReesClosure hE) ⟨g,F⟩ =
      coefficientSingle (coloredPowerPieces (E := E) (k := k))
        (powerFace_one_mem (coloredReesClosure hE))
        (powerFace_mul_mem (coloredReesClosure hE)) g x := by
    apply Subtype.ext
    rw [reesCoordinateBasis_val,coefficientSingle_val]
    exact congrArg (AddMonoidAlgebra.single g) (totalFaceBasis_val _ F).symm
  rw [hs]
  exact MinimumDegreeDiagonal.projectionLinear_single
    (coloredPowerPieces (E := E) (k := k))
    (powerFace_one_mem (coloredReesClosure hE))
    (powerFace_mul_mem (coloredReesClosure hE))
    coloredFineColorDegree coloredFineReesDegree g x

def minimumColorBasis : Module.Basis (MinimumColorIndex.{u} E) k
    (minimumColorReesAlgebra (k := k) hE) :=
  ProjectionRangeBasis.basis (reesCoordinateBasis (k := k) (coloredReesClosure hE))
    (fun a => coloredFineColorDegree a.1=coloredFineReesDegree a.1)
    (minimumColorProjection hE) (minimumColorProjection_basis hE)

lemma minimumColorBasis_val (a : MinimumColorIndex.{u} E) :
    (minimumColorBasis (k := k) hE a).val.val =
      AddMonoidAlgebra.single a.val.1 (Simplicial.basis a.val.2.val) := by
  have hv : (minimumColorBasis (k := k) hE a).val =
      reesCoordinateBasis (k := k) (coloredReesClosure hE) a.val :=
    ProjectionRangeBasis.basis_val (reesCoordinateBasis (k := k) (coloredReesClosure hE))
      (fun b => coloredFineColorDegree b.1=coloredFineReesDegree b.1)
      (minimumColorProjection hE) (minimumColorProjection_basis hE) a
  exact (congrArg (fun x : reesKoszulCoordinateAlgebra (k := k) (coloredReesClosure hE) =>
    x.val) hv).trans (reesCoordinateBasis_val (coloredReesClosure hE) a.val)

def mixedMinimumLinearEquiv :
    MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E) ≃ₗ[k]
      minimumColorReesAlgebra (k := k) hE :=
  mixedTensorBasis.equiv (minimumColorBasis hE) mixedMinimumIndexEquiv

lemma mixedMinimumLinearEquiv_basis (a : MixedCoefficientIndex.{u} E)
    (F : Finset (FiniteVariable.{u} n)) :
    (mixedMinimumLinearEquiv (k := k) hE (mixedCoefficientBasis a ⊗ₜ[k] mixedExteriorBasis r F)).val.val =
      AddMonoidAlgebra.single (a.1.degree,coloredExponent a.1 (a.2.val+faceExponent F))
        (Simplicial.basis (F.map coloredBaseEmbedding)) := by
  have hh := Module.Basis.equiv_apply mixedTensorBasis (a,F) (minimumColorBasis (k := k) hE)
    mixedMinimumIndexEquiv
  have hv := congrArg (fun x : minimumColorReesAlgebra (k := k) hE => x.val.val) hh
  rw [minimumColorBasis_val] at hv
  simpa only [mixedMinimumLinearEquiv,mixedTensorBasis,
    Module.Basis.tensorProduct_apply,mixedMinimumIndexEquiv,
    Equiv.coe_ofBijective,mixedMinimumIndex] using hv

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedReesDiagonalAlgebra -/
section

/-! # The multi-Rees algebra and its literal Koszul differential

The basis comparison is multiplicative and sends the actual variable-action
Koszul differential to the restricted exterior boundary. Thus the induced
homology equivalence is an algebra equivalence on actual cycles modulo
boundaries, rather than a numerical comparison.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}
variable {k : Type u} [Field k]

def mixedCoefficientIndexAdd (a b : MixedCoefficientIndex.{u} E) : MixedCoefficientIndex.{u} E :=
  ⟨a.1+b.1,⟨a.2.val+b.2.val,by
    apply (monomial_mem_iff (k := ULift.{u} ℤ) _ _).mp
    rw [mixedRowPowerFamily_ideal,powerProduct_add]
    have ha := (monomial_mem_iff (k := ULift.{u} ℤ) _ _).mpr a.2.property
    have hb := (monomial_mem_iff (k := ULift.{u} ℤ) _ _).mpr b.2.property
    rw [mixedRowPowerFamily_ideal] at ha hb
    simpa only [monomial_mul_monomial,one_mul] using Ideal.mul_mem_mul ha hb⟩⟩

lemma mixedCoefficientBasis_mul (a b : MixedCoefficientIndex.{u} E) :
    mixedCoefficientBasis (k := k) a * mixedCoefficientBasis b =
      mixedCoefficientBasis (mixedCoefficientIndexAdd a b) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul,mixedCoefficientBasis_val,
    AddMonoidAlgebra.single_mul_single,monomial_mul_monomial,one_mul]
  rfl

def mixedCoefficientZero : MixedCoefficientIndex.{u} E :=
  ⟨0,⟨0,by simp [mixedRowPowerFamily,mixedPowerFamily_zero,Contains]⟩⟩

lemma mixedCoefficientBasis_zero : mixedCoefficientBasis (E := E) (k := k) mixedCoefficientZero=1 := by
  apply Subtype.ext
  rw [mixedCoefficientBasis_val]
  simp [mixedCoefficientZero,AddMonoidAlgebra.one_def]

variable (hE : ColoredLatticeClosed n E)

lemma mixedMinimumLinearEquiv_mul_basis (a b : MixedTensorIndex.{u} E) :
    mixedMinimumLinearEquiv (k := k) hE (mixedTensorBasis a * mixedTensorBasis b) =
      mixedMinimumLinearEquiv hE (mixedTensorBasis a) * mixedMinimumLinearEquiv hE (mixedTensorBasis b) := by
  letI := coloredBaseOrder (r := r) (n := n)
  rcases a with ⟨a,F⟩
  rcases b with ⟨b,G⟩
  simp only [mixedTensorBasis,Module.Basis.tensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul,mixedCoefficientBasis_mul]
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subalgebra.coe_mul,mixedMinimumLinearEquiv_basis,
    AddMonoidAlgebra.single_mul_single]
  by_cases hFG : Disjoint F G
  · have he := congrArg (mixedExteriorMap (k := k) r)
      (faceBasis_mul_of_disjoint (k := k) F G hFG)
    simp only [map_mul,map_zsmul_unit,mixedExteriorMap_basis] at he
    rw [he,faceBasis_mul_of_disjoint F G hFG,TensorProduct.tmul_smul]
    erw [LinearMapClass.map_smul_of_tower (S := k)]
    simp only [Subalgebra.coe_smul]
    rw [mixedMinimumLinearEquiv_basis,← AddMonoidAlgebra.smul_single]
    congr 2
    apply Prod.ext
    · exact map_add Finsupp.degree a.1 b.1
    · dsimp only [mixedCoefficientIndexAdd]
      letI : DecidableEq (FiniteVariable.{u} n) :=
        (coloredBaseOrder (r := r) (n := n)).toDecidableEq
      change coloredExponent (a.1+b.1) (a.2.val+b.2.val+faceExponent (F∪G)) =
        coloredExponent a.1 (a.2.val+faceExponent F)+coloredExponent b.1 (b.2.val+faceExponent G)
      rw [← coloredExponent_add,faceExponent_union_of_disjoint F G hFG]
      congr 1
      abel
  · have he := congrArg (mixedExteriorMap (k := k) r)
      (faceBasis_mul_of_not_disjoint (k := k) F G hFG)
    simp only [map_mul,map_zero,mixedExteriorMap_basis] at he
    rw [he,faceBasis_mul_of_not_disjoint F G hFG]
    simp only [TensorProduct.tmul_zero,LinearEquiv.map_zero,
      Subalgebra.coe_zero,AddMonoidAlgebra.single_zero]

lemma mixedMinimumLinearEquiv_mul
    (x y : MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E)) :
    mixedMinimumLinearEquiv hE (x*y)=mixedMinimumLinearEquiv hE x * mixedMinimumLinearEquiv hE y := by
  let f := (mixedMinimumLinearEquiv (k := k) hE).toLinearMap
  have hh : (LinearMap.mul k (MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E))).compr₂ f =
      (LinearMap.mul k (minimumColorReesAlgebra (k := k) hE)).compl₁₂ f f := by
    apply mixedTensorBasis.ext
    intro a
    apply mixedTensorBasis.ext
    intro b
    exact mixedMinimumLinearEquiv_mul_basis hE a b
  exact LinearMap.congr_fun (LinearMap.congr_fun hh x) y

lemma mixedMinimumLinearEquiv_one : mixedMinimumLinearEquiv (k := k) hE 1=1 := by
  letI := coloredBaseOrder (r := r) (n := n)
  have h1 : (1 : MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E))=
      mixedCoefficientBasis mixedCoefficientZero ⊗ₜ[k] mixedExteriorBasis r (∅ : Finset (FiniteVariable.{u} n)) := by
    rw [mixedCoefficientBasis_zero,faceBasis_empty]
    rfl
  have hz : coloredExponent.{u} (r := r) (n := n) 0 0=0 := by
    ext ⟨i,j⟩
    revert j
    exact Fin.cases (fun _ => rfl) (fun _ _ => rfl) i
  apply Subtype.ext
  apply Subtype.ext
  rw [h1,mixedMinimumLinearEquiv_basis]
  simp [mixedCoefficientZero,faceBasis_empty,faceExponent_empty,hz,AddMonoidAlgebra.one_def]
  rfl

def mixedMinimumAlgEquiv :
    MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E) ≃ₐ[k]
      minimumColorReesAlgebra (k := k) hE :=
  AlgEquiv.ofLinearEquiv (mixedMinimumLinearEquiv hE)
    (mixedMinimumLinearEquiv_one hE) (mixedMinimumLinearEquiv_mul hE)

def mixedCoefficientBaseIndex (v : FiniteVariable.{u} n) : MixedCoefficientIndex.{u} E :=
  ⟨0,⟨Finsupp.single v 1,by simp [mixedRowPowerFamily,mixedPowerFamily_zero,Contains]⟩⟩

lemma mixedCoefficientBaseVariable_basis (v : FiniteVariable.{u} n) :
    MixedTransfer.idealReesBaseVariable (coloredIdeals (k := k) n E) v =
      mixedCoefficientBasis (mixedCoefficientBaseIndex v) := by
  apply Subtype.ext
  rw [mixedCoefficientBasis_val]
  rfl

lemma mixedMinimum_contraction_basis (a : MixedCoefficientIndex.{u} E)
    (F : Finset (FiniteVariable.{u} n)) (v : FiniteVariable.{u} n) :
    (mixedMinimumLinearEquiv (k := k) hE
      ((MixedTransfer.idealReesBaseVariable (coloredIdeals n E) v * mixedCoefficientBasis a) ⊗ₜ[k]
        Simplicial.contraction v (mixedExteriorBasis r F))).val.val =
      AddMonoidAlgebra.single (a.1.degree,coloredExponent a.1 (a.2.val+faceExponent F))
        (mixedExteriorMap r
          (Simplicial.contraction v (mixedExteriorBasis r F))) := by
  letI := coloredBaseOrder (r := r) (n := n)
  rw [mixedCoefficientBaseVariable_basis,mixedCoefficientBasis_mul,Simplicial.contraction_basis]
  by_cases hv : v∈F
  · rw [if_pos hv,TensorProduct.tmul_smul]
    erw [LinearMapClass.map_smul_of_tower (S := k)]
    simp only [Subalgebra.coe_smul]
    rw [mixedMinimumLinearEquiv_basis,map_zsmul_unit,mixedExteriorMap_basis,
      ← AddMonoidAlgebra.smul_single]
    congr 2
    apply Prod.ext
    · simp [mixedCoefficientIndexAdd,mixedCoefficientBaseIndex]
    · letI : DecidableEq (FiniteVariable.{u} n) :=
        (coloredBaseOrder (r := r) (n := n)).toDecidableEq
      change coloredExponent (0+a.1) (Finsupp.single v 1+a.2.val+faceExponent (F.erase v)) =
        coloredExponent a.1 (a.2.val+faceExponent F)
      rw [zero_add]
      congr 1
      rw [← faceExponent_erase_add hv]
      abel
  · rw [if_neg hv]
    simp only [TensorProduct.tmul_zero,LinearEquiv.map_zero,Subalgebra.coe_zero,
      map_zero,AddMonoidAlgebra.single_zero]

set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency true in
/-- Exact equality with the variable-action tensor Koszul differential. -/
theorem mixedMinimum_intertwines
    (x : MixedTransfer.IdealReesKoszul (coloredIdeals (k := k) n E)) :
    mixedMinimumLinearEquiv (k := k) hE
      ((MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E)).d x)=
      (minimumColorReesDifferential (k := k) hE).d
        (mixedMinimumLinearEquiv (k := k) hE x) := by
  letI := coloredBaseOrder (r := r) (n := n)
  let f := (mixedMinimumLinearEquiv (k := k) hE).toLinearMap
  have hh : f.comp (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E)).d =
      (minimumColorReesDifferential (k := k) hE).d.comp f := by
    apply (mixedTensorBasis (E := E) (k := k)).ext
    rintro ⟨a,F⟩
    simp only [LinearMap.comp_apply,f,LinearEquiv.coe_coe,mixedTensorBasis,
      Module.Basis.tensorProduct_apply]
    apply Subtype.ext
    apply Subtype.ext
    change (mixedMinimumLinearEquiv hE
      ((MixedTransfer.idealReesKoszulDGA (coloredIdeals n E)).d
        (mixedCoefficientBasis a ⊗ₜ[k] mixedExteriorBasis r F))).val.val =
      (exteriorParityDifferential (V := FiniteVariable.{u} (coloredRows (r := r) n)) (k := k)).coefficientDifferential
        (mixedMinimumLinearEquiv hE (mixedCoefficientBasis a ⊗ₜ[k] mixedExteriorBasis r F)).val.val
    rw [mixedMinimumLinearEquiv_basis,ParityDifferential.coefficientDifferential_single]
    rw [show (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E)).d
        (mixedCoefficientBasis a ⊗ₜ[k] mixedExteriorBasis r F)=
        ∑ v : FiniteVariable.{u} n,
          (MixedTransfer.idealReesBaseVariable (coloredIdeals n E) v * mixedCoefficientBasis a) ⊗ₜ[k]
            Simplicial.contraction v (mixedExteriorBasis r F) from
      TensorExteriorKoszul.differential_tmul _ _ _]
    change (((reesKoszulCoordinateAlgebra (k := k) (coloredReesClosure hE)).val.toLinearMap.comp
      (minimumColorReesAlgebra (k := k) hE).val.toLinearMap).comp f)
        (∑ v : FiniteVariable.{u} n, _) = _
    rw [map_sum]
    change (∑ v : FiniteVariable.{u} n, _) = AddMonoidAlgebra.single _
      (Simplicial.boundary (Simplicial.basis (F.map coloredBaseEmbedding)))
    rw [← mixedExteriorMap_basis (r := r) F,
      ← mixedExteriorMap_boundary,Simplicial.boundary_eq_sum,map_sum]
    change (∑ v : FiniteVariable.{u} n, _) = AddMonoidAlgebra.lsingle (R := k) _ (∑ v : FiniteVariable.{u} n, _)
    rw [map_sum]
    exact Finset.sum_congr rfl (fun v _ => mixedMinimum_contraction_basis hE a F v)
  exact LinearMap.congr_fun hh x

/-- The algebra equivalence induced on actual Koszul homology. -/
def mixedMinimumHomologyEquiv :
    (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n E)).Homology ≃ₐ[k]
      (minimumColorReesDifferential (k := k) hE).Homology :=
  ParityDifferential.homologyEquiv _ _ (mixedMinimumAlgEquiv hE) (mixedMinimum_intertwines hE)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.NestedPowerIntersection -/
section

/-!
# Nested mixed products from the symbolic powers of the colored ideal

The argument works directly with arbitrary coefficient ideals. At a prime
containing the colored ideal, the largest color variable outside that prime
supplies the prefix power, while the higher color variables supply the
complementary power. No description of the prime ideals is assumed.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial

variable {C R : Type*} [Fintype C] [LinearOrder C] [CommRing R]

/-- The cumulative exponent appearing in Corollary 5.7. -/
def prefixExponent (m : C →₀ ℕ) (c : C) : ℕ :=
  (m.filter (fun b => b ≤ c)).degree

@[simp] theorem prefixExponent_eq_sum (m : C →₀ ℕ) (c : C) :
    prefixExponent m c = ∑ b ∈ Finset.univ.filter (fun b => b ≤ c), m b := by
  simp only [prefixExponent, Finsupp.degree_eq_sum, Finsupp.filter_apply,
    Finset.sum_filter]

/-- Nestedness gives the easy inclusion for every cumulative power. -/
theorem powerProduct_le_prefix (J : C → Ideal R) (hJ : Monotone J)
    (m : C →₀ ℕ) (c : C) : powerProduct J m ≤ (J c) ^ prefixExponent m c := by
  let a := m.filter (fun b => b ≤ c)
  let b := m.filter (fun b => ¬b ≤ c)
  have hab : a+b=m := Finsupp.filter_add_filter_not m _
  calc
    powerProduct J m = powerProduct J a * powerProduct J b := by
      rw [← hab, powerProduct_add]
    _ ≤ powerProduct J a := Ideal.mul_le_left
    _ ≤ ∏ i, (J c) ^ (a i) := by
      apply Finset.prod_le_prod
      intro i _
      by_cases hi : i ≤ c
      · exact Ideal.pow_right_mono (hJ hi) _
      · simp only [a, Finsupp.filter_apply, if_neg hi, pow_zero, le_refl]
    _ = (J c) ^ prefixExponent m c := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      exact (Finsupp.degree_eq_sum a).symm

/-- A monomial supported on variables in an ideal belongs to the power
specified by its total degree, over any coefficient ring. -/
theorem monomial_one_mem_power_of_variables (P : Ideal (MvPolynomial C R))
    (m : C →₀ ℕ) (hP : ∀ c, m c ≠ 0 → X c ∈ P) :
    monomial m (1 : R) ∈ P ^ m.degree := by
  rw [monic_monomial_eq, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro c hc
  exact Ideal.pow_mem_pow (hP c (Finsupp.mem_support_iff.mp hc)) (m c)

/-- A prime containing the colored ideal contains each coefficient ideal
whose corresponding color variable is outside the prime. -/
theorem coefficientIdeal_map_le_prime (J : C → Ideal R)
    (P : Ideal (MvPolynomial C R)) [P.IsPrime] (hJP : coloredIdeal J ≤ P)
    (c : C) (hc : X c ∉ P) : (J c).map (MvPolynomial.C : R →+* MvPolynomial C R) ≤ P := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  change MvPolynomial.C f ∈ P
  have hprod : X c * MvPolynomial.C f ∈ P := by
    change monomial (Finsupp.single c 1) (1 : R) * monomial 0 f ∈ P
    rw [monomial_mul_monomial, add_zero, one_mul]
    exact hJP (coloredIdeal_generator J c f hf)
  exact (Ideal.IsPrime.mem_or_mem inferInstance hprod).resolve_left hc

/-- The reverse inclusion is forced by the actual localized symbolic
power of the colored ideal. The premise will be supplied by Theorem 4.3. -/
theorem prefix_intersection_le_powerProduct
    (J : C → Ideal R) (m : C →₀ ℕ)
    (hL : radicalSymbolicPower (coloredIdeal J) m.degree = (coloredIdeal J)^m.degree) :
    (⨅ c, (J c)^prefixExponent m c) ≤ powerProduct J m := by
  intro f hf
  apply (coloredIdeal_power_minimal_monomial_iff J m f).mp
  rw [← hL, mem_radicalSymbolicPower_iff]
  intro P hP
  letI : P.IsPrime := hP.isPrime
  refine ⟨1, ?_, ?_⟩
  · intro h
    exact hP.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · rw [one_mul]
    let A := Finset.univ.filter (fun c : C => X c ∉ P)
    by_cases hA : A.Nonempty
    · let c := A.max' hA
      have hc : X c ∉ P := (Finset.mem_filter.mp (Finset.max'_mem A hA)).2
      have hhigher (i : C) (hi : ¬i ≤ c) : X i ∈ P := by
        by_contra hn
        have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hn⟩
        exact hi (Finset.le_max' A i hiA)
      let a := m.filter (fun i => i ≤ c)
      let b := m.filter (fun i => ¬i ≤ c)
      have hab : a+b=m := Finsupp.filter_add_filter_not m _
      have hfc : f ∈ (J c)^a.degree := (Submodule.mem_iInf _).mp hf c
      have hCf : MvPolynomial.C f ∈ P^a.degree := by
        apply Ideal.pow_right_mono (coefficientIdeal_map_le_prime J P hP.le c hc) a.degree
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem (MvPolynomial.C : R →+* MvPolynomial C R) hfc
      have hleft : monomial a f ∈ P^a.degree := by
        rw [monomial_eq]
        exact Ideal.mul_mem_right _ _ hCf
      have hright : monomial b (1 : R) ∈ P^b.degree := by
        apply monomial_one_mem_power_of_variables
        intro i hi
        apply hhigher i
        intro hic
        exact hi (by simp [b, hic])
      have hprod := Ideal.mul_mem_mul hleft hright
      rw [← pow_add, ← Finsupp.degree.map_add, hab] at hprod
      simpa only [monomial_mul_monomial,mul_one,hab] using hprod
    · have hvars (i : C) : X i ∈ P := by
        by_contra hi
        exact hA ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
      have hm := monomial_one_mem_power_of_variables P m (fun i _ => hvars i)
      have hh := Ideal.mul_mem_left (P^m.degree) (MvPolynomial.C f) hm
      simpa only [C_mul_monomial,mul_one] using hh

/-- General nested-product intersection theorem used in Corollary 5.7.
The ideals, products, intersections and localized symbolic power are literal. -/
theorem nested_powerProduct_eq_iInf (J : C → Ideal R) (hJ : Monotone J)
    (m : C →₀ ℕ)
    (hL : radicalSymbolicPower (coloredIdeal J) m.degree = (coloredIdeal J)^m.degree) :
    powerProduct J m = ⨅ c, (J c)^prefixExponent m c := by
  apply le_antisymm
  · exact le_iInf (powerProduct_le_prefix J hJ m)
  · exact prefix_intersection_le_powerProduct J m hL

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.nested_powerProduct_eq_iInf

end
end
end


end

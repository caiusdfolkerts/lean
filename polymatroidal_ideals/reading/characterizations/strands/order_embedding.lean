import Characterizations.Strands.BettiTransport

/-! # Signed simplicial chain transport along an order embedding -/
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.Strands
open Classical Finset CommAlg.Simplicial CommAlg.Koszul CategoryTheory
universe u
variable {W V k : Type u} [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Field k]

def ambientMap (f : W ↪o V) : Ambient W k →ₗ[k] Ambient V k :=
  basis.constr k (fun s => basis (s.map f.toEmbedding))

@[simp] lemma ambientMap_basis (f : W ↪o V) (s : Finset W) :
    ambientMap (k := k) f (basis s) = basis (s.map f.toEmbedding) :=
  Module.Basis.constr_basis _ _ _ _

lemma eraseSign_map (f : W ↪o V) (s : Finset W) (e : W) :
    TauCeti.ExteriorAlgebra.basisEraseSign (f e) (s.map f.toEmbedding) =
      TauCeti.ExteriorAlgebra.basisEraseSign e s := by
  rw [TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt,
    Finset.filter_map]
  simp only [Finset.card_map]
  change (-1 : ℤˣ) ^ (s.filter (fun j => f j < f e)).card = _
  simp only [f.lt_iff_lt]

lemma boundary_basis_finset (s : Finset V) :
    boundary (basis (k := k) s) =
      ∑ e ∈ s, TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (s.erase e) := by
  rw [boundary_eq_sum]
  trans ∑ e ∈ s, contraction (k := k) e (basis s)
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e he hnot
    simp [contraction_basis, hnot]
  · apply Finset.sum_congr rfl
    intro e he
    simp only [contraction_basis, if_pos he]

lemma ambientMap_boundary (f : W ↪o V) :
    ambientMap (k := k) f ∘ₗ boundary = boundary ∘ₗ ambientMap f := by
  apply basis.ext
  intro s
  simp only [LinearMap.comp_apply, boundary_basis_finset, map_sum, map_zsmul_unit,
    ambientMap_basis, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  change TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (map f.toEmbedding (s.erase e)) =
    TauCeti.ExteriorAlgebra.basisEraseSign (f e) (map f.toEmbedding s) •
      basis ((map f.toEmbedding s).erase (f e))
  rw [eraseSign_map]
  exact congrArg (fun t : Finset V =>
    TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (k := k) t)
    (Finset.map_erase f.toEmbedding s e)

abbrev ChainIndex (K : Finset W → Prop) (i : ℕ) := {s : Finset W // K s ∧ s.card=i}

def chainBasis (K : Finset W → Prop) (i : ℕ) :
    Module.Basis (ChainIndex K i) k (Chains (k := k) K i) :=
  CommAlg.Grading.restrictedBasis basis (fun s => K s ∧ s.card=i)

@[simp] lemma chainBasis_val (K : Finset W → Prop) (i : ℕ) (s : ChainIndex K i) :
    (chainBasis (k := k) K i s).val = basis s.val :=
  CommAlg.Grading.restrictedBasis_val _ _ _

def faceIndexMap (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    ChainIndex K i → ChainIndex L i := fun s =>
  ⟨s.val.map f.toEmbedding, (h _).mpr ⟨s.val, s.property.1, rfl⟩,
    (Finset.card_map _).trans s.property.2⟩

def faceIndexEquiv (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    ChainIndex K i ≃ ChainIndex L i := Equiv.ofBijective (faceIndexMap f K L h i) (by
  constructor
  · intro s t he
    apply Subtype.ext
    exact Finset.map_injective f.toEmbedding (congrArg Subtype.val he)
  · intro s
    obtain ⟨t, ht, he⟩ := (h s.val).mp s.property.1
    refine ⟨⟨t, ht, ?_⟩, Subtype.ext he.symm⟩
    simpa only [he, Finset.card_map] using s.property.2)

def chainEquiv (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    Chains (k := k) K i ≃ₗ[k] Chains (k := k) L i :=
  (chainBasis K i).equiv (chainBasis L i) (faceIndexEquiv f K L h i)

lemma chainEquiv_val (f : W ↪o V) (K : Finset W → Prop) (L : Finset V → Prop)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ)
    (z : Chains (k := k) K i) : (chainEquiv f K L h i z).val = ambientMap f z.val := by
  have he : (Chains (k := k) L i).subtype ∘ₗ (chainEquiv f K L h i).toLinearMap =
      ambientMap f ∘ₗ (Chains (k := k) K i).subtype := by
    apply (chainBasis (k := k) K i).ext
    intro s
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, chainEquiv,
      Module.Basis.equiv_apply]
    change ((chainBasis (k := k) L i) (faceIndexEquiv f K L h i s)).val =
      ambientMap f ((chainBasis (k := k) K i) s).val
    rw [chainBasis_val, chainBasis_val, ambientMap_basis]
    rfl
  exact LinearMap.congr_fun he z

def embeddedChainIso (f : W ↪o V) {K : Finset W → Prop} {L : Finset V → Prop}
    (hK : Downward K) (hL : Downward L)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) :
    chainComplex (k := k) hK ≅ chainComplex hL :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (chainEquiv f K L h i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j+1 := hij.symm
      rw [chainComplex_d, chainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change Chains (k := k) K (j+1) at z
      apply Subtype.ext
      change (chainDifferential hL j (chainEquiv f K L h (j+1) z)).val =
        (chainEquiv f K L h j (chainDifferential hK j z)).val
      simp only [chainEquiv_val, chainDifferential_val]
      exact (LinearMap.congr_fun (ambientMap_boundary f) z.val).symm)

lemma embedded_homology_finrank (f : W ↪o V) {K : Finset W → Prop} {L : Finset V → Prop}
    (hK : Downward K) (hL : Downward L)
    (h : ∀ s, L s ↔ ∃ t, K t ∧ s=t.map f.toEmbedding) (i : ℕ) :
    Module.finrank k ((chainComplex (k := k) hK).homology i) =
      Module.finrank k ((chainComplex (k := k) hL).homology i) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (embeddedChainIso f hK hL h)).toLinearEquiv.finrank_eq

end Characterizations.Strands

module
public import graph_foundation.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: CommAlg.Simplicial.Filling -/
section

/-! # Chain-level deletion/contraction and nonzero homology

Every predicate below refers to actual exterior chains, their actual boundary, and the actual
existence of a filling chain. These lemmas supply the full homological induction for matroids.
-/

noncomputable section

namespace CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

/-- Every closed augmented chain in this degree is the boundary of a chain in the next degree. -/
def ExactIn (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∀ z : Ambient V k, z ∈ Chains K i → boundary z = 0 →
    ∃ y : Ambient V k, y ∈ Chains K (i + 1) ∧ boundary y = z

/-- An actual closed chain whose homology class does not vanish. -/
def NonzeroHomology (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∃ z : Ambient V k, z ∈ Chains K i ∧ boundary z = 0 ∧
    ∀ y : Ambient V k, y ∈ Chains K (i + 1) → boundary y ≠ z

lemma nonzeroHomology_iff_not_exactIn (K : Finset V → Prop) (i : ℕ) :
    NonzeroHomology (k := k) K i ↔ ¬ExactIn (k := k) K i := by
  classical
  simp only [NonzeroHomology, ExactIn, not_forall, not_exists, not_and]
  tauto

lemma chains_eq_bot_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : Chains (k := k) K i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Chains, Submodule.span_le]
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact (h s hs hc).elim

lemma exactIn_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : ExactIn (k := k) K i := by
  intro z hz hcycle
  rw [chains_eq_bot_of_no_face h, Submodule.mem_bot] at hz
  subst z
  exact ⟨0, Submodule.zero_mem _, map_zero _⟩

lemma creation_mem_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K i) : creation e z ∈ Chains K (i + 1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [creation_basis]
    split_ifs with he
    · exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      exact basis_mem (hc s hs) (by simp [he, hcard])
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i + 1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma exactIn_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) (i : ℕ) : ExactIn (k := k) K i := by
  intro z hz hcycle
  refine ⟨creation e z, creation_mem_of_cone e hc hz, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma exactIn_zero_of_vertex {K : Finset V → Prop} (e : V) (he : K {e}) :
    ExactIn (k := k) K 0 := by
  intro z hz hcycle
  have hc : creation e z ∈ Chains K 1 := by
    clear hcycle
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
      obtain rfl : s = ∅ := Finset.card_eq_zero.mp hcard
      rw [creation_basis]
      simp only [Finset.notMem_empty, ↓reduceIte, Finset.insert_empty]
      exact Submodule.smul_mem _ _ (basis_mem he (Finset.card_singleton _))
    | zero => simpa using (Submodule.zero_mem (Chains (k := k) K 1))
    | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
    | smul r a ha ih => simpa using Submodule.smul_mem _ r ih
  refine ⟨creation e z, hc, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma nonzeroHomology_zero_of_only_empty [Nontrivial k] {K : Finset V → Prop}
    (he : K ∅) (hK : ∀ s, K s → s = ∅) : NonzeroHomology (k := k) K 0 := by
  refine ⟨basis ∅, basis_mem he rfl, ?_, ?_⟩
  · exact boundary_zero_degree_zero (basis_mem he rfl)
  · intro y hy hyb
    have hn : ∀ s, K s → s.card ≠ 1 := by
      intro s hs
      rw [hK s hs]
      simp
    rw [chains_eq_bot_of_no_face hn, Submodule.mem_bot] at hy
    subst y
    have hb : basis (k := k) (∅ : Finset V) ≠ 0 := Module.Basis.ne_zero _ _
    exact hb (by simpa using hyb.symm)

/-- The exactness half of deletion/contraction, proved by filling explicit chains. -/
lemma exactIn_of_deletion_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) (i + 1))
    (hlink : ExactIn (k := k) (link K e) i) : ExactIn (k := k) K (i + 1) := by
  intro z hz hcycle
  have hw := contraction_mem e hz
  have hwcycle : boundary (contraction e z) = 0 := by
    have h := contraction_boundary e z
    rw [hcycle, map_zero, eq_neg_iff_add_eq_zero, zero_add] at h
    exact h
  obtain ⟨v, hv, hvb⟩ := hlink _ hw hwcycle
  let z' := z + boundary (creation e v)
  have hz' : z' ∈ Chains K (i + 1) :=
    Submodule.add_mem _ hz (boundary_mem hK (creation_mem_link e hv))
  have hvcon : contraction e v = 0 :=
    contraction_zero_of_deletion e (link_le_deletion hK e _ hv)
  have hz'con : contraction e z' = 0 := by
    dsimp only [z']
    rw [map_add, contraction_boundary, contraction_creation, hvcon, map_zero, sub_zero, hvb]
    exact add_neg_cancel _
  have hz'del := mem_deletion_of_contraction_zero e hz' hz'con
  have hz'cycle : boundary z' = 0 := by
    simp only [z', map_add, hcycle, boundary_boundary, add_zero]
  obtain ⟨y, hy, hyb⟩ := hdel z' hz'del hz'cycle
  refine ⟨y - creation e v,
    Submodule.sub_mem _ (chains_mono (fun s hs => hs.1) _ hy) (creation_mem_link e hv), ?_⟩
  rw [map_sub, hyb]
  exact add_sub_cancel_right z _

/-- Nonzero link homology produces nonzero homology one degree higher, whenever every chain in
that degree of the deletion can be filled. The proof constructs the cycle explicitly. -/
lemma nonzeroHomology_of_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) i)
    (hlink : NonzeroHomology (k := k) (link K e) i) :
    NonzeroHomology (k := k) K (i + 1) := by
  obtain ⟨w, hw, hwcycle, hwnonboundary⟩ := hlink
  obtain ⟨y, hy, hyb⟩ := hdel w (link_le_deletion hK e i hw) hwcycle
  refine ⟨creation e w - y,
    Submodule.sub_mem _ (creation_mem_link e hw) (chains_mono (fun s hs => hs.1) _ hy), ?_, ?_⟩
  · rw [map_sub, boundary_creation, hwcycle, map_zero, sub_zero, hyb, sub_self]
  · intro q hq hqb
    have hwcon := contraction_zero_of_deletion e (link_le_deletion hK e i hw)
    have hycon := contraction_zero_of_deletion e hy
    have h := congrArg (contraction e) hqb
    rw [contraction_boundary, map_sub, contraction_creation, hwcon, map_zero, sub_zero,
      hycon, sub_zero] at h
    exact hwnonboundary (-contraction e q)
      (Submodule.neg_mem _ (contraction_mem e hq)) (by simpa only [map_neg] using h)

end CommAlg.Simplicial

end
end

/- BEGIN EXACT BODY: CommAlg.Simplicial.Homology -/
section

/-! # Actual categorical homology of the augmented exterior chains -/

noncomputable section

namespace CommAlg.Simplicial

open CategoryTheory CategoryTheory.Limits

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The usual signed boundary, restricted to the actual face-chain submodules. -/
def chainDifferential {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    Chains (k := k) K (i + 1) →ₗ[k] Chains (k := k) K i :=
  (boundary.domRestrict (Chains K (i + 1))).codRestrict _
    (fun z => boundary_mem hK z.property)

@[simp] lemma chainDifferential_val {K : Finset V → Prop} (hK : Downward K) (i : ℕ)
    (z : Chains (k := k) K (i + 1)) :
    (chainDifferential hK i z).val = boundary z.val := rfl

lemma chainDifferential_comp {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    chainDifferential (k := k) hK i ∘ₗ chainDifferential hK (i + 1) = 0 := by
  ext z
  exact boundary_boundary z.val

/-- This is the genuine augmented simplicial chain complex, with the empty face in degree zero. -/
def chainComplex {K : Finset V → Prop} (hK : Downward K) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (Chains (k := k) K i))
    (fun i => ModuleCat.ofHom (chainDifferential hK i))
    (fun i => ModuleCat.hom_ext (chainDifferential_comp hK i))

@[simp] lemma chainComplex_d {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).d (i + 1) i = ModuleCat.ofHom (chainDifferential hK i) := by
  simp [chainComplex]

lemma chainComplex_exactAt_succ_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt (i + 1) ↔ ExactIn (k := k) K (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [chainComplex_d]
  change (∀ z : Chains (k := k) K (i + 1), chainDifferential hK i z = 0 →
    ∃ y : Chains (k := k) K (i + 2), chainDifferential hK (i + 1) y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ (Subtype.ext hc)
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (congrArg Subtype.val hz)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_zero_iff {K : Finset V → Prop} (hK : Downward K) :
    (chainComplex (k := k) hK).ExactAt 0 ↔ ExactIn (k := k) K 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  rw [chainComplex_d, (chainComplex (k := k) hK).shape 0 0 (by simp)]
  change (∀ z : Chains (k := k) K 0, (0 : Chains (k := k) K 0) = 0 →
    ∃ y : Chains (k := k) K 1, chainDifferential hK 0 y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ rfl
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (boundary_zero_degree_zero z.property)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt i ↔ ExactIn (k := k) K i := by
  cases i with
  | zero => exact chainComplex_exactAt_zero_iff hK
  | succ i => exact chainComplex_exactAt_succ_iff hK i

/-- The explicit cycle/nonboundary condition is equivalent to nonvanishing of actual homology. -/
lemma homology_nonzero_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    ¬ IsZero ((chainComplex (k := k) hK).homology i) ↔ NonzeroHomology (k := k) K i := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, chainComplex_exactAt_iff,
    nonzeroHomology_iff_not_exactIn]

end CommAlg.Simplicial

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.Faces -/
section

/-! # The actual upper Koszul faces and their homogeneous chain indices -/

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev FaceIndex (B : Family V) (a : Exponent V) (i : ℕ) :=
  {s : Finset V // koszulFaces B a s ∧ s.card = i}

def faceChainBasis (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.Basis (FaceIndex B a i) k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
  Grading.restrictedBasis Simplicial.basis (fun s => koszulFaces B a s ∧ s.card = i)

@[simp] lemma faceChainBasis_val (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) : (faceChainBasis (k := k) B a i s).val = Simplicial.basis s.val :=
  Grading.restrictedBasis_val _ _ _

/-- Exact matching of simplicial face bases with actual monomial-exterior bases of degree `a`. -/
def faceMonomialEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    FaceIndex B a i ≃ {t : MonomialIndex B i // monomialDegree t = a} where
  toFun s := ⟨⟨⟨s.val, s.property.2⟩,
    ⟨a - faceExponent s.val, s.property.1.2⟩⟩,
    tsub_add_cancel_of_le s.property.1.1⟩
  invFun t := ⟨t.val.1.val, ⟨⟨by
    exact (le_add_of_nonneg_left (show (0 : Exponent V) ≤ t.val.2.val from zero_le)).trans_eq t.property, by
    have he : a - faceExponent t.val.1.val = t.val.2.val := by
      exact (congrArg (fun b : Exponent V => b - faceExponent t.val.1.val)
        t.property.symm).trans (add_tsub_cancel_right _ _)
    rw [he]
    exact t.val.2.property⟩, t.val.1.property⟩⟩
  left_inv s := rfl
  right_inv t := by
    rcases t with ⟨⟨s, b⟩, ht⟩
    apply Subtype.ext
    dsimp only
    have hb : a - faceExponent s.val = b.val :=
      (congrArg (fun c : Exponent V => c - faceExponent s.val)
        ht.symm).trans (add_tsub_cancel_right _ _)
    exact congrArg (fun c : {c : Exponent V // Contains B c} => (⟨s, c⟩ : MonomialIndex B i))
      (Subtype.ext hb)

/-- The isomorphism acts on real chains in the actual Koszul homogeneous component. -/
def faceHomogeneousEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    Simplicial.Chains (k := k) (koszulFaces B a) i ≃ₗ[k] homogeneousPiece (k := k) B a i :=
  (faceChainBasis (k := k) B a i).equiv
    (Grading.restrictedBasis (monomialCoefficientBasis (k := k) B i)
      (fun t => monomialDegree t = a)) (faceMonomialEquiv B a i)

@[simp] lemma faceHomogeneousEquiv_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) :
    (faceHomogeneousEquiv (k := k) B a i (faceChainBasis (k := k) B a i s)).val =
      monomialCoefficientBasis (k := k) B i (faceMonomialEquiv B a i s).val := by
  unfold faceHomogeneousEquiv
  rw [Module.Basis.equiv_apply]
  exact Grading.restrictedBasis_val _ _ _

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.CoefficientTor -/
section

/-!
# Genuine Tor over the coefficient ring

The coordinate Koszul complex is transported along exact restriction of
scalars. Its differential remains the actual tensor Koszul differential.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev underlyingDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

theorem underlyingDifferential_comp (B : Family V) (i : ℕ) :
    underlyingDifferential (k := k) B i ∘ₗ underlyingDifferential B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun
    (coordinateDifferential_comp (X : V → MvPolynomial V k)
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i) z

/-- The genuine coordinate Koszul complex, regarded as a complex over the
coefficient ring by its canonical scalar structure. -/
def underlyingComplex (B : Family V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of
    (fun i => ModuleCat.of k (Set.powersetCard V i →₀ (monomialIdeal k B)))
    (fun i => ModuleCat.ofHom (underlyingDifferential B i))
    (fun i => ModuleCat.hom_ext (underlyingDifferential_comp B i))

@[simp] theorem underlyingComplex_d (B : Family V) (i : ℕ) :
    (underlyingComplex (k := k) B).d (i + 1) i =
      ModuleCat.ofHom
        ((coordinateDifferential (X : V → MvPolynomial V k)
          (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k) := by
  simp [underlyingComplex]

/-- The restriction-of-scalars module structure agrees with the canonical
coefficient-ring module structure. The equivalence is the identity on values. -/
def coefficientRestrictionEquiv (B : Family V) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (ModuleCat.of (MvPolynomial V k)
        (Set.powersetCard V i →₀ (monomialIdeal k B)))) ≃ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r z => by
    change (algebraMap k (MvPolynomial V k) r) •
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z) =
        r • (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)
    exact algebraMap_smul (MvPolynomial V k) r
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)

/-- Exact scalar restriction of the polynomial coordinate complex is
isomorphic to the same complex in canonical coefficient-ring modules. -/
def restrictionCoordinateComplexIso (B : Family V) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (coordinateComplex (X : V → MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      underlyingComplex (k := k) B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (coefficientRestrictionEquiv B i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      simp only [Functor.mapHomologicalComplex_obj_d, coordinateComplex_d,
        underlyingComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

/-- Actual derived Tor, restricted to the coefficient ring, is the homology
of the original standard coordinate Koszul complex. -/
def coefficientTorIso [Nontrivial k] (B : Family V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      (underlyingComplex (k := k) B).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))
  let M := ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)
  let C := coordinateComplex (X : V → MvPolynomial V k) M
  F.mapIso (finitePolynomialTorIso i M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k))
      (ComplexShape.down ℕ) i).mapIso (coordinateComplexIso (X : V → MvPolynomial V k) M)) ≪≫
    ((C.sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
      (restrictionCoordinateComplexIso B)

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.MonomialDifferential -/
section

/-! # The actual Koszul differential preserves the standard multigrading -/

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical MvPolynomial CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev monomialDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

/-- A term obtained by removing one exterior variable and multiplying the coefficient by it. -/
def differentialIndex {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) : MonomialIndex B i :=
  ⟨eraseIndex t.1 j, ⟨t.2.val + Finsupp.single j.val 1, by
    obtain ⟨b, hb, hba⟩ := t.2.property
    exact ⟨b, hb, hba.trans (le_add_of_nonneg_right (zero_le))⟩⟩⟩

lemma differentialIndex_degree {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) :
    monomialDegree (differentialIndex t j) = monomialDegree t := by
  change (t.2.val + Finsupp.single j.val 1) + faceExponent (t.1.val.erase j.val) = _
  rw [add_assoc, add_comm (Finsupp.single j.val 1), faceExponent_erase_add j.property]
  rfl

lemma monomialBasis_mul_variable (B : Family V) (a : {a : Exponent V // Contains B a})
    (j : V) (ha : Contains B (a.val + Finsupp.single j 1)) :
    (X j : MvPolynomial V k) • monomialBasis (k := k) B a =
      monomialBasis (k := k) B ⟨a.val + Finsupp.single j 1, ha⟩ := by
  apply Subtype.ext
  change X j * (monomialBasis (k := k) B a).val = _
  rw [monomialBasis_val, monomialBasis_val, X, monomial_mul_monomial]
  simp [add_comm]

lemma monomialDifferential_basis (B : Family V) (i : ℕ) (t : MonomialIndex B (i + 1)) :
    monomialDifferential (k := k) B i (monomialCoefficientBasis (k := k) B (i + 1) t) =
      ∑ j : {j // j ∈ t.1.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val •
        monomialCoefficientBasis (k := k) B i (differentialIndex t j) := by
  rcases t with ⟨s, a⟩
  rw [monomialCoefficientBasis_apply]
  change coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i
    (Finsupp.single s (monomialBasis (k := k) B a)) = _
  rw [coordinateDifferential_single]
  apply Finset.sum_congr rfl
  intro j hj
  change Finsupp.single (eraseIndex s j)
    (X j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • monomialBasis (k := k) B a)) = _
  rw [smul_comm (X j.val)]
  rw [monomialBasis_mul_variable (k := k) B a j.val (differentialIndex (B := B) ⟨s, a⟩ j).2.property]
  simp [differentialIndex, monomialCoefficientBasis_apply, Finsupp.smul_single]

lemma monomialDifferential_comp (B : Family V) (i : ℕ) :
    monomialDifferential (k := k) B i ∘ₗ monomialDifferential (k := k) B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun (underlyingDifferential_comp (k := k) B i) z

lemma monomialDifferential_homogeneous (B : Family V) (a : Exponent V) (i : ℕ)
    {z : Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)}
    (hz : z ∈ homogeneousPiece (k := k) B a (i + 1)) :
    monomialDifferential (k := k) B i z ∈ homogeneousPiece (k := k) B a i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, rfl⟩ := hz
    rw [monomialDifferential_basis]
    apply Submodule.sum_mem
    intro j hj
    apply (Submodule.smul_mem_iff' _ (TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val)).2
    exact Submodule.subset_span
      ⟨differentialIndex t j, (differentialIndex_degree t j).trans ht, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem (homogeneousPiece (k := k) B a i))
  | add z w hz hw ihz ihw => simpa using Submodule.add_mem _ ihz ihw
  | smul c z hz ih => simpa using Submodule.smul_mem _ c ih

lemma homogeneousProjection_differential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousProjection (k := k) B a i ∘ₗ monomialDifferential (k := k) B i =
      monomialDifferential (k := k) B i ∘ₗ homogeneousProjection (k := k) B a (i + 1) := by
  apply (monomialCoefficientBasis (k := k) B (i + 1)).ext
  intro t
  change homogeneousProjection (k := k) B a i
    (monomialDifferential B i (monomialCoefficientBasis B (i + 1) t)) =
    monomialDifferential B i (homogeneousProjection B a (i + 1)
      (monomialCoefficientBasis B (i + 1) t))
  have hm : monomialDifferential (k := k) B i (monomialCoefficientBasis B (i + 1) t) ∈
      homogeneousPiece B (monomialDegree t) i :=
    monomialDifferential_homogeneous B _ i (Grading.basis_mem_piece _ _ t)
  change Grading.projection _ _ a _ = monomialDifferential (k := k) B i
    (Grading.projection _ _ a ((monomialCoefficientBasis B (i + 1)) t))
  rw [Grading.projection_basis]
  by_cases ht : monomialDegree t = a
  · rw [if_pos ht]
    exact Grading.projection_eq_self (ht ▸ hm)
  · rw [if_neg ht, map_zero]
    exact Grading.projection_eq_zero (Ne.symm ht) hm

/-- Restricting the actual Koszul differential to its genuine degree component. -/
def homogeneousDifferential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousPiece (k := k) B a (i + 1) →ₗ[k] homogeneousPiece (k := k) B a i :=
  ((monomialDifferential (k := k) B i).domRestrict (homogeneousPiece (k := k) B a (i + 1))).codRestrict _
    (fun z => monomialDifferential_homogeneous B a i z.property)

lemma homogeneousDifferential_comp (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousDifferential (k := k) B a i ∘ₗ homogeneousDifferential (k := k) B a (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (monomialDifferential_comp B i) z.val

/-- The actual multidegree subcomplex of the tensor Koszul resolution. -/
def homogeneousComplex (B : Family V) (a : Exponent V) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (homogeneousPiece (k := k) B a i))
    (fun i => ModuleCat.ofHom (homogeneousDifferential (k := k) B a i))
    (fun i => ModuleCat.hom_ext (homogeneousDifferential_comp B a i))

@[simp] lemma homogeneousComplex_d (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).d (i + 1) i =
      ModuleCat.ofHom (homogeneousDifferential (k := k) B a i) := by
  simp [homogeneousComplex]

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.HomogeneousFaces -/
section

/-! # Homogeneous Koszul components are genuinely isomorphic to upper-face chains -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma boundary_basis_sum (s : Finset V) :
    Simplicial.boundary (Simplicial.basis (k := k) s) =
      ∑ j : {j // j ∈ s}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s •
        Simplicial.basis (s.erase j.val) := by
  rw [Simplicial.boundary_eq_sum]
  calc
    ∑ j : V, Simplicial.contraction j (Simplicial.basis s) =
        ∑ j ∈ s, Simplicial.contraction j (Simplicial.basis s) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      simp only [Simplicial.contraction_basis, if_neg hnot]
    _ = ∑ j : {j // j ∈ s}, Simplicial.contraction j.val (Simplicial.basis s) :=
      Finset.sum_subtype s (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Simplicial.contraction_basis, if_pos j.property]

def eraseFace {B : Family V} {a : Exponent V} {i : ℕ}
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) : FaceIndex B a i :=
  ⟨s.val.erase j.val,
    (koszulFaces_downward B a) (Finset.erase_subset _ _) s.property.1,
    by simp [Finset.card_erase_of_mem j.property, s.property.2]⟩

lemma faceChainDifferential_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) :
    Simplicial.chainDifferential (k := k) (koszulFaces_downward B a) i
      (faceChainBasis (k := k) B a (i + 1) s) =
      ∑ j : {j // j ∈ s.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
        faceChainBasis (k := k) B a i (eraseFace s j) := by
  apply Subtype.ext
  simp only [Simplicial.chainDifferential_val, faceChainBasis_val,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, eraseFace]
  exact boundary_basis_sum s.val

lemma faceMonomialEquiv_erase (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) :
    (faceMonomialEquiv B a i (eraseFace s j)).val =
      differentialIndex (faceMonomialEquiv B a (i + 1) s).val j := by
  have hExp : a - faceExponent (s.val.erase j.val) =
      a - faceExponent s.val + Finsupp.single j.val 1 := by
    have he := faceExponent_erase_add j.property
    have hle := s.property.1.1
    ext v
    have hv := hle v
    have hev := congrArg (fun b : Exponent V => b v) he
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at *
    omega
  exact congrArg (fun b : {b : Exponent V // Contains B b} =>
    (⟨eraseIndex ⟨s.val, s.property.2⟩ j, b⟩ : MonomialIndex B i)) (Subtype.ext hExp)

lemma faceHomogeneousEquiv_comm (B : Family V) (a : Exponent V) (i : ℕ) :
    (faceHomogeneousEquiv (k := k) B a i).toLinearMap ∘ₗ
        Simplicial.chainDifferential (koszulFaces_downward B a) i =
      homogeneousDifferential (k := k) B a i ∘ₗ
        (faceHomogeneousEquiv (k := k) B a (i + 1)).toLinearMap := by
  apply (faceChainBasis (k := k) B a (i + 1)).ext
  intro s
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, faceChainDifferential_basis,
    map_sum, map_zsmul_unit]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, faceHomogeneousEquiv_basis]
  change _ = monomialDifferential (k := k) B i
    ((faceHomogeneousEquiv (k := k) B a (i + 1))
      ((faceChainBasis (k := k) B a (i + 1)) s)).val
  rw [faceHomogeneousEquiv_basis, monomialDifferential_basis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [faceMonomialEquiv_erase]
  rfl

/-- Kernel-checked chain isomorphism, including every homological and multigraded degree. -/
def homogeneousFacesIso (B : Family V) (a : Exponent V) :
    Simplicial.chainComplex (k := k) (koszulFaces_downward B a) ≅
      homogeneousComplex (k := k) B a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (faceHomogeneousEquiv (k := k) B a i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [Simplicial.chainComplex_d, homogeneousComplex_d]
      apply ModuleCat.hom_ext
      exact (faceHomogeneousEquiv_comm B a j).symm)

/-- Nonvanishing of an actual homogeneous Koszul homology group is exactly the face-chain condition. -/
lemma homogeneous_homology_nonzero_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    ¬ CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  have e := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (homogeneousFacesIso (k := k) B a)
  have he : CategoryTheory.Limits.IsZero
      ((Simplicial.chainComplex (k := k) (koszulFaces_downward B a)).homology i) ↔
      CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) :=
    e.isZero_iff
  exact (not_congr he.symm).trans (Simplicial.homology_nonzero_iff _ i)

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TotalFaces -/
section

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def idealTotalData {P : Finset V → Prop} (hP : Simplicial.Downward P) :
    FourPapers.SubmoduleComplexData k (TotalFaceModule (k := k) P) where
  piece := totalFacePiece P
  d := idealTotalDifferential hP
  square_zero := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Simplicial.boundary_boundary x.val
  lowers i x hx := Simplicial.boundary_mem hP hx

/-- The total-module interpretation has exactly the original augmented face
complex, including its degree-zero object and differential. -/
def idealTotalComplexIso {P : Finset V → Prop} (hP : Simplicial.Downward P) :
    (idealTotalData (k := k) hP).complex ≅ Simplicial.chainComplex (k := k) hP :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (totalFacePieceEquiv (k := k) P i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [FourPapers.SubmoduleComplexData.complex_d,Simplicial.chainComplex_d]
      apply ModuleCat.hom_ext
      ext x
      rfl)

/-- The ideal total face model is an actual Koszul homogeneous complex. -/
def idealTotalKoszulIso (B : Family V) (α : Exponent V) :
    (idealTotalData (k := k) (koszulFaces_downward B α)).complex ≅
      homogeneousComplex (k := k) B α :=
  idealTotalComplexIso (koszulFaces_downward B α) ≪≫ homogeneousFacesIso B α

def quotientTotalData (B : Family V) (α : Exponent V) :
    FourPapers.SubmoduleComplexData k (TotalFaceModule (k := k) (quotientKoszulFaces B α)) where
  piece := totalFacePiece (quotientKoszulFaces B α)
  d := quotientTotalDifferential B α
  square_zero := quotientTotalDifferential_comp B α
  lowers i x hx := by
    have hy := (quotientFaceDifferential (k := k) B α i ⟨x.val,hx⟩).property
    change quotientFaceProjection B α (Simplicial.boundary x.val) ∈
      Simplicial.Chains (quotientKoszulFaces B α) i
    simpa only [quotientFaceDifferential_val] using hy

def quotientTotalComplexIso (B : Family V) (α : Exponent V) :
    (quotientTotalData (k := k) B α).complex ≅ quotientFaceComplex (k := k) B α :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (totalFacePieceEquiv (k := k) (quotientKoszulFaces B α) i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [FourPapers.SubmoduleComplexData.complex_d,quotientFaceComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (quotientFaceDifferential (k := k) B α j ⟨x.val.val,x.property⟩).val =
        quotientFaceProjection B α (Simplicial.boundary x.val.val)
      exact quotientFaceDifferential_val (k := k) B α j _)

/-- The total quotient face model is connected to the genuine polynomial-quotient
Koszul complex, rather than declared to be its homology. -/
def quotientTotalKoszulIso (B : Family V) (α : Exponent V) :
    (quotientTotalData (k := k) B α).complex ≅ quotientHomogeneousComplex (k := k) B α :=
  quotientTotalComplexIso B α ≪≫ quotientFacesIso B α


end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTor -/
section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

/-!
# The coefficient quotient's genuine derived Tor grading

The fine pieces below are images in Mathlib's derived tensor functor.  Their
inclusions split by homogeneous chain projections.  Thus `quotientBettiNumber`
measures the usual multigraded Tor of the actual polynomial quotient.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CategoryTheory.Limits MvPolynomial
open CommAlg.Polymatroid CommAlg.Koszul

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def quotientUnderlyingComplex (B : Family V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of
    (fun i => ModuleCat.of k (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B))
    (fun i => ModuleCat.ofHom (quotientDifferential B i))
    (fun i => ModuleCat.hom_ext (quotientDifferential_comp B i))

@[simp] lemma quotientUnderlyingComplex_d (B : Family V) (i : ℕ) :
    (quotientUnderlyingComplex (k := k) B).d (i + 1) i =
      ModuleCat.ofHom (quotientDifferential (k := k) B i) := by
  simp [quotientUnderlyingComplex]

def quotientRestrictionEquiv (B : Family V) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (ModuleCat.of (MvPolynomial V k)
        (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B))) ≃ₗ[k]
      (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r z := by
    change (algebraMap k (MvPolynomial V k) r) •
      (show Set.powersetCard V i →₀ CoefficientQuotient (k := k) B from z) =
        r • (show Set.powersetCard V i →₀ CoefficientQuotient (k := k) B from z)
    exact algebraMap_smul (MvPolynomial V k) r
      (show Set.powersetCard V i →₀ CoefficientQuotient (k := k) B from z)

def quotientRestrictionComplexIso (B : Family V) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (coordinateComplex (X : V → MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) ≅
      quotientUnderlyingComplex (k := k) B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (quotientRestrictionEquiv B i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      simp only [Functor.mapHomologicalComplex_obj_d, coordinateComplex_d,
        quotientUnderlyingComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

/-- The homology is the derived tensor functor applied to the actual quotient. -/
def quotientTorIso [Nontrivial k] (B : Family V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) ≅
      (quotientUnderlyingComplex (k := k) B).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))
  let M := ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)
  let C := coordinateComplex (X : V → MvPolynomial V k) M
  F.mapIso (finitePolynomialTorIso i M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k))
      (ComplexShape.down ℕ) i).mapIso (coordinateComplexIso (X : V → MvPolynomial V k) M)) ≪≫
    ((C.sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
      (quotientRestrictionComplexIso B)

def quotientProjection (B : Family V) (a : Exponent V) (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) →ₗ[k]
      (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) :=
  CommAlg.Grading.projection (quotientCoefficientBasis (k := k) B i) quotientDegree a

lemma quotientProjection_mem (B : Family V) (a : Exponent V) (i : ℕ)
    (z : Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) :
    quotientProjection (k := k) B a i z ∈ quotientPiece (k := k) B a i :=
  CommAlg.Grading.projection_mem _ _ _ _

lemma quotientProjection_differential (B : Family V) (a : Exponent V) (i : ℕ) :
    quotientProjection (k := k) B a i ∘ₗ quotientDifferential B i =
      quotientDifferential B i ∘ₗ quotientProjection B a (i + 1) := by
  apply (quotientCoefficientBasis (k := k) B (i + 1)).ext
  intro t
  change quotientProjection (k := k) B a i
    (quotientDifferential B i (quotientCoefficientBasis B (i + 1) t)) =
    quotientDifferential B i (quotientProjection B a (i + 1)
      (quotientCoefficientBasis B (i + 1) t))
  have hm : quotientDifferential (k := k) B i (quotientCoefficientBasis B (i + 1) t) ∈
      quotientPiece B (quotientDegree t) i :=
    quotientDifferential_homogeneous B _ i (CommAlg.Grading.basis_mem_piece _ _ t)
  change CommAlg.Grading.projection _ _ a _ = quotientDifferential (k := k) B i
    (CommAlg.Grading.projection _ _ a (quotientCoefficientBasis B (i + 1) t))
  rw [CommAlg.Grading.projection_basis]
  by_cases ht : quotientDegree t = a
  · rw [if_pos ht]
    exact CommAlg.Grading.projection_eq_self (ht ▸ hm)
  · rw [if_neg ht, map_zero]
    exact CommAlg.Grading.projection_eq_zero (Ne.symm ht) hm

def quotientHomogeneousInclusion (B : Family V) (a : Exponent V) :
    quotientHomogeneousComplex (k := k) B a ⟶ quotientUnderlyingComplex (k := k) B where
  f i := ModuleCat.ofHom (quotientPiece (k := k) B a i).subtype
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [quotientHomogeneousComplex_d, quotientUnderlyingComplex_d]
    rfl

def quotientHomogeneousRetraction (B : Family V) (a : Exponent V) :
    quotientUnderlyingComplex (k := k) B ⟶ quotientHomogeneousComplex (k := k) B a where
  f i := ModuleCat.ofHom ((quotientProjection (k := k) B a i).codRestrict _
    (fun z => quotientProjection_mem B a i z))
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [quotientHomogeneousComplex_d, quotientUnderlyingComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (LinearMap.congr_fun (quotientProjection_differential B a j) z).symm

lemma quotientHomogeneousInclusion_retraction (B : Family V) (a : Exponent V) :
    quotientHomogeneousInclusion (k := k) B a ≫ quotientHomogeneousRetraction B a = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact CommAlg.Grading.projection_eq_self z.property

lemma quotientHomogeneousHomology_injective (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (quotientHomogeneousInclusion (k := k) B a) i).hom := by
  have hs : HomologicalComplex.homologyMap (quotientHomogeneousInclusion (k := k) B a) i ≫
      HomologicalComplex.homologyMap (quotientHomogeneousRetraction (k := k) B a) i = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, quotientHomogeneousInclusion_retraction,
      HomologicalComplex.homologyMap_id]
  intro x y h
  have hh := congrArg (HomologicalComplex.homologyMap (quotientHomogeneousRetraction (k := k) B a) i) h
  simpa only [← ModuleCat.comp_apply, hs, ModuleCat.id_apply] using hh

def quotientToDerivedTor [Nontrivial k] (B : Family V) (a : Exponent V) (i : ℕ) :
    (quotientHomogeneousComplex (k := k) B a).homology i ⟶
      (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
        (finitePolynomialTor i
          (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) :=
  HomologicalComplex.homologyMap (quotientHomogeneousInclusion (k := k) B a) i ≫
    (quotientTorIso (k := k) B i).inv

lemma quotientToDerivedTor_injective [Nontrivial k] (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (quotientToDerivedTor (k := k) B a i).hom := by
  intro x y h
  apply quotientHomogeneousHomology_injective (k := k) B a i
  apply (quotientTorIso (k := k) B i).symm.toLinearEquiv.injective
  exact h

/-- The usual fine component, as a submodule of actual derived Tor. -/
def quotientGradedTor [Nontrivial k] (B : Family V) (a : Exponent V) (i : ℕ) :
    Submodule k ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)))) :=
  LinearMap.range (quotientToDerivedTor (k := k) B a i).hom

def quotientGradedTorIso [Nontrivial k] (B : Family V) (a : Exponent V) (i : ℕ) :
    (quotientHomogeneousComplex (k := k) B a).homology i ≅
      ModuleCat.of k (quotientGradedTor (k := k) B a i) :=
  (LinearEquiv.ofInjective (quotientToDerivedTor (k := k) B a i).hom
    (quotientToDerivedTor_injective (k := k) B a i)).toModuleIso

lemma quotientHomogeneousInclusion_retraction_ne (B : Family V) (a b : Exponent V)
    (hab : a ≠ b) :
    quotientHomogeneousInclusion (k := k) B a ≫ quotientHomogeneousRetraction B b = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact CommAlg.Grading.projection_eq_zero (Ne.symm hab) z.property

def quotientProjector (B : Family V) (a : Exponent V) :
    quotientUnderlyingComplex (k := k) B ⟶ quotientUnderlyingComplex (k := k) B :=
  quotientHomogeneousRetraction B a ≫ quotientHomogeneousInclusion B a

@[simp] lemma quotientProjector_f (B : Family V) (a : Exponent V) (i : ℕ) :
    (quotientProjector (k := k) B a).f i =
      ModuleCat.ofHom (quotientProjection (k := k) B a i) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The genuine homology is the sum of its fine pieces; the preceding lemma
proves that distinct pieces are independent. -/
lemma quotient_homology_decomposition (B : Family V) (i : ℕ)
    (x : (quotientUnderlyingComplex (k := k) B).homology i) :
    ∃ s : Finset (Exponent V),
      ∑ a ∈ s, HomologicalComplex.homologyMap (quotientProjector (k := k) B a) i x = x := by
  let C := quotientUnderlyingComplex (k := k) B
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance x
  let s := ((quotientCoefficientBasis (k := k) B i).repr (C.iCycles i z)).support.image
    quotientDegree
  have hz : ∑ a ∈ s, HomologicalComplex.cyclesMap
      (quotientProjector (k := k) B a) i z = z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
    rw [map_sum]
    calc
      ∑ a ∈ s, C.iCycles i
          (HomologicalComplex.cyclesMap (quotientProjector (k := k) B a) i z) =
          ∑ a ∈ s, quotientProjection (k := k) B a i (C.iCycles i z) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact congrArg (fun f : C.cycles i ⟶ C.X i => f z)
          (HomologicalComplex.cyclesMap_i (quotientProjector (k := k) B a) i)
      _ = C.iCycles i z := by
        exact CommAlg.Grading.sum_projections (quotientCoefficientBasis (k := k) B i)
          quotientDegree (C.iCycles i z)
  refine ⟨s, ?_⟩
  calc
    ∑ a ∈ s, HomologicalComplex.homologyMap (quotientProjector (k := k) B a) i
        (C.homologyπ i z) =
        ∑ a ∈ s, C.homologyπ i
          (HomologicalComplex.cyclesMap (quotientProjector (k := k) B a) i z) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun f : C.cycles i ⟶ C.homology i => f z)
        (HomologicalComplex.homologyπ_naturality (quotientProjector (k := k) B a) i)
    _ = C.homologyπ i
        (∑ a ∈ s, HomologicalComplex.cyclesMap (quotientProjector (k := k) B a) i z) :=
      (map_sum _ _ _).symm
    _ = _ := congrArg (C.homologyπ i) hz

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientBetti -/
section

set_option autoImplicit false

/-! # Finiteness and the usual Betti numbers of the coefficient quotients -/

noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CategoryTheory.Limits
open CommAlg.Polymatroid CommAlg.Koszul

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance quotientDegreeFiber_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    Finite {t : QuotientIndex B i // quotientDegree t = a} := by
  apply Finite.of_injective (fun t : {t : QuotientIndex B i // quotientDegree t = a} => t.val.1)
  intro t u he
  rcases t with ⟨⟨s, x⟩, ht⟩
  rcases u with ⟨⟨s', y⟩, hu⟩
  dsimp at he
  subst s'
  change x.val + faceExponent s.val = a at ht
  change y.val + faceExponent s.val = a at hu
  have hxy : x = y := Subtype.ext (add_right_cancel (ht.trans hu.symm))
  subst y
  rfl

instance quotientPiece_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (quotientPiece (k := k) B a i) :=
  (quotientPieceBasis (k := k) B a i).finiteDimensional_of_finite

instance quotientHomogeneousHomology_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k ((quotientHomogeneousComplex (k := k) B a).homology i) := by
  let C := quotientHomogeneousComplex (k := k) B a
  letI : FiniteDimensional k (C.X i) := quotientPiece_finite B a i
  letI : FiniteDimensional k (C.cycles i) :=
    FiniteDimensional.of_injective (C.iCycles i).hom
      ((ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance)
  exact FiniteDimensional.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance)

instance quotientGradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (quotientGradedTor (k := k) B a i) :=
  FiniteDimensional.of_injective (quotientGradedTorIso (k := k) B a i).inv.hom
    ((ModuleCat.mono_iff_injective (quotientGradedTorIso (k := k) B a i).inv).mp inferInstance)

/-- The ordinary multigraded Betti number of the actual quotient `S/C`. -/
def quotientBettiNumber (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k (quotientGradedTor (k := k) B a i)

lemma quotientBettiNumber_eq_homology (B : Family V) (a : Exponent V) (i : ℕ) :
    quotientBettiNumber (k := k) B a i =
      Module.finrank k ((quotientHomogeneousComplex (k := k) B a).homology i) :=
  (quotientGradedTorIso (k := k) B a i).toLinearEquiv.finrank_eq.symm

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.GradedTor -/
section

/-! # Standard multigraded pieces as actual submodules of genuine derived Tor

The degree pieces below are images in Mathlib's derived tensor functor. Their inclusions split
by the homogeneous projections of the actual Koszul resolution. No combinatorial support
condition is used in their definition.
-/

noncomputable section

set_option maxHeartbeats 100000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Inclusion of the genuine homogeneous subcomplex. -/
def homogeneousInclusion (B : Family V) (a : Exponent V) :
    homogeneousComplex (k := k) B a ⟶ underlyingComplex (k := k) B where
  f i := ModuleCat.ofHom (homogeneousPiece (k := k) B a i).subtype
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [homogeneousComplex_d, underlyingComplex_d]
    rfl

/-- Projection onto the genuine homogeneous subcomplex. -/
def homogeneousRetraction (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ homogeneousComplex (k := k) B a where
  f i := ModuleCat.ofHom ((homogeneousProjection (k := k) B a i).codRestrict _
    (fun z => homogeneousProjection_mem B a i z))
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [homogeneousComplex_d, underlyingComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (LinearMap.congr_fun (homogeneousProjection_differential B a j) z).symm

lemma homogeneousInclusion_retraction (B : Family V) (a : Exponent V) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B a = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_self z.property

lemma homogeneousHomology_injective (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (homogeneousInclusion (k := k) B a) i).hom := by
  have hs : HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B a) i ≫
      HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, homogeneousInclusion_retraction,
      HomologicalComplex.homologyMap_id]
  intro x y h
  have hh := congrArg (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i) h
  simpa only [← ModuleCat.comp_apply, hs, ModuleCat.id_apply] using hh

variable [Nontrivial k]

/-- The map from homogeneous Koszul homology into the actual derived Tor module. -/
def toDerivedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).homology i ⟶
      (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
        (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
  HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B a) i ≫ (coefficientTorIso (k := k) B i).inv

lemma toDerivedTor_injective (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (toDerivedTor (k := k) B a i).hom := by
  intro x y h
  apply homogeneousHomology_injective (k := k) B a i
  apply (coefficientTorIso (k := k) B i).symm.toLinearEquiv.injective
  exact h

/-- The standard degree component, as a genuine submodule of derived Tor. -/
def gradedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    Submodule k ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :=
  LinearMap.range (toDerivedTor (k := k) B a i).hom

/-- Every homogeneous Koszul homology group is isomorphic to its actual derived-Tor component. -/
def gradedTorIso (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).homology i ≅ ModuleCat.of k (gradedTor (k := k) B a i) :=
  (LinearEquiv.ofInjective (toDerivedTor (k := k) B a i).hom (toDerivedTor_injective (k := k) B a i)).toModuleIso

/-- Nonzero multigraded Betti support defined using genuine derived Tor. -/
def GradedBettiNonzero (B : Family V) (a : Exponent V) (i : ℕ) : Prop :=
  ¬ IsZero (ModuleCat.of k (gradedTor (k := k) B a i))

lemma gradedBettiNonzero_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    GradedBettiNonzero (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  unfold GradedBettiNonzero
  rw [← (gradedTorIso (k := k) B a i).isZero_iff, homogeneous_homology_nonzero_iff]

/-- The homological shift ideal, generated by precisely the nonzero genuine Tor multidegrees. -/
def homologicalShift (B : Family V) (i : ℕ) : Ideal (MvPolynomial V k) :=
  Ideal.span ((fun a : Exponent V => MvPolynomial.monomial a (1 : k)) ''
    {a | GradedBettiNonzero (k := k) B a i})

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.TorGrading -/
section

/-! # Completeness and independence of the genuine Tor multigrading

Every derived Tor class is a finite sum of the degree components defined in `GradedTor`.
The projections onto distinct components annihilate one another, so this is a genuine
internal grading of the actual derived tensor module.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Distinct multidegrees have orthogonal chain projections. -/
lemma homogeneousInclusion_retraction_ne (B : Family V) (a b : Exponent V)
    (hab : a ≠ b) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B b = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_zero (Ne.symm hab) z.property

/-- The chain endomorphism projecting to one degree and including it again. -/
def homogeneousProjector (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ underlyingComplex (k := k) B :=
  homogeneousRetraction (k := k) B a ≫ homogeneousInclusion (k := k) B a

@[simp] lemma homogeneousProjector_f (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousProjector (k := k) B a).f i =
      ModuleCat.ofHom (homogeneousProjection (k := k) B a i) := rfl

/-- Every actual Koszul homology class is a finite sum of its homogeneous projections. -/
lemma homogeneous_homology_decomposition (B : Family V) (i : ℕ)
    (x : (underlyingComplex (k := k) B).homology i) :
    ∃ s : Finset (Exponent V),
      ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i x = x := by
  let K := underlyingComplex (k := k) B
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x
  let s := ((monomialCoefficientBasis (k := k) B i).repr (K.iCycles i z)).support.image
    monomialDegree
  have hz : ∑ a ∈ s, HomologicalComplex.cyclesMap
      (homogeneousProjector (k := k) B a) i z = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    rw [map_sum]
    calc
      ∑ a ∈ s, K.iCycles i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) =
          ∑ a ∈ s, homogeneousProjection (k := k) B a i (K.iCycles i z) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := congrArg (fun f : K.cycles i ⟶ K.X i => f z)
          (HomologicalComplex.cyclesMap_i (homogeneousProjector (k := k) B a) i)
        exact h
      _ = _ := homogeneous_decomposition B i (K.iCycles i z)
  refine ⟨s, ?_⟩
  calc
    ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i
        (K.homologyπ i z) =
        ∑ a ∈ s, K.homologyπ i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun f : K.cycles i ⟶ K.homology i => f z)
        (HomologicalComplex.homologyπ_naturality (homogeneousProjector (k := k) B a) i)
    _ = K.homologyπ i
        (∑ a ∈ s, HomologicalComplex.cyclesMap
          (homogeneousProjector (k := k) B a) i z) := (map_sum _ _ _).symm
    _ = _ := congrArg (K.homologyπ i) hz

variable [Nontrivial k]

/-- A nonzero multigraded Betti component forces the genuine derived Tor module to be nonzero. -/
lemma derivedTor_nonzero_of_graded (B : Family V) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) := by
  intro hz
  letI : Subsingleton (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  apply h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  exact Subsingleton.elim (α := finitePolynomialTor i
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) x.val y.val

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.BettiNumbers -/
section

/-! # Genuine finite multigraded Betti numbers

Over a field, every homogeneous component of the derived Tor module is finite-dimensional.
Its dimension therefore has positive support exactly at the degree components used to define
homological shift ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance homogeneousPiece_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (homogeneousPiece (k := k) B a i) := by
  letI : FiniteDimensional k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
    (faceChainBasis (k := k) B a i).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective (faceHomogeneousEquiv (k := k) B a i).symm.toLinearMap
    (faceHomogeneousEquiv (k := k) B a i).symm.injective

instance homogeneousHomology_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k ((homogeneousComplex (k := k) B a).homology i) := by
  let K := homogeneousComplex (k := k) B a
  letI : FiniteDimensional k (K.X i) := homogeneousPiece_finite B a i
  letI : FiniteDimensional k (K.cycles i) :=
    FiniteDimensional.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact FiniteDimensional.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

instance gradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (gradedTor (k := k) B a i) := by
  exact FiniteDimensional.of_injective (gradedTorIso (k := k) B a i).inv.hom
    ((ModuleCat.mono_iff_injective (gradedTorIso (k := k) B a i).inv).mp inferInstance)

/-- The actual multigraded Betti number: dimension of the corresponding derived Tor component. -/
def bettiNumber (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k (gradedTor (k := k) B a i)

lemma bettiNumber_pos_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔ GradedBettiNonzero (k := k) B a i := by
  unfold bettiNumber GradedBettiNonzero
  rw [Nat.pos_iff_ne_zero]
  have he : Module.finrank k (gradedTor (k := k) B a i) = 0 ↔
      Subsingleton (gradedTor (k := k) B a i) :=
    Module.finrank_zero_iff (R := k) (M := gradedTor (k := k) B a i)
  exact (not_congr he).trans (not_congr (ModuleCat.isZero_iff_subsingleton
    (M := ModuleCat.of k (gradedTor (k := k) B a i))).symm)

lemma bettiNumber_pos_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  rw [bettiNumber_pos_iff, gradedBettiNonzero_iff_faces]

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MonomialColon -/
section
set_option autoImplicit false

/-!
# Colon of a monomial ideal by a monomial

This is a coefficientwise theorem for actual polynomial ideals over an arbitrary
commutative semiring. It is the algebraic bridge used for predecessor ratios.
-/

noncomputable section

namespace FourPapers.Sublattice

open MvPolynomial

variable {V k : Type*} [CommSemiring k]

/-- A monomial ideal, specified by an arbitrary set of exponent vectors. -/
def exponentIdeal (B : Set (V →₀ ℕ)) : Ideal (MvPolynomial V k) :=
  Ideal.span ((fun b : V →₀ ℕ => monomial b (1 : k)) '' B)

lemma mem_exponentIdeal_iff (B : Set (V →₀ ℕ)) (f : MvPolynomial V k) :
    f ∈ exponentIdeal B ↔ ∀ a ∈ f.support, ∃ b ∈ B, b ≤ a :=
  mem_ideal_span_monomial_image

lemma mul_monomial_mem_exponentIdeal_iff (B : Set (V →₀ ℕ))
    (a : V →₀ ℕ) (f : MvPolynomial V k) :
    f * monomial a 1 ∈ exponentIdeal B ↔
      ∀ d ∈ f.support, ∃ b ∈ B, b ≤ d + a := by
  classical
  rw [mem_exponentIdeal_iff]
  constructor
  · intro h d hd
    apply h (d + a)
    rw [mem_support_iff,coeff_mul_monomial,mul_one]
    exact mem_support_iff.mp hd
  · intro h e he
    have hcoeff : (f * monomial a 1).coeff e ≠ 0 := mem_support_iff.mp he
    have hae : a ≤ e := by
      by_contra hn
      simp [coeff_mul_monomial',hn] at hcoeff
    have hd : e - a ∈ f.support := by
      rw [mem_support_iff]
      simpa [coeff_mul_monomial',hae] using hcoeff
    simpa [tsub_add_cancel_of_le hae] using h (e - a) hd

/-- Colon ideals are generated by the componentwise truncated exponent differences,
which are exactly the exponents of the quotients by greatest common divisors. -/
theorem exponentIdeal_colon_monomial (B : Set (V →₀ ℕ)) (a : V →₀ ℕ) :
    (exponentIdeal (k := k) B).colon {monomial a 1} =
      exponentIdeal ((fun b => b - a) '' B) := by
  classical
  ext f
  rw [Submodule.mem_colon_singleton,smul_eq_mul,mul_monomial_mem_exponentIdeal_iff,
    mem_exponentIdeal_iff]
  constructor
  · intro h d hd
    obtain ⟨b,hb,hbd⟩ := h d hd
    exact ⟨b - a,⟨b,hb,rfl⟩,tsub_le_iff_right.mpr hbd⟩
  · intro h d hd
    obtain ⟨e,⟨b,hb,rfl⟩,hbd⟩ := h d hd
    exact ⟨b,hb,tsub_le_iff_right.mp hbd⟩

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteDefinitions -/
section
set_option autoImplicit false

/-!
# Exact finite row polynomial rings, ideals, powers, and predecessor colons

Each row may have its own size. The universe lift is proved equivalent to the
ordinary finite row/column pairs and introduces no additional variables.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical Finset MvPolynomial
open CommAlg.Polymatroid
open scoped Pointwise

universe u

variable {d : ℕ} (n : Fin d → ℕ)

abbrev FiniteTuple := ∀ r, Fin (n r)
/-- `ULift` changes only the universe; the variables are still exactly one per
row/column pair, as witnessed by `finiteVariableEquiv` below. -/
abbrev FiniteVariable : Type u := Σ r, ULift.{u} (Fin (n r))

def finiteVariableEquiv : FiniteVariable.{u} n ≃ (Σ r, Fin (n r)) where
  toFun x := ⟨x.1,x.2.down⟩
  invFun x := ⟨x.1,ULift.up x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An orientation of the finite variable set, used only for the Koszul exterior signs. -/
noncomputable instance finiteVariableLinearOrder : LinearOrder (FiniteVariable.{u} n) :=
  LinearOrder.lift' (Fintype.equivFin (FiniteVariable.{u} n)) (Fintype.equivFin _).injective

def finiteRowExponent (a : FiniteTuple n) : Exponent (FiniteVariable.{u} n) :=
  ∑ r, Finsupp.single ⟨r, ULift.up (a r)⟩ 1

def finiteRowMonomial {k : Type*} [CommSemiring k] (a : FiniteTuple n) :
    MvPolynomial (FiniteVariable.{u} n) k := ∏ r, X ⟨r, ULift.up (a r)⟩

lemma finiteRowMonomial_eq_monomial {k : Type*} [CommSemiring k] (a : FiniteTuple n) :
    finiteRowMonomial n (k := k) a = monomial (finiteRowExponent n a) 1 := by
  unfold finiteRowMonomial finiteRowExponent
  rw [monomial_sum_one]
  apply prod_congr rfl
  intro r hr
  rfl

def finiteRowFamily (E : Finset (FiniteTuple n)) : Family (FiniteVariable.{u} n) :=
  E.image (finiteRowExponent n)

/-- The ideal is generated by the actual products of one variable from each row. -/
def finiteSublatticeIdeal {k : Type*} [CommSemiring k] (E : Finset (FiniteTuple n)) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  Ideal.span ((finiteRowMonomial n (k := k)) '' (E : Set (FiniteTuple n)))

lemma finiteSublatticeIdeal_eq_monomialIdeal {k : Type*} [CommSemiring k]
    (E : Finset (FiniteTuple n)) :
    finiteSublatticeIdeal n (k := k) E = monomialIdeal k (finiteRowFamily n E) := by
  unfold finiteSublatticeIdeal monomialIdeal finiteRowFamily
  apply congrArg Ideal.span
  ext f
  simp only [coe_image, Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨finiteRowExponent n a, ⟨a, ha, rfl⟩, (finiteRowMonomial_eq_monomial n a).symm⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, finiteRowMonomial_eq_monomial n a⟩

/-- Ordinary powers represented by their genuine monomial generators. -/
def exponentPowerFamily {V : Type*} [DecidableEq V] (B : Finset (V →₀ ℕ)) :
    ℕ → Finset (V →₀ ℕ)
  | 0 => {0}
  | m + 1 => ((exponentPowerFamily B m).product B).image fun bc => bc.1 + bc.2

lemma exponentFamily_mul {V k : Type*} [Fintype V] [DecidableEq V] [CommSemiring k]
    (B C : Family V) :
    monomialIdeal k B * monomialIdeal k C =
      monomialIdeal k ((B.product C).image (fun bc => bc.1 + bc.2)) := by
  classical
  unfold monomialIdeal
  rw [Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨b + c, mem_image.mpr ⟨(b,c), mem_product.mpr ⟨hb,hc⟩, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨b,c⟩, hbc, rfl⟩ := mem_image.mp ha
    obtain ⟨hb,hc⟩ := mem_product.mp hbc
    refine Set.mem_mul.mpr ⟨monomial b 1, ⟨b,hb,rfl⟩,
      monomial c 1, ⟨c,hc,rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]

lemma exponentPowerFamily_ideal {V k : Type*} [Fintype V] [DecidableEq V] [CommSemiring k]
    (B : Family V) (m : ℕ) :
    monomialIdeal k (exponentPowerFamily B m) = (monomialIdeal k B) ^ m := by
  induction m with
  | zero => simp [exponentPowerFamily, monomialIdeal]
  | succ m ih => rw [exponentPowerFamily, ← exponentFamily_mul, ih, pow_succ]

lemma finitePowerFamily_ideal {k : Type*} [CommSemiring k]
    (E : Finset (FiniteTuple n)) (m : ℕ) :
    monomialIdeal k (exponentPowerFamily (finiteRowFamily n E) m) =
      (finiteSublatticeIdeal n (k := k) E) ^ m := by
  rw [exponentPowerFamily_ideal, finiteSublatticeIdeal_eq_monomialIdeal]

def finiteLexBefore (b a : FiniteTuple n) : Prop :=
  ∃ r, b r < a r ∧ ∀ s < r, b s = a s

def finitePrefix (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    Finset (FiniteTuple n) := E.filter fun b => finiteLexBefore n b a

def finitePredecessorFamily (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    Family (FiniteVariable.{u} n) :=
  (finitePrefix n E a).image fun b => finiteRowExponent n b - finiteRowExponent n a

/-- The colon appearing in the paper, defined as an actual ideal colon. -/
def finitePredecessorColon {k : Type*} [CommSemiring k]
    (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  (finiteSublatticeIdeal n (k := k) (finitePrefix n E a)).colon {finiteRowMonomial n a}

/-- The generator family used for the coefficient quotient equals the actual
lexicographic predecessor colon; there is no assumed colon formula. -/
lemma finitePredecessorColon_eq {k : Type*} [CommSemiring k]
    (E : Finset (FiniteTuple n)) (a : FiniteTuple n) :
    finitePredecessorColon n (k := k) E a =
      monomialIdeal k (finitePredecessorFamily n E a) := by
  rw [finitePredecessorColon, finiteSublatticeIdeal_eq_monomialIdeal,
    finiteRowMonomial_eq_monomial]
  change (exponentIdeal (k := k) (↑(finiteRowFamily n (finitePrefix n E a)))).colon
      {monomial (finiteRowExponent n a) 1} =
    exponentIdeal (k := k) (↑(finitePredecessorFamily n E a))
  rw [exponentIdeal_colon_monomial]
  apply congrArg (exponentIdeal (k := k))
  simp [finiteRowFamily, finitePredecessorFamily, Set.image_image]

def FiniteMultichain (E : Finset (FiniteTuple n)) (m : ℕ) :=
  {w : Fin m → E // Monotone (fun s => (w s).val)}

instance finiteMultichainFintype (E : Finset (FiniteTuple n)) (m : ℕ) :
    Fintype (FiniteMultichain n E m) := by
  classical
  unfold FiniteMultichain
  infer_instance

def finiteChainShift {E : Finset (FiniteTuple n)} {m : ℕ}
    (w : FiniteMultichain n E m) : Exponent (FiniteVariable.{u} n) :=
  ∑ s, finiteRowExponent n (w.val s).val

def finiteChainCoefficientFamily {E : Finset (FiniteTuple n)} {m : ℕ}
    (w : FiniteMultichain n E m) : Family (FiniteVariable.{u} n) :=
  univ.biUnion fun s => finitePredecessorFamily n E (w.val s).val

/-- The sum of the genuine colon ideals is precisely the monomial coefficient
ideal used in the fine Betti formula. -/
lemma finiteChainCoefficientFamily_ideal {k : Type*} [CommSemiring k]
    {E : Finset (FiniteTuple n)} {m : ℕ} (w : FiniteMultichain n E m) :
    monomialIdeal k (finiteChainCoefficientFamily n w) =
      ⨆ s, finitePredecessorColon n (k := k) E (w.val s).val := by
  simp_rw [finitePredecessorColon_eq]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    obtain ⟨s, hs, ha⟩ := mem_biUnion.mp ha
    exact (le_iSup (fun s => monomialIdeal k (finitePredecessorFamily n E (w.val s).val)) s)
      (Ideal.subset_span ⟨a, ha, rfl⟩)
  · apply iSup_le
    intro s
    apply Ideal.span_mono
    apply Set.image_mono
    intro a ha
    exact mem_biUnion.mpr ⟨s, mem_univ s, ha⟩

def finiteLatticeClosed (E : Finset (FiniteTuple n)) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E) ∧ (∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E)

end FourPapers.Sublattice
end

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteRows -/
section

set_option autoImplicit false

/-!
# The exact all-powers Betti target in the finite row ring

`AllPowersBettiFormula` is a specification, not a proved assertion. A completed
verification must supply it from the actual sublattice hypothesis, with no
additional mathematical assumptions.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical Finset CommAlg.Polymatroid

universe u
variable {d : ℕ} (n : Fin d → ℕ)

/-- Exact fine Betti formula of Theorem 1.2, with negative residual multidegrees
interpreted as zero. This is a target proposition, not a verified assertion. -/
def AllPowersBettiFormula (E : Finset (FiniteTuple n)) : Prop :=
  ∀ (k : Type u) [Field k], ∀ m : ℕ, 0 < m →
    ∀ (p : ℕ) (α : Exponent (FiniteVariable.{u} n)),
      CommAlg.Koszul.bettiNumber (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) α p =
      ∑ w : FiniteMultichain n E m,
        if finiteChainShift n w ≤ α then
          quotientBettiNumber (k := k) (finiteChainCoefficientFamily n w)
            (α - finiteChainShift n w) p
        else 0

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerDegrees -/
section

set_option autoImplicit false

/-!
# Integer fine degrees and the zero negative strands

Natural exponent degrees are embedded into integer exponent degrees by their
actual coordinatewise inclusion. Regrading the genuine Tor submodules along
this injective map gives the usual integer grading. The negative pieces vanish
because they contain no homogeneous basis vector, not by an independent axiom
or a convention inserted into the theorem statement.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid CommAlg.Koszul

section Exponents

variable {V : Type*}

def integerExponent (a : V →₀ ℕ) : V →₀ ℤ := a.mapRange Int.ofNat (by rfl)

@[simp] lemma integerExponent_apply (a : V →₀ ℕ) (v : V) :
    integerExponent a v = (a v : ℤ) := rfl

lemma integerExponent_injective : Function.Injective (integerExponent (V := V)) := by
  intro a b h
  ext v
  exact Int.ofNat_inj.mp (congrArg (fun c : V →₀ ℤ => c v) h)

lemma integerExponent_nonneg (a : V →₀ ℕ) (v : V) : 0 ≤ integerExponent a v :=
  Int.ofNat_nonneg _

def naturalExponent (a : V →₀ ℤ) : V →₀ ℕ := a.mapRange Int.toNat (by rfl)

lemma integerExponent_naturalExponent {a : V →₀ ℤ} (ha : ∀ v, 0 ≤ a v) :
    integerExponent (naturalExponent a) = a := by
  ext v
  exact Int.toNat_of_nonneg (ha v)

lemma integerExponent_exists_iff (a : V →₀ ℤ) :
    (∃ b, integerExponent b = a) ↔ ∀ v, 0 ≤ a v := by
  constructor
  · rintro ⟨b,rfl⟩ v
    exact integerExponent_nonneg b v
  · intro h
    exact ⟨naturalExponent a,integerExponent_naturalExponent h⟩

section Regrading

variable {K M I : Type*} [CommRing K] [AddCommMonoid M] [Module K M]

def integerRegrade (N : (V →₀ ℕ) → Submodule K M) (a : V →₀ ℤ) : Submodule K M :=
  ⨆ b, ⨆ (_ : integerExponent b = a), N b

@[simp] lemma integerRegrade_nat (N : (V →₀ ℕ) → Submodule K M) (a : V →₀ ℕ) :
    integerRegrade N (integerExponent a) = N a := by
  apply le_antisymm
  · apply iSup_le
    intro b
    apply iSup_le
    intro h
    obtain rfl := integerExponent_injective h
    exact le_rfl
  · exact le_iSup_of_le a (le_iSup_of_le rfl le_rfl)

lemma integerRegrade_eq_bot_of_not_image (N : (V →₀ ℕ) → Submodule K M)
    (a : V →₀ ℤ) (ha : ¬ ∃ b, integerExponent b = a) : integerRegrade N a = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro b
  apply iSup_le
  intro h
  exact (ha ⟨b,h⟩).elim

lemma integerRegrade_eq_bot_of_negative (N : (V →₀ ℕ) → Submodule K M)
    (a : V →₀ ℤ) {v : V} (ha : a v < 0) : integerRegrade N a = ⊥ := by
  apply integerRegrade_eq_bot_of_not_image
  rintro ⟨b,h⟩
  exact (not_lt_of_ge (integerExponent_nonneg b v)) (h.symm ▸ ha)

lemma iSup_integerRegrade (N : (V →₀ ℕ) → Submodule K M) :
    (⨆ a, integerRegrade N a) = ⨆ b, N b := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro b
    exact iSup_le fun _ => le_iSup N b
  · apply iSup_le
    intro b
    rw [← integerRegrade_nat N b]
    exact le_iSup _ _

/-- Regrading the actual basis-degree pieces is exactly the span of basis vectors
whose integer exponent is the specified degree. -/
theorem integerRegrade_basisPiece
    (b : Module.Basis I K M) (degree : I → V →₀ ℕ) (a : V →₀ ℤ) :
    integerRegrade (CommAlg.Grading.Piece b degree) a =
      CommAlg.Grading.Piece b (integerExponent ∘ degree) a := by
  by_cases ha : ∃ c, integerExponent c = a
  · obtain ⟨c,rfl⟩ := ha
    rw [integerRegrade_nat]
    unfold CommAlg.Grading.Piece
    congr 1
    congr 1
    ext i
    exact (integerExponent_injective.eq_iff).symm
  · rw [integerRegrade_eq_bot_of_not_image _ _ ha]
    have hs : {i | (integerExponent ∘ degree) i = a} = (∅ : Set I) := by
      ext i
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => ha ⟨degree i,h⟩
    change ⊥ = Submodule.span K (b '' {i | (integerExponent ∘ degree) i = a})
    rw [hs]
    simp

end Regrading
end Exponents

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Tor
variable [CommRing k] [Nontrivial k]

/-- Integer regrading of the actual derived Tor submodules of a monomial ideal. -/
def integerGradedTor (B : Family V) (a : V →₀ ℤ) (i : ℕ) :=
  integerRegrade (fun b => gradedTor (k := k) B b i) a

/-- Integer regrading of the actual derived Tor submodules of a monomial quotient. -/
def quotientIntegerGradedTor (B : Family V) (a : V →₀ ℤ) (i : ℕ) :=
  integerRegrade (fun b => quotientGradedTor (k := k) B b i) a

end Tor

section Betti
variable [Field k]

def integerBettiNumber (B : Family V) (a : V →₀ ℤ) (i : ℕ) : ℕ :=
  Module.finrank k (integerGradedTor (k := k) B a i)

def quotientIntegerBettiNumber (B : Family V) (a : V →₀ ℤ) (i : ℕ) : ℕ :=
  Module.finrank k (quotientIntegerGradedTor (k := k) B a i)

@[simp] theorem integerBettiNumber_nat (B : Family V) (a : Exponent V) (i : ℕ) :
    integerBettiNumber (k := k) B (integerExponent a) i = bettiNumber (k := k) B a i := by
  unfold integerBettiNumber integerGradedTor bettiNumber
  rw [integerRegrade_nat]

@[simp] theorem quotientIntegerBettiNumber_nat (B : Family V) (a : Exponent V) (i : ℕ) :
    quotientIntegerBettiNumber (k := k) B (integerExponent a) i =
      quotientBettiNumber (k := k) B a i := by
  unfold quotientIntegerBettiNumber quotientIntegerGradedTor quotientBettiNumber
  rw [integerRegrade_nat]

theorem integerBettiNumber_negative (B : Family V) (a : V →₀ ℤ) (i : ℕ)
    {v : V} (ha : a v < 0) : integerBettiNumber (k := k) B a i = 0 := by
  unfold integerBettiNumber integerGradedTor
  rw [integerRegrade_eq_bot_of_negative _ a ha]
  exact Module.finrank_zero_of_subsingleton

theorem quotientIntegerBettiNumber_negative (B : Family V) (a : V →₀ ℤ) (i : ℕ)
    {v : V} (ha : a v < 0) : quotientIntegerBettiNumber (k := k) B a i = 0 := by
  unfold quotientIntegerBettiNumber quotientIntegerGradedTor
  rw [integerRegrade_eq_bot_of_negative _ a ha]
  exact Module.finrank_zero_of_subsingleton

end Betti

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerFormula -/
section

set_option autoImplicit false

/-!
# Equivalence of natural and integer fine-degree formulas

This theorem extends a proof of the natural-degree formula to every integer fine
degree of the actual Tor grading. It supplies no missing all-powers argument.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma integerExponent_tsub {a b : Exponent V} (hab : b ≤ a) :
    integerExponent (a - b) = integerExponent a - integerExponent b := by
  ext v
  exact Int.ofNat_sub (hab v)

lemma quotientIntegerBettiNumber_shift_nat (B : Family V) (a b : Exponent V) (p : ℕ) :
    quotientIntegerBettiNumber (k := k) B (integerExponent a - integerExponent b) p =
      if b ≤ a then quotientBettiNumber (k := k) B (a - b) p else 0 := by
  by_cases h : b ≤ a
  · rw [if_pos h,← integerExponent_tsub h,quotientIntegerBettiNumber_nat]
  · rw [if_neg h]
    obtain ⟨v,hv⟩ : ∃ v, a v < b v := by
      by_contra hn
      push_neg at hn
      exact h hn
    apply quotientIntegerBettiNumber_negative B _ p
    change (a v : ℤ) - (b v : ℤ) < 0
    exact sub_neg.mpr (Int.ofNat_lt.mpr hv)

variable {d : ℕ} (n : Fin d → ℕ) (E : Finset (FiniteTuple n))

/-- Once the natural-degree theorem is proved, it gives the unrestricted integer
fine-degree formula with ordinary integer subtraction and no implicit truncation. -/
theorem integerFormula_of_allPowersBettiFormula
    (h : AllPowersBettiFormula.{u} n E) (k : Type u) [Field k]
    (m : ℕ) (hm : 0 < m) (p : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    integerBettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p =
      ∑ w : FiniteMultichain n E m,
        quotientIntegerBettiNumber (k := k) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w)) p := by
  by_cases hα : ∀ v, 0 ≤ α v
  · obtain ⟨a,rfl⟩ := (integerExponent_exists_iff α).mpr hα
    rw [integerBettiNumber_nat,h k m hm p a]
    apply Finset.sum_congr rfl
    intro w _
    exact (quotientIntegerBettiNumber_shift_nat _ _ _ _).symm
  · obtain ⟨v,hv⟩ : ∃ v, α v < 0 := by
      simpa only [not_forall,not_le] using hα
    rw [integerBettiNumber_negative _ _ _ hv]
    symm
    apply Finset.sum_eq_zero
    intro w _
    apply quotientIntegerBettiNumber_negative _ _ _
    change α v - ((finiteChainShift n w) v : ℤ) < 0
    exact (sub_le_self _ (Int.ofNat_nonneg _)).trans_lt hv

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.TorSymmetry -/
section

set_option autoImplicit false

/-!
# Tensor-order symmetry for the actual derived Tor functor

The computation resolves the residue module in the first tensor factor. The paper
writes the ideal in the first factor and resolves the residue in the second. The
braiding identifies the underlying additive functors before deriving them, giving
an explicit natural isomorphism between these two conventions.
-/

noncomputable section

namespace FourPapers.Sublattice

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasProjectiveResolutions C]

def leftDerivedNatIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (p : ℕ) :
    F.leftDerived p ≅ G.leftDerived p where
  hom := NatTrans.leftDerived e.hom p
  inv := NatTrans.leftDerived e.inv p
  hom_inv_id := by rw [← NatTrans.leftDerived_comp,e.hom_inv_id,NatTrans.leftDerived_id]
  inv_hom_id := by rw [← NatTrans.leftDerived_comp,e.inv_hom_id,NatTrans.leftDerived_id]

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]

/-- Symmetry is obtained before deriving; it does not assume a balanced-derived-
functor theorem or identify homology objects by definition. -/
def torPrimeSwapIso (p : ℕ) (X Y : C) :
    ((Tor' C p).obj X).obj Y ≅ ((Tor C p).obj Y).obj X :=
  (leftDerivedNatIso (BraidedCategory.tensorLeftIsoTensorRight Y).symm p).app X

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: CommAlg.KoszulComplex.ResidueCoefficients -/
section

/-! # The residue quotient is the coefficient field with its intended polynomial action -/

noncomputable section
namespace CommAlg.Koszul
open CategoryTheory MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

/-- The coefficient ring, with polynomial action by evaluation at zero. -/
def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)

/-- The quotient by all variables agrees as a polynomial module with the coefficient ring. -/
def residueCoefficientEquiv :
    FiniteResidue V k ≃ₗ[MvPolynomial V k] residueCoefficientModule (V := V) (k := k) where
  toFun := (residueRingEquiv (V := V) (k := k))
  invFun := (residueRingEquiv (V := V) (k := k)).symm
  left_inv := (residueRingEquiv (V := V) (k := k)).left_inv
  right_inv := (residueRingEquiv (V := V) (k := k)).right_inv
  map_add' := (residueRingEquiv (V := V) (k := k)).map_add
  map_smul' f q := by
    change (residueRingEquiv (V := V) (k := k)) (f • q) = constantCoeff f * (residueRingEquiv (V := V) (k := k)) q
    refine Quotient.inductionOn' q ?_
    intro p
    change (residueRingEquiv (V := V) (k := k))
      (Ideal.Quotient.mk (idealOfVars V k) (f * p)) =
      constantCoeff f * (residueRingEquiv (V := V) (k := k))
        (Ideal.Quotient.mk (idealOfVars V k) p)
    simp only [residueRingEquiv_mk, map_mul]

/-- Canonical polynomial-module isomorphism to the actual coefficient ring. -/
def residueCoefficientIso :
    ModuleCat.of (MvPolynomial V k) (FiniteResidue V k) ≅
      residueCoefficientModule (V := V) (k := k) :=
  residueCoefficientEquiv.toModuleIso

variable [Fintype V] [LinearOrder V]

/-- The derived Tor groups used throughout are isomorphic to derived Tor with the coefficient ring
itself, carrying precisely its standard evaluation-at-zero polynomial action. -/
def finitePolynomialTorCoefficientIso (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
        (residueCoefficientModule (V := V) (k := k))).obj M :=
  ((Functor.flip (Tor' (ModuleCat (MvPolynomial V k)) i)).obj M).mapIso residueCoefficientIso

end CommAlg.Koszul

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteTorConvention -/
section

set_option autoImplicit false

/-! # Exact comparison with the paper's `Tor^S(M,k)` convention -/

noncomputable section
namespace FourPapers.Sublattice

open CategoryTheory CommAlg.Koszul MvPolynomial

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The actual finite-variable Tor computation is isomorphic to Mathlib's Tor,
with the ideal/module in the first slot and `k` with its evaluation-at-zero action
in the second slot, exactly as in the paper. -/
def finitePolynomialTorPaperIso (p : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor p M ≅
      ((Tor (ModuleCat (MvPolynomial V k)) p).obj M).obj
        (residueCoefficientModule (V := V) (k := k)) :=
  finitePolynomialTorCoefficientIso p M ≪≫
    torPrimeSwapIso p (residueCoefficientModule (V := V) (k := k)) M

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Common.BiproductHomology -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open CategoryTheory CategoryTheory.Limits
universe u
variable {k : Type u} [CommRing k] {J : Type} [Fintype J]

/-- Finite biproducts follow from the already constructed finite products of
chain complexes; no existence premise is added to the homology statements. -/
noncomputable instance chainComplexHasFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} k) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Homology of a finite direct sum is the product of the actual categorical
homology modules. This follows from additivity of Mathlib's homology functor. -/
def homologyBiproductIso (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (⨁ C).homology i ≅ ModuleCat.of k (∀ j, (C j).homology i) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapBiproduct C ≪≫
    ModuleCat.biproductIsoPi (fun j => (C j).homology i)

section Field
variable {K : Type u} [Field K]

theorem finrank_homology_biproduct (C : J → ChainComplex (ModuleCat.{u} K) ℕ)
    (i : ℕ) [∀ j, FiniteDimensional K ((C j).homology i)] :
    Module.finrank K ((⨁ C).homology i) = ∑ j, Module.finrank K ((C j).homology i) := by
  rw [(homologyBiproductIso C i).toLinearEquiv.finrank_eq]
  exact Module.finrank_pi_fintype K

end Field
end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteDirectSumComplex -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical CategoryTheory CategoryTheory.Limits
universe u
variable {k : Type u} [CommRing k] {J : Type} [Fintype J]

def finiteDirectSumDifferential (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (Π₀ j, (C j).X (i+1)) →ₗ[k] (Π₀ j, (C j).X i) :=
  DFinsupp.mapRange.linearMap (fun j => ((C j).d (i+1) i).hom)

def finiteDirectSumComplex (C : J → ChainComplex (ModuleCat.{u} k) ℕ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (Π₀ j, (C j).X i))
    (fun i => ModuleCat.ofHom (finiteDirectSumDifferential C i)) (by
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro j
      exact ConcreteCategory.congr_hom ((C j).d_comp_d (i+2) (i+1) i) (x j))

@[simp] lemma finiteDirectSumComplex_d (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (finiteDirectSumComplex C).d (i+1) i = ModuleCat.ofHom (finiteDirectSumDifferential C i) := by
  simp [finiteDirectSumComplex]

def complexBiproductDegreeIso (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (⨁ C).X i ≅ ModuleCat.of k (∀ j, (C j).X i) :=
  (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapBiproduct C ≪≫
    ModuleCat.biproductIsoPi (fun j => (C j).X i)

lemma complexBiproductDegreeIso_hom_projection
    (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) (j : J) :
    (complexBiproductDegreeIso C i).hom ≫
        ModuleCat.ofHom (LinearMap.proj j : (∀ j, (C j).X i) →ₗ[k] (C j).X i) =
      (biproduct.π C j).f i := by
  rw [← ModuleCat.biproductIsoPi_inv_comp_π (fun j => (C j).X i) j]
  simp only [complexBiproductDegreeIso,Iso.trans_hom,Category.assoc,
    Iso.hom_inv_id_assoc,Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  rfl

lemma complexBiproductDegreeIso_hom_apply
    (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) (j : J) (x : (⨁ C).X i) :
    ((complexBiproductDegreeIso C i).hom x) j = (biproduct.π C j).f i x :=
  ConcreteCategory.congr_hom (complexBiproductDegreeIso_hom_projection C i j) x

lemma complexBiproductDegreeIso_d_apply
    (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i l : ℕ) (j : J) (x : (⨁ C).X i) :
    ((complexBiproductDegreeIso C l).hom ((⨁ C).d i l x)) j =
      (C j).d i l (((complexBiproductDegreeIso C i).hom x) j) := by
  rw [complexBiproductDegreeIso_hom_apply,complexBiproductDegreeIso_hom_apply]
  exact (ConcreteCategory.congr_hom ((biproduct.π C j).comm i l) x).symm

def finiteDirectSumDegreeEquiv (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (Π₀ j, (C j).X i) ≃ₗ[k] (⨁ C).X i :=
  (DFinsupp.linearEquivFunOnFintype (R := k) (M := fun j => (C j).X i)).trans
    (complexBiproductDegreeIso C i).toLinearEquiv.symm

lemma finiteDirectSumDegreeEquiv_cancel
    (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) (x : Π₀ j, (C j).X i) :
    (complexBiproductDegreeIso C i).hom (finiteDirectSumDegreeEquiv C i x) =
      fun j => x j := by
  change (complexBiproductDegreeIso C i).toLinearEquiv
    ((complexBiproductDegreeIso C i).toLinearEquiv.symm
      (DFinsupp.linearEquivFunOnFintype x)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The literal componentwise DFinsupp complex is the categorical finite direct
sum. Its differential is checked on each coordinate, including degree zero. -/
def finiteDirectSumBiproductIso (C : J → ChainComplex (ModuleCat.{u} k) ℕ) :
    finiteDirectSumComplex C ≅ ⨁ C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (finiteDirectSumDegreeEquiv C i).toModuleIso) (by
      intro i l hil
      obtain rfl : i=l+1 := hil.symm
      rw [finiteDirectSumComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Π₀ j, (C j).X (l+1)) at x
      apply (complexBiproductDegreeIso C l).toLinearEquiv.injective
      funext j
      change ((complexBiproductDegreeIso C l).hom
          ((⨁ C).d (l+1) l (finiteDirectSumDegreeEquiv C (l+1) x))) j =
        ((complexBiproductDegreeIso C l).hom
          (finiteDirectSumDegreeEquiv C l (finiteDirectSumDifferential C l x))) j
      rw [complexBiproductDegreeIso_d_apply,finiteDirectSumDegreeEquiv_cancel,
        finiteDirectSumDegreeEquiv_cancel]
      rfl)

def finiteDirectSumHomologyIso (C : J → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (finiteDirectSumComplex C).homology i ≅ ModuleCat.of k (∀ j, (C j).homology i) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
      (finiteDirectSumBiproductIso C) ≪≫ homologyBiproductIso C i

theorem finrank_homology_finiteDirectSum {K : Type u} [Field K]
    (C : J → ChainComplex (ModuleCat.{u} K) ℕ) (i : ℕ)
    [∀ j, FiniteDimensional K ((C j).homology i)] :
    Module.finrank K ((finiteDirectSumComplex C).homology i) =
      ∑ j, Module.finrank K ((C j).homology i) := by
  rw [(finiteDirectSumHomologyIso C i).toLinearEquiv.finrank_eq]
  exact Module.finrank_pi_fintype K

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.DFinsuppComplexData -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical CategoryTheory CategoryTheory.Limits
universe u
variable {k : Type u} [CommRing k] {J : Type} [Fintype J]
variable {M : J → Type u} [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]

def dfinsuppPiece (P : ∀ j, Submodule k (M j)) : Submodule k (Π₀ j, M j) :=
  ⨅ j, (P j).comap (DFinsupp.lapply j)

@[simp] lemma mem_dfinsuppPiece (P : ∀ j, Submodule k (M j)) (x : Π₀ j, M j) :
    x ∈ dfinsuppPiece P ↔ ∀ j, x j ∈ P j := by
  simp [dfinsuppPiece]

def dfinsuppPieceEquiv (P : ∀ j, Submodule k (M j)) :
    dfinsuppPiece P ≃ₗ[k] (Π₀ j, P j) where
  toFun x := DFinsupp.equivFunOnFintype.symm
    (fun j => ⟨x.val j,(mem_dfinsuppPiece P x.val).mp x.property j⟩)
  invFun y := ⟨DFinsupp.equivFunOnFintype.symm (fun j => (y j).val),by
    apply (mem_dfinsuppPiece P _).mpr
    intro j
    exact (y j).property⟩
  left_inv x := by apply Subtype.ext; apply DFinsupp.ext; intro j; rfl
  right_inv x := by apply DFinsupp.ext; intro j; apply Subtype.ext; rfl
  map_add' x y := by apply DFinsupp.ext; intro j; apply Subtype.ext; rfl
  map_smul' c x := by apply DFinsupp.ext; intro j; apply Subtype.ext; rfl

/-- The direct sum of the literal degree submodules and differentials. -/
def dfinsuppComplexData (C : ∀ j, SubmoduleComplexData k (M j)) :
    SubmoduleComplexData k (Π₀ j, M j) where
  piece i := dfinsuppPiece (fun j => (C j).piece i)
  d := DFinsupp.mapRange.linearMap (fun j => (C j).d)
  square_zero := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro j
    exact LinearMap.congr_fun (C j).square_zero (x j)
  lowers i x hx := by
    apply (mem_dfinsuppPiece _ _).mpr
    intro j
    exact (C j).lowers i (x j) ((mem_dfinsuppPiece _ x).mp hx j)

def dfinsuppComplexIso (C : ∀ j, SubmoduleComplexData k (M j)) :
    (dfinsuppComplexData C).complex ≅ finiteDirectSumComplex (fun j => (C j).complex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (dfinsuppPieceEquiv (fun j => (C j).piece i)).toModuleIso) (by
      intro i l hil
      obtain rfl : i=l+1 := hil.symm
      rw [SubmoduleComplexData.complex_d,finiteDirectSumComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro j
      apply Subtype.ext
      change (((C j).complex.d (l+1) l)
        ((dfinsuppPieceEquiv (fun j => (C j).piece (l+1)) x) j)).val =
          ((dfinsuppComplexData C).d x.val) j
      rw [SubmoduleComplexData.complex_d]
      rfl)

/-- The homology isomorphism is induced from the actual componentwise chain
complex, not from a numerical definition of homology. -/
def dfinsuppComplexHomologyIso (C : ∀ j, SubmoduleComplexData k (M j)) (i : ℕ) :
    (dfinsuppComplexData C).complex.homology i ≅
      ModuleCat.of k (∀ j, (C j).complex.homology i) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) i).mapIso
      (dfinsuppComplexIso C) ≪≫ finiteDirectSumHomologyIso (fun j => (C j).complex) i

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Crossing -/
section
set_option autoImplicit false

/-!
# The crossing-block lemma for finite sublattices

This file proves the full, unbounded combinatorial assertion of Lemma 2.4 of
`Sublattice resolutions and Betti preservation in all powers`.

A row generator has one variable `(r, a r)` in each row. For `b ≤ a`,
`ratio b a` is the support of `u_b / gcd(u_b,u_a)`. Every such ratio is squarefree.
A minimal generator of the sum of the predecessor ideals is therefore exactly an
inclusion-minimal member of the family `Occurs` below. The polynomial-ideal bridge
is supplied separately; this file makes no homological assertion.
-/

namespace FourPapers.Sublattice

open Finset

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The support of the predecessor ratio; only coordinates strictly lowered are used. -/
def ratio (b a : R → ℕ) : Finset (R × ℕ) :=
  (univ.filter fun r => b r < a r).image fun r => (r, b r)

@[simp] theorem mem_ratio {b a : R → ℕ} {r : R} {j : ℕ} :
    (r, j) ∈ ratio b a ↔ j = b r ∧ b r < a r := by
  simp only [ratio, mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨s, hs, rfl, hj⟩
    exact ⟨hj.symm, hs⟩
  · rintro ⟨rfl, h⟩
    exact ⟨r, h, rfl, rfl⟩

lemma ratio_nonempty {b a : R → ℕ} (hba : b ≤ a) (hne : b ≠ a) :
    (ratio b a).Nonempty := by
  have hx : ∃ r, b r < a r := by
    by_contra h
    push_neg at h
    apply hne
    ext r
    exact le_antisymm (hba r) (h r)
  rcases hx with ⟨r, hr⟩
  exact ⟨(r, b r), by simp [hr]⟩

/-- Coordinatewise meet closure, the only lattice axiom needed for crossing blocks. -/
def MeetClosed (E : Finset (R → ℕ)) : Prop :=
  ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E

/-- A ratio appearing in the sum of all predecessor ideals along a multichain. -/
def Occurs {m : ℕ} (E : Finset (R → ℕ)) (w : Fin m → R → ℕ)
    (g : Finset (R × ℕ)) : Prop :=
  ∃ s b, b ∈ E ∧ b ≤ w s ∧ b ≠ w s ∧ g = ratio b (w s)

/-- Inclusion-minimal ratio support, equivalently a minimal squarefree generator. -/
def MinimalRatio {m : ℕ} (E : Finset (R → ℕ)) (w : Fin m → R → ℕ)
    (g : Finset (R × ℕ)) : Prop :=
  Occurs E w g ∧ ∀ h, Occurs E w h → h ⊆ g → g ⊆ h

/-- A variable crosses at the first chain member strictly above its column index. -/
def Crosses {m : ℕ} (w : Fin m → R → ℕ) (p : Fin m) (x : R × ℕ) : Prop :=
  x.2 < w p x.1 ∧ ∀ q < p, w q x.1 ≤ x.2

lemma crosses_unique {m : ℕ} {w : Fin m → R → ℕ} {p q : Fin m}
    {x : R × ℕ} (hp : Crosses w p x) (hq : Crosses w q x) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim ((not_lt_of_ge (hq.2 p h)) hp.1)
  · exact h
  · exact False.elim ((not_lt_of_ge (hp.2 q h)) hq.1)

/-- Every minimal ratio uses variables from a single first-crossing block, and the
ratio already belongs to the predecessor ideal at that crossing step.
This is Lemma 2.4, with arbitrary finite row type and arbitrary chain length. -/
theorem minimalRatio_single_crossing {m : ℕ} {E : Finset (R → ℕ)}
    (hE : MeetClosed E) {w : Fin m → R → ℕ} (hw : ∀ s, w s ∈ E)
    (hmono : Monotone w) {g : Finset (R × ℕ)} (hg : MinimalRatio E w g) :
    ∃ p c, c ∈ E ∧ c ≤ w p ∧ c ≠ w p ∧
      g = ratio c (w p) ∧ ∀ x ∈ g, Crosses w p x := by
  classical
  rcases hg.1 with ⟨s, b, hbE, hbs, hbne, rfl⟩
  let g := ratio b (w s)
  have hgne : g.Nonempty := ratio_nonempty hbs hbne
  let T : Finset (Fin m) := univ.filter fun p => ∃ x ∈ g, x.2 < w p x.1
  have hsT : s ∈ T := by
    rcases hgne with ⟨⟨r,j⟩, hx⟩
    have hx' := mem_ratio.mp hx
    exact mem_filter.mpr ⟨mem_univ _, ⟨(r,j),hx,by simpa [hx'.1] using hx'.2⟩⟩
  have hT : T.Nonempty := ⟨s, hsT⟩
  let p : Fin m := T.min' hT
  have hpT : p ∈ T := min'_mem T hT
  have hps : p ≤ s := min'_le T s hsT
  have hwp : w p ≤ w s := hmono hps
  let c : R → ℕ := b ⊓ w p
  have hcE : c ∈ E := hE b hbE (w p) (hw p)
  have hcp : c ≤ w p := inf_le_right
  have hsub : ratio c (w p) ⊆ g := by
    rintro ⟨r,j⟩ hx
    rcases mem_ratio.mp hx with ⟨hj,hlt⟩
    have hb_lt : b r < w p r := by simpa [c, Pi.inf_apply, min_lt_iff] using hlt
    have hc_eq : c r = b r := min_eq_left (le_of_lt hb_lt)
    apply mem_ratio.mpr
    exact ⟨hj.trans hc_eq, lt_of_lt_of_le hb_lt (hwp r)⟩
  have hcross_at : ∃ x ∈ g, x.2 < w p x.1 := (mem_filter.mp hpT).2
  have hcne : c ≠ w p := by
    rcases hcross_at with ⟨⟨r,j⟩, hx, hlt⟩
    have hj : j = b r := (mem_ratio.mp hx).1
    intro he
    have hr := congrFun he r
    have hbr : b r < w p r := by simpa [hj] using hlt
    have hc_eq : c r = b r := min_eq_left (le_of_lt hbr)
    exact (ne_of_lt hbr) (hc_eq.symm.trans hr)
  have hocc : Occurs E w (ratio c (w p)) := ⟨p,c,hcE,hcp,hcne,rfl⟩
  have heq : g = ratio c (w p) := subset_antisymm (hg.2 _ hocc hsub) hsub
  refine ⟨p,c,hcE,hcp,hcne,heq,?_⟩
  intro x hx
  constructor
  · rcases x with ⟨r,j⟩
    have hxg : (r, j) ∈ g := hx
    have hx' := mem_ratio.mp (heq ▸ hxg)
    simpa [hx'.1] using hx'.2
  · intro q hqp
    by_contra hq
    have hq' : x.2 < w q x.1 := lt_of_not_ge hq
    have hqT : q ∈ T := mem_filter.mpr ⟨mem_univ _, x,hx,hq'⟩
    exact (not_le_of_gt hqp) (min'_le T q hqT)

end FourPapers.Sublattice

end


end

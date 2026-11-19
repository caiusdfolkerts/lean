module
public import Mathlib

/-! Naturality of ordinary rank-selected cohomology. -/

@[expose] public section
namespace PalomarBarycentricTor
theorem natRightCancelAdd : IsRightCancelAdd ℕ := by infer_instance
def naturalUp : ComplexShape ℕ := @ComplexShape.up ℕ _ natRightCancelAdd _
attribute [reducible] naturalUp
attribute [instance 2200] natRightCancelAdd
end PalomarBarycentricTor
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
open scoped BigOperators DirectSum
universe u v w
open Classical Finset MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
namespace CommAlg.Grading
variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
def restrictedBasis (b : Module.Basis I R M) (P : I → Prop) :
    Module.Basis {i // P i} R (Submodule.span R (b '' {i | P i})) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by congr 1; ext x; simp))
end CommAlg.Grading
namespace CommAlg.Simplicial
open CliffordAlgebra
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) := Submodule.span k (basis '' {s | K s ∧ s.card = i})
def Downward (K : Finset V → Prop) : Prop := ∀ ⦃s t⦄, t ⊆ s → K s → K t
abbrev boundary : Ambient V k →ₗ[k] Ambient V k := contractLeft (Q := (0 : QuadraticForm k (V → k))) (Fintype.linearCombination k (fun _ : V => (1 : k)))
lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k} (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by sorry
end CommAlg.Simplicial
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop := ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))
def faceVertices (p : P) : Finset P := univ.filter fun a => IsAtom a ∧ a ≤ p
def faceRank (p : P) : ℕ := (faceVertices p).card
@[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by sorry
theorem faceRank_strictMono (hs : IsSimplicialPoset P) : StrictMono (faceRank : P → ℕ) := by sorry
theorem faceRank_eq_of_orderIso {Q : Type*} [PartialOrder Q] [OrderBot Q] [Fintype Q] (e : P ≃o Q) (p : P) : faceRank (e p) = faceRank p := by sorry
abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}
instance palomarNonzeroFaceFintype : Fintype (NonzeroFace P) := Fintype.ofFinite _
end
section
variable {V C : Type*} [Fintype V] [Fintype C]
structure ProperlyColoredComplex (V C : Type*) where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  color : V → C
  proper : ∀ s, face s → Set.InjOn color (s : Set V)
attribute [class] ProperlyColoredComplex
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
def rankColoredOrderComplex (hs : IsSimplicialPoset P) (d : ℕ)
    (hrank : ∀ p : P, faceRank p ≤ d) :
    ProperlyColoredComplex (NonzeroFace P) (Fin d) where
  face s := ∀ p ∈ s, ∀ q ∈ s, p.val ≤ q.val ∨ q.val ≤ p.val
  downward := by
    intro s t hst ht p hp q hq
    exact ht p (hst hp) q (hst hq)
  color p := ⟨faceRank p.val - 1, by
    have hpos : 0 < faceRank p.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr p.property)
    have hbound := hrank p.val
    omega⟩
  proper s hs' p hp q hq he := by
    have hpos (v : NonzeroFace P) : 0 < faceRank v.val := by
      simpa only [faceRank_bot] using
        (faceRank_strictMono hs) (bot_lt_iff_ne_bot.mpr v.property)
    have hr : faceRank p.val = faceRank q.val := by
      have hh := congrArg Fin.val he
      have hp' := hpos p
      have hq' := hpos q
      dsimp at hh
      omega
    apply Subtype.ext
    rcases hs' p hp q hq with hpq | hqp
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hpq hn))) hr
    · by_contra hn
      exact (Nat.ne_of_lt ((faceRank_strictMono hs) (lt_of_le_of_ne hqp (Ne.symm hn)))) hr.symm
end
open CommAlg
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
def augmentedFaceBoundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Simplicial.Chains (k := K) Λ (i + 1) →ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains Λ (i + 1))).codRestrict _ (fun x => Simplicial.boundary_mem hΛ x.property)
def relativeFaceSubmodule (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Submodule K (Simplicial.Chains (k := K) Λ i) := (Simplicial.Chains Λ₀ i).comap (Simplicial.Chains Λ i).subtype
abbrev RelativeAugmentedChains (Λ Λ₀ : Finset V → Prop) (i : ℕ) := Simplicial.Chains (k := K) Λ i ⧸ relativeFaceSubmodule (K := K) Λ Λ₀ i
def relativeAugmentedBoundary (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) :
    RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1) →ₗ[K] RelativeAugmentedChains (K := K) Λ Λ₀ i :=
  Submodule.mapQ _ _ (augmentedFaceBoundary Λ hΛ i) (by
    intro x hx
    exact Simplicial.boundary_mem hΛ₀ hx)
def relativeAugmentedCoboundary (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K)
  Λ Λ₀ i) →ₗ[K] Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ (i + 1)) := (relativeAugmentedBoundary Λ Λ₀ hΛ hΛ₀ i).dualMap
theorem relativeAugmentedCoboundary_square (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (i : ℕ) : (relativeAugmentedCoboundary (K := K)
  Λ Λ₀ hΛ hΛ₀ (i + 1)).comp (relativeAugmentedCoboundary (K := K) Λ Λ₀ hΛ hΛ₀ i) = 0 := by sorry
def relativeAugmentedCochainComplex (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) : HomologicalComplex (ModuleCat.{max u v} K) PalomarBarycentricTor.naturalUp :=
  CochainComplex.of (fun i => ModuleCat.of K (Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i))) (fun i => ModuleCat.ofHom (relativeAugmentedCoboundary Λ Λ₀ hΛ hΛ₀ i))
  (fun i => ModuleCat.hom_ext (relativeAugmentedCoboundary_square Λ Λ₀ hΛ hΛ₀ i))
def reducedRelativeCohomology (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (q : ℤ) :
    ModuleCat.{max u v} K :=
  if -1 ≤ q then (relativeAugmentedCochainComplex (K := K) Λ Λ₀ hΛ hΛ₀).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
def rankSelection {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Finset V → Prop := fun F => D.face F ∧ F.image D.color ⊆ S
theorem rankSelection_downward {C : Type*} [DecidableEq C] (D : ProperlyColoredComplex V C) (S : Finset C) : Simplicial.Downward (rankSelection D S) := by sorry
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
variable {C : Type*} [LinearOrder C] [DecidableEq C] {V : Type*} [Fintype V] (D : FourPapers.Universal.ProperlyColoredComplex V C)
def colorLinearOrder : LinearOrder V := LinearOrder.lift' (fun v => toLex (D.color v, (Fintype.equivFin V) v)) (by
    intro v w h
    apply (Fintype.equivFin V).injective
    exact congrArg (fun p => (ofLex p).2) h)
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal
section
open CommAlg
variable {K V : Type*} [CommRing K] [Fintype V] [LinearOrder V]
abbrev AugmentedFaceIndex (Λ : Finset V → Prop) (i : ℕ) := {F : Finset V // Λ F ∧ F.card = i}
abbrev RelativeFaceIndex (Λ Λ₀ : Finset V → Prop) (i : ℕ) := {F : Finset V // Λ F ∧ F.card = i ∧ ¬ Λ₀ F}
def augmentedChainBasis (Λ : Finset V → Prop) (i : ℕ) : Module.Basis (AugmentedFaceIndex Λ i) K (Simplicial.Chains (k := K) Λ i) := Grading.restrictedBasis Simplicial.basis
  (fun F => Λ F ∧ F.card = i)
def relativeFaceClass (Λ Λ₀ : Finset V → Prop) (i : ℕ) (F : AugmentedFaceIndex Λ i) : RelativeAugmentedChains (K := K) Λ Λ₀ i := Submodule.Quotient.mk (augmentedChainBasis Λ i
  F)
def relativeCochainCoordinates (Λ Λ₀ : Finset V → Prop) (i : ℕ) :
    Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i) →ₗ[K] (RelativeFaceIndex Λ Λ₀ i → K) where
  toFun f F := f (relativeFaceClass Λ Λ₀ i ⟨F.val, F.property.1, F.property.2.1⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem relativeCochainCoordinates_injective (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Function.Injective (relativeCochainCoordinates (K := K) Λ Λ₀ i) := by sorry
theorem relativeCochainCoordinates_surjective (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Function.Surjective (relativeCochainCoordinates (K := K) Λ Λ₀ i) := by sorry
def relativeCochainCoordinateEquiv (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i) ≃ₗ[K] (RelativeFaceIndex Λ Λ₀ i → K) :=
  LinearEquiv.ofBijective (relativeCochainCoordinates Λ Λ₀ i) ⟨relativeCochainCoordinates_injective Λ Λ₀ i, relativeCochainCoordinates_surjective Λ Λ₀ i⟩
end
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P)
def nonzeroFaceOrderEquiv (e : P ≃o P) : NonzeroFace P ≃ NonzeroFace P where
  toFun p := ⟨e p.val, fun h => p.property (e.injective (h.trans e.map_bot.symm))⟩
  invFun p := ⟨e.symm p.val, fun h => p.property (e.symm.injective (h.trans e.symm.map_bot.symm))⟩
  left_inv p := Subtype.ext (e.symm_apply_apply p.val)
  right_inv p := Subtype.ext (e.apply_symm_apply p.val)
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
structure Subcomplex where
  face : Finset V → Prop
  downward : ∀ ⦃s t : Finset V⦄, s ⊆ t → face t → face s
  subface : ∀ s, face s → D.face s
end FourPapers.Universal.ProperlyColoredComplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
variable {V C K : Type*} [Fintype V] [Fintype C] [CommRing K] (D : FourPapers.Universal.ProperlyColoredComplex V C)
variable {D} (Q : D.Subcomplex)
def toColoredComplex : FourPapers.Universal.ProperlyColoredComplex V C where
  face := Q.face
  downward := Q.downward
  color := D.color
  proper s hs := D.proper s (Q.subface s hs)
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal
section
variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P] (K : Type*) [CommRing K] (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
def rankColoredSubcomplex (Q : Set P) : (rankColoredOrderComplex hs d hrank).Subcomplex where
  face s := (⊥ : P) ∈ Q ∧ (rankColoredOrderComplex hs d hrank).face s ∧ ∀ p ∈ s, p.val ∈ Q
  downward := by
    intro s t hst ht
    exact ⟨ht.1, (rankColoredOrderComplex hs d hrank).downward hst ht.2.1, fun p hp => ht.2.2 p (hst hp)⟩
  subface s hs := hs.2.1
@[simp] theorem rankColoredSubcomplex_empty_face (s : Finset (NonzeroFace P)) :
    ¬ (rankColoredSubcomplex hs d hrank (∅ : Set P)).face s := by sorry
end
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {K V : Type*} [CommRing K] [Fintype V] [LinearOrder V]
def relativeCochainBasis (Λ Λ₀ : Finset V → Prop) (i : ℕ) : Module.Basis (RelativeFaceIndex Λ Λ₀ i) K (Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i)) := (Pi.basisFun
  K (RelativeFaceIndex Λ Λ₀ i)).map (relativeCochainCoordinateEquiv (K := K) Λ Λ₀ i).symm
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
section
open CategoryTheory.Limits CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] (Q : D.Subcomplex) (K)
local instance : DecidableEq C := Classical.decEq C
set_option synthInstance.checkSynthOrder false in
local instance relativeSquarefreeHomologyVertexOrder : LinearOrder V := D.colorLinearOrder
abbrev rankCochainComplex (S : Finset C) : HomologicalComplex (ModuleCat.{u} K) PalomarBarycentricTor.naturalUp := relativeAugmentedCochainComplex (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex
  S) (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S)
end
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable {D : FourPapers.Universal.ProperlyColoredComplex V C} (Q : D.Subcomplex)
structure ColorPairAutomorphism where
  vertex : Equiv.Perm V
  face_iff : ∀ F, D.face (F.image vertex) ↔ D.face F
  subface_iff : ∀ F, Q.face (F.image vertex) ↔ Q.face F
  color_eq : ∀ v, D.color (vertex v) = D.color v
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
section
variable {D : FourPapers.Universal.ProperlyColoredComplex V C} (Q : D.Subcomplex)
variable {Q} (e : Q.ColorPairAutomorphism)
def symm : Q.ColorPairAutomorphism where
  vertex := e.vertex.symm
  face_iff F := by
    have h := e.face_iff (F.image e.vertex.symm)
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id'] using h.symm
  subface_iff F := by
    have h := e.subface_iff (F.image e.vertex.symm)
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id'] using h.symm
  color_eq v := by
    have h := e.color_eq (e.vertex.symm v)
    simpa only [Equiv.apply_symm_apply] using h.symm
end
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] {Q : D.Subcomplex}
variable (e : Q.ColorPairAutomorphism) (K)
section
set_option synthInstance.checkSynthOrder false in
local instance relativeCochainAutomorphismsVertexOrder : LinearOrder V := D.colorLinearOrder
local instance relativeCochainAutomorphismsColorDecidableEq : DecidableEq C := Classical.decEq _
local instance relativeCochainAutomorphismsVertexDecidableEq : DecidableEq V := Classical.decEq _
lemma rankSelection_iff (S : Finset C) (F : Finset V) : rankSelection D S (F.image e.vertex) ↔ rankSelection D S F := by sorry
lemma relativeRankSelection_iff (S : Finset C) (F : Finset V) : rankSelection Q.toColoredComplex S (F.image e.vertex) ↔ rankSelection Q.toColoredComplex S F := by sorry
def cochainIndexEquiv (S : Finset C) (j : ℕ) :
    RelativeFaceIndex (rankSelection D S) (rankSelection Q.toColoredComplex S) j ≃
      RelativeFaceIndex (rankSelection D S) (rankSelection Q.toColoredComplex S) j where
  toFun F := ⟨F.val.image e.vertex, (e.rankSelection_iff S F.val).mpr F.property.1,
    (Finset.card_image_of_injective F.val e.vertex.injective).trans F.property.2.1,
    fun h => F.property.2.2 ((e.relativeRankSelection_iff S F.val).mp h)⟩
  invFun F := ⟨F.val.image e.vertex.symm, (e.symm.rankSelection_iff S F.val).mpr F.property.1,
    (Finset.card_image_of_injective F.val e.vertex.symm.injective).trans F.property.2.1,
    fun h => F.property.2.2 ((e.symm.relativeRankSelection_iff S F.val).mp h)⟩
  left_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply, Finset.image_id, Finset.image_id']
  right_inv F := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id, Finset.image_id']
def cochainEquiv (S : Finset C) (j : ℕ) : (Q.rankCochainComplex K S).X j ≃ₗ[K] (Q.rankCochainComplex K S).X j := (relativeCochainBasis (K := K) (rankSelection D S)
  (rankSelection Q.toColoredComplex S) j).equiv (relativeCochainBasis (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S) j) (e.cochainIndexEquiv S j)
theorem cochainEquiv_differential (S : Finset C) (j : ℕ) (f : (Q.rankCochainComplex K S).X j) : (Q.rankCochainComplex K S).d j (j + 1) (e.cochainEquiv K S j f) =
  e.cochainEquiv K S (j + 1) ((Q.rankCochainComplex K S).d j (j + 1) f) := by sorry
def cochainMap (S : Finset C) : Q.rankCochainComplex K S ⟶ Q.rankCochainComplex K S where
  f j := (e.cochainEquiv K S j).toModuleIso.hom
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact e.cochainEquiv_differential K S i
end
set_option synthInstance.checkSynthOrder false in
local instance relativeSquarefreeNaturalityVertexOrder : LinearOrder V := D.colorLinearOrder
local instance relativeSquarefreeNaturalityColorDecidableEq : DecidableEq C := Classical.decEq _
local instance relativeSquarefreeNaturalityVertexDecidableEq : DecidableEq V := Classical.decEq _
def reducedCohomologyMap (S : Finset C) (q : ℤ) :
    reducedRelativeCohomology (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S)
      (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S) q ⟶
    reducedRelativeCohomology (K := K) (rankSelection D S) (rankSelection Q.toColoredComplex S)
      (rankSelection_downward D S) (rankSelection_downward Q.toColoredComplex S) q := by
  by_cases hq : -1 ≤ q
  · simp only [reducedRelativeCohomology, if_pos hq]
    exact HomologicalComplex.homologyMap (e.cochainMap K S) (q + 1).toNat
  · simp only [reducedRelativeCohomology, if_neg hq]
    exact 𝟙 _
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency.types false
section
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (e : P ≃o P) (hstable : ∀ p, e p ∈ Q ↔ p ∈ Q)
local instance rankColoredNaturalNonzeroDecidableEq : DecidableEq (NonzeroFace P) := Classical.decEq _
lemma rankColored_face_order_iff (F : Finset (NonzeroFace P)) : (rankColoredOrderComplex hs d hrank).face (F.image (nonzeroFaceOrderEquiv e)) ↔ (rankColoredOrderComplex hs d
  hrank).face F := by sorry
def rankColoredPairOrderAut :
    (rankColoredSubcomplex hs d hrank Q).ColorPairAutomorphism where
  vertex := nonzeroFaceOrderEquiv e
  face_iff := rankColored_face_order_iff hs d hrank e
  subface_iff F := by
    constructor
    · rintro ⟨hb, hF, hQ⟩
      refine ⟨hb, (rankColored_face_order_iff hs d hrank e F).mp hF, ?_⟩
      intro p hp
      exact (hstable p.val).mp
        (hQ (nonzeroFaceOrderEquiv e p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    · rintro ⟨hb, hF, hQ⟩
      refine ⟨hb, (rankColored_face_order_iff hs d hrank e F).mpr hF, ?_⟩
      intro p hp
      obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp hp
      rw [← hap]
      exact (hstable a.val).mpr (hQ a ha)
  color_eq p := by
    apply Fin.ext
    change faceRank (e p.val) - 1 = faceRank p.val - 1
    rw [faceRank_eq_of_orderIso]
end
section
open CommAlg
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
variable (Q : Set P) (hQ : ∀ ⦃p q : P⦄, p ≤ q → q ∈ Q → p ∈ Q)
abbrev rankSelectedRelativeCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedRelativeCohomology (K := K)
    (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredSubcomplex hs d hrank Q).toColoredComplex S)
    ((S.card : ℤ) - i - 1)
end
open CommAlg
variable {K : Type u} {V : Type v} [CommRing K] [Fintype V] [LinearOrder V]
theorem relativeFaceSubmodule_eq_bot_of_void (Λ Λ₀ : Finset V → Prop) (hvoid : ∀ F, ¬ Λ₀ F) (i : ℕ) : relativeFaceSubmodule (K := K) Λ Λ₀ i = ⊥ := by sorry
def relativeVoidChainsEquiv (Λ Λ₀ : Finset V → Prop) (hvoid : ∀ F, ¬ Λ₀ F) (i : ℕ) : RelativeAugmentedChains (K := K) Λ Λ₀ i ≃ₗ[K] Simplicial.Chains (k := K) Λ i :=
  (relativeFaceSubmodule (K := K) Λ Λ₀ i).quotEquivOfEqBot (relativeFaceSubmodule_eq_bot_of_void Λ Λ₀ hvoid i)
def augmentedCoboundary (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : Module.Dual K (Simplicial.Chains (k := K) Λ i) →ₗ[K] Module.Dual K (Simplicial.Chains (k
  := K) Λ (i + 1)) := (augmentedFaceBoundary Λ hΛ i).dualMap
theorem augmentedCoboundary_square (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (i : ℕ) : (augmentedCoboundary (K := K) Λ hΛ (i + 1)).comp (augmentedCoboundary (K := K)
  Λ hΛ i) = 0 := by sorry
def augmentedCochainComplex (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) : HomologicalComplex (ModuleCat.{max u v} K) PalomarBarycentricTor.naturalUp := CochainComplex.of (fun i => ModuleCat.of K
  (Module.Dual K (Simplicial.Chains (k := K) Λ i))) (fun i => ModuleCat.ofHom (augmentedCoboundary Λ hΛ i)) (fun i => ModuleCat.hom_ext (augmentedCoboundary_square Λ hΛ i))
@[simp] theorem augmentedCochainComplex_d (Λ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (i : ℕ) :
    (augmentedCochainComplex (K := K) Λ hΛ).d i (i + 1) = ModuleCat.ofHom (augmentedCoboundary Λ hΛ i) := by sorry
def reducedCohomology (Λ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (q : ℤ) :
    ModuleCat.{max u v} K :=
  if -1 ≤ q then (augmentedCochainComplex (K := K) Λ hΛ).homology (q + 1).toNat
  else ModuleCat.of K (ULift.{v} (Fin 0 → K))
def relativeVoidCochainsEquiv (Λ Λ₀ : Finset V → Prop) (hvoid : ∀ F, ¬ Λ₀ F) (i : ℕ) : Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i) ≃ₗ[K] Module.Dual K
  (Simplicial.Chains (k := K) Λ i) := (relativeVoidChainsEquiv Λ Λ₀ hvoid i).symm.dualMap
theorem relativeVoidCochainsEquiv_differential (Λ Λ₀ : Finset V → Prop) (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀) (hvoid : ∀ F, ¬ Λ₀ F) (i : ℕ) (f :
  Module.Dual K (RelativeAugmentedChains (K := K) Λ Λ₀ i)) : augmentedCoboundary Λ hΛ i (relativeVoidCochainsEquiv Λ Λ₀ hvoid i f) = relativeVoidCochainsEquiv Λ Λ₀ hvoid (i +
  1) (relativeAugmentedCoboundary Λ Λ₀ hΛ hΛ₀ i f) := by sorry
def relativeVoidCochainComplexIso (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀)
    (hvoid : ∀ F, ¬ Λ₀ F) :
    relativeAugmentedCochainComplex (K := K) Λ Λ₀ hΛ hΛ₀ ≅ augmentedCochainComplex Λ hΛ := HomologicalComplex.Hom.isoOfComponents
    (fun i => (relativeVoidCochainsEquiv Λ Λ₀ hvoid i).toModuleIso) (by
      intro i j hij
      obtain rfl : j = i + 1 := hij.symm
      simp only [relativeAugmentedCochainComplex, CochainComplex.of_d, augmentedCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact relativeVoidCochainsEquiv_differential Λ Λ₀ hΛ hΛ₀ hvoid i)
def relativeVoidReducedCohomologyIso (Λ Λ₀ : Finset V → Prop)
    (hΛ : Simplicial.Downward Λ) (hΛ₀ : Simplicial.Downward Λ₀)
    (hvoid : ∀ F, ¬ Λ₀ F) (q : ℤ) :
    reducedRelativeCohomology (K := K) Λ Λ₀ hΛ hΛ₀ q ≅ reducedCohomology Λ hΛ q := by
  by_cases hq : -1 ≤ q
  · simpa only [reducedRelativeCohomology, reducedCohomology, if_pos hq] using
      HomologicalComplex.homologyMapIso
        (relativeVoidCochainComplexIso (K := K) Λ Λ₀ hΛ hΛ₀ hvoid) (q + 1).toNat
  · simp only [reducedRelativeCohomology, reducedCohomology, if_neg hq]
    exact Iso.refl _
end FourPapers.Universal
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] {Q : D.Subcomplex}
local instance instDecidableEq_4 : DecidableEq C := Classical.decEq C
set_option synthInstance.checkSynthOrder false in
local instance absoluteCochainsVertexOrder : LinearOrder V := D.colorLinearOrder
local instance instDecidableEq_5 : DecidableEq V := Classical.decEq V
theorem rankSelection_void (hvoid : ∀ F, ¬ Q.face F) (S : Finset C) (F : Finset V) : ¬ rankSelection Q.toColoredComplex S F := by sorry
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex
namespace FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
set_option backward.isDefEq.respectTransparency.types false
open CommAlg
variable {V : Type u} {C : Type} {K : Type u} [Fintype V] [Fintype C] [LinearOrder C] [CommRing K]
variable [D : FourPapers.Universal.ProperlyColoredComplex V C] {Q : D.Subcomplex}
attribute [local instance] instDecidableEq_4
set_option synthInstance.checkSynthOrder false in
attribute [local instance] absoluteCochainsVertexOrder
attribute [local instance] instDecidableEq_5
variable (e : Q.ColorPairAutomorphism) (K)
def absoluteInverseFace (S : Finset C) (i : ℕ)
    (F : AugmentedFaceIndex (rankSelection D S) i) :
    AugmentedFaceIndex (rankSelection D S) i := ⟨F.val.image e.vertex.symm, by
    simpa only [ColorPairAutomorphism.symm] using
      (e.symm.rankSelection_iff S F.val).mpr F.property.1, (Finset.card_image_of_injective F.val e.vertex.symm.injective).trans F.property.2⟩
def absoluteChainPullback (S : Finset C) (i : ℕ) : Module.End K (Simplicial.Chains (k := K) (rankSelection D S) i) := (augmentedChainBasis (K := K) (rankSelection D S)
  i).constr K (fun F => augmentedChainBasis (rankSelection D S) i (e.absoluteInverseFace S i F))
def absoluteCochainTermMap (S : Finset C) (i : ℕ) : Module.End K (Module.Dual K (Simplicial.Chains (k := K) (rankSelection D S) i)) := (e.absoluteChainPullback K S i).dualMap
variable (hvoid : ∀ F, ¬ Q.face F)
section
include hvoid
theorem absoluteCochainTermMap_differential (S : Finset C) (i : ℕ) (f : Module.Dual K (Simplicial.Chains (k := K) (rankSelection D S) i)) : augmentedCoboundary (rankSelection
  D S) (rankSelection_downward D S) i (e.absoluteCochainTermMap K S i f) = e.absoluteCochainTermMap K S (i + 1) (augmentedCoboundary (rankSelection D S)
  (rankSelection_downward D S) i f) := by sorry
end
def absoluteCochainMap (S : Finset C) :
    augmentedCochainComplex (K := K) (rankSelection D S) (rankSelection_downward D S) ⟶
      augmentedCochainComplex (K := K) (rankSelection D S) (rankSelection_downward D S) where
  f i := ModuleCat.ofHom (e.absoluteCochainTermMap K S i)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    simp only [augmentedCochainComplex_d (K := K)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact e.absoluteCochainTermMap_differential K hvoid S i
def absoluteReducedCohomologyMap (S : Finset C) (q : ℤ) :
    reducedCohomology (K := K) (rankSelection D S) (rankSelection_downward D S) q ⟶
      reducedCohomology (K := K) (rankSelection D S) (rankSelection_downward D S) q :=
  if hq : -1 ≤ q then by
    simp only [reducedCohomology, if_pos hq]
    exact HomologicalComplex.homologyMap (e.absoluteCochainMap K hvoid S) (q + 1).toNat
  else by
    simp only [reducedCohomology, if_neg hq]
    exact 𝟙 _
end FourPapers.Universal.ProperlyColoredComplex.Subcomplex.ColorPairAutomorphism
namespace FourPapers.Universal
set_option backward.isDefEq.respectTransparency.types false
variable {P K : Type u} [PartialOrder P] [OrderBot P] [Fintype P] [CommRing K]
variable (K) (hs : IsSimplicialPoset P) (d : ℕ) (hrank : ∀ p : P, faceRank p ≤ d)
abbrev rankSelectedCohomology (S : Finset (Fin d)) (i : ℕ) :=
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  reducedCohomology (K := K) (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    ((S.card : ℤ) - i - 1)
def rankSelectedEmptyRelativeIso (S : Finset (Fin d)) (i : ℕ) :
    rankSelectedRelativeCohomology K hs d hrank (∅ : Set P) S i ≅ rankSelectedCohomology K hs d hrank S i := by
  letI : LinearOrder (NonzeroFace P) := (rankColoredOrderComplex hs d hrank).colorLinearOrder
  letI : DecidableEq (Fin d) := Classical.decEq _
  letI : DecidableEq (NonzeroFace P) := Classical.decEq _
  exact relativeVoidReducedCohomologyIso (K := K)
    (rankSelection (rankColoredOrderComplex hs d hrank) S)
    (rankSelection (rankColoredSubcomplex hs d hrank (∅ : Set P)).toColoredComplex S)
    (rankSelection_downward (rankColoredOrderComplex hs d hrank) S)
    (rankSelection_downward (rankColoredSubcomplex hs d hrank (∅ : Set P)).toColoredComplex S)
    (ProperlyColoredComplex.Subcomplex.rankSelection_void
      (D := rankColoredOrderComplex hs d hrank)
      (Q := rankColoredSubcomplex hs d hrank (∅ : Set P))
      (rankColoredSubcomplex_empty_face hs d hrank) S) ((S.card : ℤ) - i - 1)
def rankSelectedCohomologyAction (e : P ≃o P) (S : Finset (Fin d)) (i : ℕ) :
    rankSelectedCohomology K hs d hrank S i ⟶ rankSelectedCohomology K hs d hrank S i :=
  (rankColoredPairOrderAut hs d hrank (∅ : Set P) e (by simp)).absoluteReducedCohomologyMap (D := rankColoredOrderComplex hs d hrank) K
    (rankColoredSubcomplex_empty_face hs d hrank) S ((S.card : ℤ) - i - 1)
theorem rankSelectedEmptyRelativeIso_natural (e : P ≃o P) (S : Finset (Fin d)) (i : ℕ)
    (x : rankSelectedRelativeCohomology K hs d hrank (∅ : Set P) S i) :
    (rankSelectedEmptyRelativeIso K hs d hrank S i).hom
      ((rankColoredPairOrderAut hs d hrank (∅ : Set P) e (by simp)).reducedCohomologyMap (D := rankColoredOrderComplex hs d hrank) K S
        ((S.card : ℤ) - i - 1) x) = rankSelectedCohomologyAction K hs d hrank e S i
        ((rankSelectedEmptyRelativeIso K hs d hrank S i).hom x) := by sorry
end FourPapers.Universal

module

public import Recovery.Unimodular.WeakFano.Realization
public import Unimodular.FanPatches
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.AllowedBlocks

section General
variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- Independence of the actual prescribed ray vectors in a full allowed block. -/
def Independent (s : FullBlock ι u) : Prop :=
  LinearIndependent ℝ (fun e : {e // e ∈ s.val} => ι (u e.val))

/-- Full blocks have rank equal to the ambient dimension; independence is
therefore precisely the independent rank-n condition in Corollary 4.3. -/
theorem Independent.card_eq {s : FullBlock ι u} (hs : Independent ι u s) :
    s.val.card = Module.finrank ℝ V := by
  have hspan : Submodule.span ℝ
      (Set.range (fun e : {e // e ∈ s.val} => ι (u e.val))) = ⊤ := by
    have he : Set.range (fun e : {e // e ∈ s.val} => ι (u e.val)) =
        (fun e => ι (u e)) '' (s.val : Set E) := by
      ext x
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨e.val, e.property, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩
    rw [he]
    apply top_unique
    calc
      ⊤ = Submodule.span ℝ (blockCone ι u s.val : Set V) := s.property.2.symm
      _ ≤ _ := Submodule.span_le.2 (PointedCone.hull_le_span ℝ _)
  have hc := finrank_span_eq_card hs
  rw [hspan, finrank_top] at hc
  simpa using hc.symm

end General

section Coordinates
variable {n : ℕ} (U : Finset (Lattice n))
  (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
    (fun u : (U : Set (Lattice n)) => u.val))
  (hspan : Submodule.span ℝ (embed '' (U : Set (Lattice n))) = ⊤)
  (hzero : (0 : Lattice n) ∉ U)

local notation "ι₀" => FanBridge.standardEmbedding n
local notation "u₀" => (Subtype.val : {u // u ∈ U} → Lattice n)

include hU hspan

/-- Uniform unimodularity extends every independent allowed block to an
actual integral basis, so its actual toric cone is regular. -/
theorem regular_of_independent (s : FullBlock ι₀ u₀)
    (hs : Independent ι₀ u₀ s) : IsRegularCone ι₀ (blockCone ι₀ u₀ s.val) := by
  let a : {e // e ∈ s.val} → (U : Set (Lattice n)) := fun e => e.val
  obtain ⟨b, hb, hj⟩ := LatticeHull.exists_lattice_basis_extension
    (U : Set (Lattice n)) hU hspan a hs
  choose j hj using hj
  have he : (fun e => ι₀ (u₀ e)) '' (s.val : Set {u // u ∈ U}) =
      (fun i => ι₀ (b i)) '' Set.range j := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨j ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, congrArg (fun v => ι₀ v) (hj ⟨e, he⟩)⟩
    · rintro ⟨i, ⟨e, rfl⟩, rfl⟩
      exact ⟨e.val, e.property, congrArg (fun v => ι₀ v) (hj e).symm⟩
  unfold blockCone
  rw [he]
  simpa only [Set.image_image, Function.comp_def] using
    isRegularCone_hull_image_basis (FanBridge.standardEmbedding_isIntegralLattice n)
      b (Set.range j)

include hzero

/-- For regular blocks, the original ray vectors are precisely their
primitive ray generators, hence linearly independent. -/
theorem independent_of_regular (s : FullBlock ι₀ u₀)
    (hs : IsRegularCone ι₀ (blockCone ι₀ u₀ s.val)) : Independent ι₀ u₀ s := by
  let C := blockCone ι₀ u₀ s.val
  let ρ : {e // e ∈ s.val} → ToricRay C := fun e =>
    ⟨⟨ray (ι₀ (u₀ e.val)),
      ((s.property.1.2.1 _).2 ⟨e.val, e.property, rfl⟩).1⟩,
      ((s.property.1.2.1 _).2 ⟨e.val, e.property, rfl⟩).2⟩
  have hg (e : {e // e ∈ s.val}) : IsPrimitiveGenerator ι₀ (ρ e) e.val.val := by
    apply isPrimitiveGenerator_iff.2
    refine ⟨PointedCone.subset_hull (by simp), ?_⟩
    apply (primitiveLatticeVector_iff_isPrimitive _).1
    exact FlowOrientations.configuration_vector_primitive (U : Set (Lattice n))
      hU hspan e.val.property (fun he => hzero (he ▸ e.val.property))
  have he (e : {e // e ∈ s.val}) : e.val.val =
      primitiveGenerator (FanBridge.standardEmbedding_isIntegralLattice n) hs.toIsToricCone (ρ e) :=
    (hg e).eq_primitiveGenerator _ _
  have hρ : Function.Injective ρ := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    rw [he e, he f, hef]
  have hli := (hs.linearIndependent_primitiveGenerator
    (FanBridge.standardEmbedding_isIntegralLattice n)).comp ρ hρ
  have hf : (fun e : {e // e ∈ s.val} =>
      ι₀ (primitiveGenerator (FanBridge.standardEmbedding_isIntegralLattice n)
        hs.toIsToricCone (ρ e))) = (fun e : {e // e ∈ s.val} => ι₀ (u₀ e.val)) := by
    funext e
    exact congrArg (fun v => ι₀ v) (he e).symm
  change LinearIndependent ℝ (fun e : {e // e ∈ s.val} => ι₀ (u₀ e.val))
  simpa only [Function.comp_def, hf] using hli

theorem regular_iff_independent (s : FullBlock ι₀ u₀) :
    IsRegularCone ι₀ (blockCone ι₀ u₀ s.val) ↔ Independent ι₀ u₀ s :=
  ⟨independent_of_regular U hU hspan hzero s, regular_of_independent U hU hspan s⟩

/-- Deleting every dependent full-block column characterizes exactly the
smooth complete fans, with actual TauCeti regularity on every face. -/
theorem regular_iff_indicator_supported (Φ : FanOnRays ι₀ u₀) :
    Φ.val.IsRegular ↔ ∀ s : FullBlock ι₀ u₀,
      ¬ Independent ι₀ u₀ s → indicator ι₀ u₀ Φ s = 0 := by
  constructor
  · intro hΦ s hs
    apply (indicator_eq_zero_iff ι₀ u₀ Φ s).2
    intro hm
    exact hs ((regular_iff_independent U hU hspan hzero s).1
      ((Fan.isRegular_iff.1 hΦ) _ hm))
  · intro hΦ
    apply Fan.isRegular_iff.2
    intro C hC
    obtain ⟨D, hD, hfull, hCD⟩ := FanMaximalCones.exists_full_supercone Φ.val Φ.property.1 hC
    have hnz : ∀ e : {u // u ∈ U}, ι₀ (u₀ e) ≠ 0 := by
      intro e he
      apply hzero
      have hz : embed (0 : Lattice n) = 0 := by ext i; simp [embed]
      have he' : e.val = 0 := LatticeHull.embed_injective (he.trans hz.symm)
      exact he' ▸ e.property
    obtain ⟨s, hs⟩ := full_fan_cone_eq_block ι₀ u₀ hnz Φ.property.2 hD hfull
    change blockCone ι₀ u₀ s.val = D at hs
    have hi : Independent ι₀ u₀ s := by
      by_contra hn
      have hzero' := hΦ s hn
      have hone : indicator ι₀ u₀ Φ s = 1 :=
        (indicator_eq_one_iff ι₀ u₀ Φ s).2 (by simpa only [hs] using hD)
      omega
    apply IsRegularCone.of_isFaceOf _ hCD
    rw [← hs]
    exact regular_of_independent U hU hspan s hi

end Coordinates
end Unimodular.AllowedBlocks

#print axioms Unimodular.AllowedBlocks.Independent.card_eq
#print axioms Unimodular.AllowedBlocks.regular_iff_independent
#print axioms Unimodular.AllowedBlocks.regular_iff_indicator_supported
#check Unimodular.AllowedBlocks.regular_iff_indicator_supported

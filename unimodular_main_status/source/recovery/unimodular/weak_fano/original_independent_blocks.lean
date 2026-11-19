module

public import Recovery.Unimodular.WeakFano.ArbitraryRealization
public import Recovery.Unimodular.WeakFano.IndependentBlocks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.OriginalSmoothBlocks

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : N →+ V}

/-- Every independent subset extends to a basis of the original integral
lattice. Both the integral and real coordinate maps are explicitly compatible. -/
theorem basis_extension (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hpos : PointedCone.hull ℝ (ι '' U) = ⊤)
    {K : Type*} (a : K → U) (ha : LinearIndependent ℝ (fun j => ι (a j).val)) :
    ∃ B : Module.Basis (Fin n) ℤ N,
      (∀ i, B i ∈ U) ∧ ∀ j, ∃ i, B i = (a j).val := by
  let eN := LatticeCoordinates.latticeEquiv b
  let eR := LatticeCoordinates.realEquiv hι b
  let UC : Set (Lattice n) := eN '' U
  let aC : K → UC := fun j => ⟨eN (a j).val, ⟨(a j).val, (a j).property, rfl⟩⟩
  have hemb : (LatticeCoordinates.coordinateEmbedding n : Lattice n → Ambient n) = embed := by
    ext x i
    rfl
  have hcomm (x : N) : eR (ι x) = embed (eN x) := by
    simpa only [hemb] using LatticeCoordinates.coordinates_commute hι b x
  have hUC : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : UC => u.val) := (LatticeCoordinates.uniform_image_iff b U).2 hU
  have hpC : PointedCone.hull ℝ (embed '' UC) = ⊤ := by
    simpa only [hemb] using (LatticeCoordinates.hull_top_coordinates_iff hι b U).2 hpos
  have hsC : Submodule.span ℝ (embed '' UC) = ⊤ := by
    apply top_unique
    intro x _
    apply PointedCone.hull_le_span ℝ (embed '' UC)
    rw [hpC]
    trivial
  have haC : LinearIndependent ℝ (fun j => embed (aC j).val) := by
    have h := ha.map' eR.toLinearMap (LinearMap.ker_eq_bot.2 eR.injective)
    simpa only [Function.comp_def, LinearEquiv.coe_coe, hcomm] using h
  obtain ⟨BC, hBC, hj⟩ := LatticeHull.exists_lattice_basis_extension UC hUC hsC aC haC
  refine ⟨BC.map eN.symm, ?_, ?_⟩
  · intro i
    obtain ⟨u, hu, he⟩ := hBC i
    change eN.symm (BC i) ∈ U
    rw [← he, eN.symm_apply_apply]
    exact hu
  · intro j
    obtain ⟨i, hi⟩ := hj j
    refine ⟨i, ?_⟩
    change eN.symm (BC i) = (a j).val
    rw [hi]
    exact eN.symm_apply_apply _

/-- Nonzero original ray vectors are primitive in the original lattice. -/
theorem vector_primitive (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hpos : PointedCone.hull ℝ (ι '' U) = ⊤) {x : N} (hx : x ∈ U) (hn : x ≠ 0) :
    TauCeti.IsPrimitive x := by
  let a : Unit → U := fun _ => ⟨x, hx⟩
  have hne : ι x ≠ 0 := fun he => hn (hι.injective (he.trans (map_zero ι).symm))
  have ha : LinearIndependent ℝ (fun j => ι (a j).val) :=
    linearIndependent_unique_iff.2 hne
  obtain ⟨B, hB, hj⟩ := basis_extension hι b U hU hpos a ha
  obtain ⟨i, hi⟩ := hj ()
  change B i = x at hi
  rw [← hi]
  exact B.isPrimitive i

end Unimodular.OriginalSmoothBlocks

namespace Unimodular.AllowedBlocks

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V} (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
  (U : Finset N) (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
  (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U)

local notation "u₀" => (Subtype.val : {u // u ∈ U} → N)
include hι b hU hpos

/-- Independence gives actual regularity in the original lattice. -/
theorem regular_of_independent_original (s : FullBlock ι u₀)
    (hs : Independent ι u₀ s) : IsRegularCone ι (blockCone ι u₀ s.val) := by
  let a : {e // e ∈ s.val} → (U : Set N) := fun e => e.val
  obtain ⟨B, hB, hj⟩ := OriginalSmoothBlocks.basis_extension hι b
    (U : Set N) hU hpos a hs
  choose j hj using hj
  have he : (fun e => ι (u₀ e)) '' (s.val : Set {u // u ∈ U}) =
      (fun i => ι (B i)) '' Set.range j := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨j ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, congrArg ι (hj ⟨e, he⟩)⟩
    · rintro ⟨i, ⟨e, rfl⟩, rfl⟩
      exact ⟨e.val, e.property, congrArg ι (hj e).symm⟩
  unfold blockCone
  rw [he]
  simpa only [Set.image_image, Function.comp_def] using
    isRegularCone_hull_image_basis hι B (Set.range j)

include hzero

/-- Regularity forces independence of the original primitive ray vectors. -/
theorem independent_of_regular_original (s : FullBlock ι u₀)
    (hs : IsRegularCone ι (blockCone ι u₀ s.val)) : Independent ι u₀ s := by
  let C := blockCone ι u₀ s.val
  let ρ : {e // e ∈ s.val} → ToricRay C := fun e =>
    ⟨⟨ray (ι (u₀ e.val)),
      ((s.property.1.2.1 _).2 ⟨e.val, e.property, rfl⟩).1⟩,
      ((s.property.1.2.1 _).2 ⟨e.val, e.property, rfl⟩).2⟩
  have hg (e : {e // e ∈ s.val}) : IsPrimitiveGenerator ι (ρ e) e.val.val := by
    apply isPrimitiveGenerator_iff.2
    refine ⟨PointedCone.subset_hull (by simp), ?_⟩
    exact OriginalSmoothBlocks.vector_primitive hι b (U : Set N) hU hpos
      e.val.property (fun he => hzero (he ▸ e.val.property))
  have he (e : {e // e ∈ s.val}) : e.val.val = primitiveGenerator hι hs.toIsToricCone (ρ e) :=
    (hg e).eq_primitiveGenerator _ _
  have hρ : Function.Injective ρ := by
    intro e f hef
    apply Subtype.ext
    apply Subtype.ext
    rw [he e, he f, hef]
  have hli := (hs.linearIndependent_primitiveGenerator hι).comp ρ hρ
  have hf : (fun e : {e // e ∈ s.val} => ι (primitiveGenerator hι hs.toIsToricCone (ρ e))) =
      (fun e : {e // e ∈ s.val} => ι (u₀ e.val)) := by
    funext e
    exact congrArg ι (he e).symm
  change LinearIndependent ℝ (fun e : {e // e ∈ s.val} => ι (u₀ e.val))
  simpa only [Function.comp_def, hf] using hli

theorem regular_iff_independent_original (s : FullBlock ι u₀) :
    IsRegularCone ι (blockCone ι u₀ s.val) ↔ Independent ι u₀ s :=
  ⟨independent_of_regular_original hι b U hU hpos hzero s,
    regular_of_independent_original hι b U hU hpos s⟩

/-- Deleting the dependent columns characterizes precisely actual smooth
complete fans, in the original lattice and real space and in all dimensions. -/
theorem regular_iff_indicator_supported_original (Φ : FanOnRays ι u₀) :
    Φ.val.IsRegular ↔ ∀ s : FullBlock ι u₀,
      ¬ Independent ι u₀ s → indicator ι u₀ Φ s = 0 := by
  constructor
  · intro hΦ s hs
    apply (indicator_eq_zero_iff ι u₀ Φ s).2
    intro hm
    exact hs ((regular_iff_independent_original hι b U hU hpos hzero s).1
      ((Fan.isRegular_iff.1 hΦ) _ hm))
  · intro hΦ
    apply Fan.isRegular_iff.2
    intro C hC
    obtain ⟨D, hD, hfull, hCD⟩ := FanMaximalCones.exists_full_supercone Φ.val Φ.property.1 hC
    have hnz : ∀ e : {u // u ∈ U}, ι (u₀ e) ≠ 0 := by
      intro e he
      have hz : e.val = 0 := hι.injective (he.trans (map_zero ι).symm)
      exact hzero (hz ▸ e.property)
    obtain ⟨s, hs⟩ := full_fan_cone_eq_block ι u₀ hnz Φ.property.2 hD hfull
    change blockCone ι u₀ s.val = D at hs
    have hi : Independent ι u₀ s := by
      by_contra hn
      have hzero' := hΦ s hn
      have hone : indicator ι u₀ Φ s = 1 :=
        (indicator_eq_one_iff ι u₀ Φ s).2 (by simpa only [hs] using hD)
      omega
    apply IsRegularCone.of_isFaceOf _ hCD
    rw [← hs]
    exact regular_of_independent_original hι b U hU hpos s hi

end Unimodular.AllowedBlocks

#print axioms Unimodular.OriginalSmoothBlocks.basis_extension
#print axioms Unimodular.OriginalSmoothBlocks.vector_primitive
#print axioms Unimodular.AllowedBlocks.regular_iff_independent_original
#print axioms Unimodular.AllowedBlocks.regular_iff_indicator_supported_original
#check Unimodular.AllowedBlocks.regular_iff_indicator_supported_original

module

public import Unimodular.Geometry
public import Unimodular.AllowedBlocks
public import Unimodular.FanMaximalCones
public import Recovery.Unimodular.PriorExtensions.FanEquivCompatibility
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

/-!
# The integral-isomorphism criterion in Theorem 3.4

This file concerns the second paragraph of Theorem 3.4 only.  It does not
assume or prove Seymour's decomposition theorem.  The cones are the actual
cones of finite complete fans, with no regularity, simpliciality, or
projectivity hypothesis.  Chirotopes use the actual primitive ray vectors;
the permitted sign is one global unit of `ℤ`, never independent ray signs.

The final theorem states the full integral-isomorphism criterion. Its
complete transitive proof audit is provided in FanIsomorphismCriterionAudit.
-/

noncomputable section FanIsomorphismCriterionBody
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti TauCeti.Toric
open scoped NNReal

namespace Unimodular.FanIsomorphismCriterion

variable {E E' N N' V V' : Type*}
  [Fintype E] [Fintype E'] [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
  {i : N →+ V} {i' : N' →+ V'}

/-- The exact label set of a full-dimensional cone.  In a complete fan these
are exactly its maximal cones, by `FanMaximalCones.full_iff_maximal`. -/
def MaximalRayBlock (Φ : Fan i) (u : E → N) (s : Finset E) : Prop :=
  ∃ C ∈ Φ.cones, Submodule.span ℝ (C : Set V) = ⊤ ∧
    s = AllowedBlocks.blockOfCone i u C

private theorem map_inverse (e : V ≃ₗ[ℝ] V') (C : PointedCone ℝ V) :
    (C.map (e : V →ₗ[ℝ] V')).map (e.symm : V' →ₗ[ℝ] V) = C := by
  ext x
  simp [PointedCone.mem_map]

private theorem map_inverse_rev (e : V ≃ₗ[ℝ] V') (D : PointedCone ℝ V') :
    (D.map (e.symm : V' →ₗ[ℝ] V)).map (e : V →ₗ[ℝ] V') = D :=
  map_inverse e.symm D

private theorem full_map_iff (e : V ≃ₗ[ℝ] V') (C : PointedCone ℝ V) :
    Submodule.span ℝ (C.map (e : V →ₗ[ℝ] V') : Set V') = ⊤ ↔
      Submodule.span ℝ (C : Set V) = ⊤ := by
  rw [PointedCone.coe_map, Submodule.span_image]
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : e x ∈ (Submodule.span ℝ (C : Set V)).map
        (e : V →ₗ[ℝ] V') := by rw [h]; trivial
    obtain ⟨y, hy, hxy⟩ := hx
    exact e.injective hxy ▸ hy
  · intro h
    rw [h, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective

private theorem map_ray (e : V ≃ₗ[ℝ] V') (x : V) :
    (AllowedBlocks.ray x).map (e : V →ₗ[ℝ] V') =
      AllowedBlocks.ray (e x) := by
  change Submodule.map ((e : V →ₗ[ℝ] V').restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 {x}) = Submodule.span ℝ≥0 {e x}
  rw [Submodule.map_span, Set.image_singleton]
  rfl

private theorem blockOfCone_map (u : E → N) (v : E' → N')
    (e : V ≃ₗ[ℝ] V') (f : E ≃ E')
    (h : ∀ a, e (i (u a)) = i' (v (f a))) (C : PointedCone ℝ V) :
    AllowedBlocks.blockOfCone i' v (C.map (e : V →ₗ[ℝ] V')) =
      (AllowedBlocks.blockOfCone i u C).map f.toEmbedding := by
  classical
  ext a'
  obtain ⟨a, rfl⟩ := f.surjective a'
  rw [AllowedBlocks.mem_blockOfCone]
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hxe : x = i (u a) := e.injective (hxa.trans (h a).symm)
    refine Finset.mem_map.mpr ⟨a, ?_, rfl⟩
    exact (AllowedBlocks.mem_blockOfCone i u C a).mpr (hxe ▸ hx)
  · intro ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_map.mp ha
    have hba' : b = a := f.injective hba
    subst b
    exact ⟨i (u a), (AllowedBlocks.mem_blockOfCone i u C a).mp hb, h a⟩

private theorem blockCone_map (u : E → N) (v : E' → N')
    (e : V ≃ₗ[ℝ] V') (f : E ≃ E')
    (h : ∀ a, e (i (u a)) = i' (v (f a))) (s : Finset E) :
    (AllowedBlocks.blockCone i u s).map (e : V →ₗ[ℝ] V') =
      AllowedBlocks.blockCone i' v (s.map f.toEmbedding) := by
  classical
  change Submodule.map ((e : V →ₗ[ℝ] V').restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 ((fun a => i (u a)) '' (s : Set E))) =
      Submodule.span ℝ≥0 ((fun a => i' (v a)) '' (s.map f.toEmbedding : Set E'))
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, (h a).symm⟩
  · rintro ⟨a', ha', rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ha'
    exact ⟨i (u a), ⟨a, ha, rfl⟩, h a⟩

/-- An actual fan equivalence transports the entire maximal-cone family,
with its exact primitive-ray labels. -/
theorem maximalRayBlock_iff_of_fanEquiv (Φ : Fan i) (Ψ : Fan i')
    (u : E → N) (v : E' → N') (g : FanEquiv Φ Ψ) (f : E ≃ E')
    (h : ∀ a, g.latticeEquiv (u a) = v (f a)) (s : Finset E) :
    MaximalRayBlock Φ u s ↔ MaximalRayBlock Ψ v (s.map f.toEmbedding) := by
  classical
  have hreal (a) : g.realEquiv (i (u a)) = i' (v (f a)) := by
    rw [g.map_lattice, h]
  constructor
  · rintro ⟨C, hC, hfull, rfl⟩
    refine ⟨C.map (g.realEquiv : V →ₗ[ℝ] V'), (g.map_mem C).mpr hC,
      (full_map_iff g.realEquiv C).mpr hfull, ?_⟩
    exact (blockOfCone_map u v g.realEquiv f hreal C).symm
  · rintro ⟨D, hD, hfull, hs⟩
    let C := D.map (g.realEquiv.symm : V' →ₗ[ℝ] V)
    refine ⟨C, ?_,
      (full_map_iff g.realEquiv.symm D).mpr hfull, ?_⟩
    · simpa only [C, FanEquiv.symm_realEquiv] using (g.symm.map_mem D).mpr hD
    apply Finset.map_injective f.toEmbedding
    rw [← blockOfCone_map u v g.realEquiv f hreal C]
    simpa only [C, map_inverse_rev] using hs

private theorem maps_cones_of_maximal_blocks (Φ : Fan i) (Ψ : Fan i')
    (u : E → N) (v : E' → N')
    (hΦ : Φ.IsComplete) (hrΦ : AllowedBlocks.HasRays i u Φ)
    (hrΨ : AllowedBlocks.HasRays i' v Ψ)
    (hnz : ∀ a, i (u a) ≠ 0) (hnz' : ∀ a, i' (v a) ≠ 0)
    (e : V ≃ₗ[ℝ] V') (f : E ≃ E')
    (h : ∀ a, e (i (u a)) = i' (v (f a)))
    (hmax : ∀ s, MaximalRayBlock Φ u s →
      MaximalRayBlock Ψ v (s.map f.toEmbedding))
    {C : PointedCone ℝ V} (hC : C ∈ Φ.cones) :
    C.map (e : V →ₗ[ℝ] V') ∈ Ψ.cones := by
  obtain ⟨D, hD, hfull, hCD⟩ :=
    FanMaximalCones.exists_full_supercone Φ hΦ hC
  obtain ⟨D', hD', _, hlabels⟩ :=
    hmax (AllowedBlocks.blockOfCone i u D) ⟨D, hD, hfull, rfl⟩
  have hsource := (AllowedBlocks.fan_cone_allowed i u hnz hrΦ hD).2
  have htarget := (AllowedBlocks.fan_cone_allowed i' v hnz' hrΨ hD').2
  have hmap : D.map (e : V →ₗ[ℝ] V') = D' := by
    rw [← hsource, blockCone_map u v e f h, hlabels, htarget]
  exact Ψ.mem_of_isFaceOf hD' (hmap ▸ hCD.map_equiv e)

/-- An integral lattice equivalence extends to the actual ambient real spaces.
The inverse identities follow from uniqueness of scalar extension. -/
def realExtension (Φ : Fan i) (Ψ : Fan i') (φ : N ≃ₗ[ℤ] N') : V ≃ₗ[ℝ] V' :=
  LinearEquiv.ofLinearMap
    (Φ.lattice.extend i' φ.toLinearMap.toAddMonoidHom)
    (Ψ.lattice.extend i φ.symm.toLinearMap.toAddMonoidHom)
    (by
      apply Ψ.lattice.isBaseChange.algHom_ext
      intro x
      simp)
    (by
      apply Φ.lattice.isBaseChange.algHom_ext
      intro x
      simp)

@[simp] theorem realExtension_apply (Φ : Fan i) (Ψ : Fan i')
    (φ : N ≃ₗ[ℤ] N') (x : N) : realExtension Φ Ψ φ (i x) = i' (φ x) :=
  Φ.lattice.extend_apply i' φ.toLinearMap.toAddMonoidHom x

/-- Preserving the primitive rays and maximal blocks suffices to preserve all
actual cones and faces.  No choice of triangulation is involved. -/
def fanEquivOfMaximalBlocks (Φ : Fan i) (Ψ : Fan i')
    (u : E → N) (v : E' → N')
    (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete)
    (hrΦ : AllowedBlocks.HasRays i u Φ) (hrΨ : AllowedBlocks.HasRays i' v Ψ)
    (hnz : ∀ a, i (u a) ≠ 0) (hnz' : ∀ a, i' (v a) ≠ 0)
    (φ : N ≃ₗ[ℤ] N') (f : E ≃ E')
    (h : ∀ a, φ (u a) = v (f a))
    (hmax : ∀ s, MaximalRayBlock Φ u s ↔
      MaximalRayBlock Ψ v (s.map f.toEmbedding)) : FanEquiv Φ Ψ where
  latticeEquiv := φ.toAddEquiv
  realEquiv := realExtension Φ Ψ φ
  map_lattice := realExtension_apply Φ Ψ φ
  map_mem C := by
    classical
    let e := realExtension Φ Ψ φ
    have hreal (a) : e (i (u a)) = i' (v (f a)) := by
      rw [realExtension_apply, h]
    constructor
    · intro hC
      have hinverse (a') : e.symm (i' (v a')) = i (u (f.symm a')) := by
        apply e.injective
        simp only [LinearEquiv.apply_symm_apply, hreal, Equiv.apply_symm_apply]
      have hback (t) : MaximalRayBlock Ψ v t →
          MaximalRayBlock Φ u (t.map f.symm.toEmbedding) := by
        intro ht
        apply (hmax _).mpr
        have he : f.symm.toEmbedding.trans f.toEmbedding = Function.Embedding.refl E' := by
          ext a
          exact f.apply_symm_apply a
        simpa only [Finset.map_map, he, Finset.map_refl] using ht
      have := maps_cones_of_maximal_blocks Ψ Φ v u hΨ hrΨ hrΦ hnz' hnz
        e.symm f.symm hinverse hback hC
      change (C.map (e : V →ₗ[ℝ] V')).map (e.symm : V' →ₗ[ℝ] V) ∈ Φ.cones at this
      simpa only [map_inverse] using this
    · exact maps_cones_of_maximal_blocks Φ Ψ u v hΦ hrΦ hrΨ hnz hnz'
        e f hreal (fun s => (hmax s).mp)

private theorem exists_image_label (Φ : Fan i) (Ψ : Fan i')
    (u : E → N) (v : E' → N')
    (hrΦ : AllowedBlocks.HasRays i u Φ) (hrΨ : AllowedBlocks.HasRays i' v Ψ)
    (hu : ∀ a, IsPrimitive (u a)) (hv : ∀ a, IsPrimitive (v a))
    (g : FanEquiv Φ Ψ) (a : E) : ∃ a', g.latticeEquiv (u a) = v a' := by
  let C := AllowedBlocks.ray (i (u a))
  have hC := (hrΦ C).mpr ⟨a, rfl⟩
  let D := C.map (g.realEquiv : V →ₗ[ℝ] V')
  have hD : D ∈ Ψ.cones := (g.map_mem C).mpr hC.1
  have hdim : Module.finrank ℝ (Submodule.span ℝ (D : Set V')) = 1 := by
    dsimp only [D]
    rw [PointedCone.coe_map, Submodule.span_image, g.realEquiv.finrank_map_eq]
    exact hC.2
  obtain ⟨a', ha'⟩ := (hrΨ D).mp ⟨hD, hdim⟩
  let ρ : ToricRay D := ⟨⟨D, PointedCone.IsFaceOf.refl D⟩, hdim⟩
  have hfirst : IsPrimitiveGenerator i' ρ (g.latticeEquiv (u a)) := by
    refine isPrimitiveGenerator_iff.mpr
      ⟨?_, (g.latticeEquiv.toIntLinearEquiv.isPrimitive_iff).mpr (hu a)⟩
    change i' (g.latticeEquiv (u a)) ∈ D
    rw [← g.map_lattice]
    exact ⟨i (u a), PointedCone.subset_hull (by simp), rfl⟩
  have hsecond : IsPrimitiveGenerator i' ρ (v a') := by
    refine isPrimitiveGenerator_iff.mpr ⟨?_, hv a'⟩
    change i' (v a') ∈ D
    rw [ha']
    exact PointedCone.subset_hull (by simp)
  exact ⟨a', hfirst.unique Ψ.lattice (Ψ.isToricCone hD).salient hsecond⟩

/-- Primitive, unrepeated ray labels are transported bijectively by every
integral fan isomorphism. -/
theorem exists_label_equiv (Φ : Fan i) (Ψ : Fan i')
    (u : E → N) (v : E' → N')
    (hrΦ : AllowedBlocks.HasRays i u Φ) (hrΨ : AllowedBlocks.HasRays i' v Ψ)
    (hu : ∀ a, IsPrimitive (u a)) (hv : ∀ a, IsPrimitive (v a))
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (g : FanEquiv Φ Ψ) :
    ∃ f : E ≃ E', ∀ a, g.latticeEquiv (u a) = v (f a) := by
  choose f hf using exists_image_label Φ Ψ u v hrΦ hrΨ hu hv g
  have hfi : Function.Injective f := by
    intro a b hab
    apply huinj
    apply g.latticeEquiv.injective
    rw [hf, hf, hab]
  have hfs : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := exists_image_label Ψ Φ v u hrΨ hrΦ hv hu g.symm b
    have ha' : g.latticeEquiv.symm (v b) = u a := by
      simpa only [FanEquiv.symm_latticeEquiv] using ha
    refine ⟨a, hvinj ?_⟩
    rw [← hf, ← ha']
    exact g.latticeEquiv.apply_symm_apply (v b)
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf⟩

/-- Completeness supplies full ray rank, including the zero-dimensional case. -/
theorem ray_span_eq_top (Φ : Fan i) (u : E → N)
    (hΦ : Φ.IsComplete) (hrΦ : AllowedBlocks.HasRays i u Φ)
    (hnz : ∀ a, i (u a) ≠ 0) :
    Submodule.span ℝ (Set.range (fun a => i (u a))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨C, hC, hx⟩ := Φ.isComplete_iff.mp hΦ x
  have hgen := (AllowedBlocks.fan_cone_allowed i u hnz hrΦ hC).2
  rw [← hgen] at hx
  apply Submodule.span_mono (show
    (fun a => i (u a)) '' (AllowedBlocks.blockOfCone i u C : Set E) ⊆
      Set.range (fun a => i (u a)) from Set.image_subset_range _ _)
  exact PointedCone.hull_le_span ℝ _ hx

theorem exists_full_ray_determinant {I : Type*} [Fintype I] [DecidableEq I]
    (Φ : Fan i) (b : Module.Basis I ℤ N) (u : E → N)
    (hΦ : Φ.IsComplete) (hrΦ : AllowedBlocks.HasRays i u Φ)
    (hnz : ∀ a, i (u a) ≠ 0) :
    ∃ a : I → E, b.det (u ∘ a) ≠ 0 := by
  let hs := ray_span_eq_top Φ u hΦ hrΦ hnz
  let c := Module.Basis.ofSpan hs.ge
  let e := (Φ.lattice.isBaseChange.basis b).indexEquiv c
  have hc (j : I) : c (e j) ∈ Set.range (fun a => i (u a)) :=
    Module.Basis.ofSpan_subset hs.ge ⟨e j, rfl⟩
  choose a ha using hc
  have hli : LinearIndependent ℝ (fun j => i (u (a j))) := by
    have hfun : (fun j => i (u (a j))) = c ∘ e := funext ha
    rw [hfun]
    exact c.linearIndependent.comp e e.injective
  refine ⟨a, (IntegralRigidity.independent_iff_det_ne_zero b (u ∘ a)).mp ?_⟩
  exact LinearIndependent.of_comp i.toIntLinearMap (hli.restrict_scalars' ℤ)

/-- The second paragraph of Theorem 3.4 for arbitrary primitive ray labels.
The index equivalence expresses equality of ranks, not an extra hypothesis.
Only one global chirotope sign is allowed. -/
theorem fan_equiv_iff_oriented_maximal_blocks
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Fan i) (Ψ : Fan i') (b : Module.Basis I ℤ N) (b' : Module.Basis J ℤ N')
    (u : E → N) (v : E' → N')
    (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete)
    (hrΦ : AllowedBlocks.HasRays i u Φ) (hrΨ : AllowedBlocks.HasRays i' v Ψ)
    (hu : ∀ a, IsPrimitive (u a)) (hv : ∀ a, IsPrimitive (v a))
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hU : IntegralRigidity.Uniform b u) (hV : IntegralRigidity.Uniform b' v) :
    Nonempty (FanEquiv Φ Ψ) ↔
      ∃ (r : I ≃ J) (f : E ≃ E') (ε : ℤˣ),
        (∀ a : I → E, ((b'.reindex r.symm).det ((v ∘ f) ∘ a)).sign =
          (ε : ℤ) * (b.det (u ∘ a)).sign) ∧
        ∀ s, MaximalRayBlock Φ u s ↔ MaximalRayBlock Ψ v (s.map f.toEmbedding) := by
  classical
  constructor
  · rintro ⟨g⟩
    obtain ⟨f, hf⟩ := exists_label_equiv Φ Ψ u v hrΦ hrΨ hu hv huinj hvinj g
    let r : I ≃ J := (b.map g.latticeEquiv.toIntLinearEquiv).indexEquiv b'
    obtain ⟨ε, hε⟩ := IntegralRigidity.chirotope_of_lattice_equiv b
      (b'.reindex r.symm) u (v ∘ f) g.latticeEquiv.toIntLinearEquiv hf
    exact ⟨r, f, ε, hε, maximalRayBlock_iff_of_fanEquiv Φ Ψ u v g f hf⟩
  · rintro ⟨r, f, ε, hε, hmax⟩
    have hnz (a) : i (u a) ≠ 0 := by
      simpa only [map_zero] using Φ.lattice.injective.ne (hu a).ne_zero
    have hnz' (a) : i' (v a) ≠ 0 := by
      simpa only [map_zero] using Ψ.lattice.injective.ne (hv a).ne_zero
    have hV' : IntegralRigidity.Uniform (b'.reindex r.symm) (v ∘ f) := by
      intro a
      rw [Module.Basis.det_reindex]
      simpa only [Function.comp_def] using hV (fun j => f (a (r.symm j)))
    obtain ⟨φ, hφ, _⟩ := IntegralRigidity.exists_unique_lattice_equiv_of_chirotope
      b (b'.reindex r.symm) u (v ∘ f) hU hV'
      (exists_full_ray_determinant Φ b u hΦ hrΦ hnz) ε hε
    exact ⟨fanEquivOfMaximalBlocks Φ Ψ u v hΦ hΨ hrΦ hrΨ hnz hnz' φ f hφ hmax⟩

/-! The intrinsic labels below remove all externally supplied ray-family data. -/

/-- The literal one-dimensional cones of a fan. -/
abbrev RayIndex (Φ : Fan i) :=
  {R : Φ.cones // Module.finrank ℝ (Submodule.span ℝ (R.val : Set V)) = 1}

instance rayIndexFinite (Φ : Fan i) : Finite (RayIndex Φ) := inferInstance

noncomputable instance rayIndexFintype (Φ : Fan i) : Fintype (RayIndex Φ) :=
  Fintype.ofFinite _

def selfRay (Φ : Fan i) (R : RayIndex Φ) : ToricRay R.val.val :=
  ⟨⟨R.val.val, PointedCone.IsFaceOf.refl _⟩, R.property⟩

/-- The primitive integral vector on each actual ray. -/
def rayVector (Φ : Fan i) (R : RayIndex Φ) : N :=
  primitiveGenerator Φ.lattice (Φ.isToricCone R.val.property) (selfRay Φ R)

theorem rayVector_primitive (Φ : Fan i) (R : RayIndex Φ) :
    IsPrimitive (rayVector Φ R) :=
  primitiveGenerator_isPrimitive Φ.lattice (Φ.isToricCone R.val.property) (selfRay Φ R)

theorem rayVector_hull (Φ : Fan i) (R : RayIndex Φ) :
    R.val.val = AllowedBlocks.ray (i (rayVector Φ R)) := by
  exact (selfRay Φ R).eq_hull_singleton (Φ.isToricCone R.val.property).salient
    (primitiveGenerator_mem Φ.lattice (Φ.isToricCone R.val.property) (selfRay Φ R))
    (by simpa only [map_zero] using Φ.lattice.injective.ne (rayVector_primitive Φ R).ne_zero)

theorem rayVector_injective (Φ : Fan i) : Function.Injective (rayVector Φ) := by
  intro R S h
  apply Subtype.ext
  apply Subtype.ext
  rw [rayVector_hull Φ R, rayVector_hull Φ S, h]

theorem rayVector_hasRays (Φ : Fan i) : AllowedBlocks.HasRays i (rayVector Φ) Φ := by
  intro R
  constructor
  · rintro ⟨hR, hdim⟩
    exact ⟨⟨⟨R, hR⟩, hdim⟩, rayVector_hull Φ ⟨⟨R, hR⟩, hdim⟩⟩
  · rintro ⟨ρ, rfl⟩
    rw [← rayVector_hull Φ ρ]
    exact ⟨ρ.val.property, ρ.property⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- Intrinsic complete-fan form of the integral-isomorphism criterion in
Theorem 3.4.  Maximal blocks refer to the actual primitive-ray labels above;
the left side is the usual integral equivalence of every cone of the fans. -/
theorem theorem_3_4_isomorphism_criterion
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (Φ : Fan i) (Ψ : Fan i') (b : Module.Basis I ℤ N) (b' : Module.Basis J ℤ N')
    (hΦ : Φ.IsComplete) (hΨ : Ψ.IsComplete)
    (hU : IntegralRigidity.Uniform b (rayVector Φ))
    (hV : IntegralRigidity.Uniform b' (rayVector Ψ)) :
    Nonempty (FanEquiv Φ Ψ) ↔
      ∃ (r : I ≃ J) (f : RayIndex Φ ≃ RayIndex Ψ) (ε : ℤˣ),
        (∀ a : I → RayIndex Φ,
          ((b'.reindex r.symm).det ((rayVector Ψ ∘ f) ∘ a)).sign =
            (ε : ℤ) * (b.det (rayVector Φ ∘ a)).sign) ∧
        ∀ s, MaximalRayBlock Φ (rayVector Φ) s ↔
          MaximalRayBlock Ψ (rayVector Ψ) (s.map f.toEmbedding) := by
  letI : FiniteDimensional ℝ V := Φ.lattice.finiteDimensional
  letI : FiniteDimensional ℝ V' := Ψ.lattice.finiteDimensional
  exact fan_equiv_iff_oriented_maximal_blocks Φ Ψ b b' (rayVector Φ) (rayVector Ψ)
    hΦ hΨ (rayVector_hasRays Φ) (rayVector_hasRays Ψ)
    (rayVector_primitive Φ) (rayVector_primitive Ψ)
    (rayVector_injective Φ) (rayVector_injective Ψ) hU hV

end Unimodular.FanIsomorphismCriterion

end FanIsomorphismCriterionBody

#print axioms Unimodular.FanIsomorphismCriterion.fan_equiv_iff_oriented_maximal_blocks
#print axioms Unimodular.FanIsomorphismCriterion.theorem_3_4_isomorphism_criterion
#check "UNIMODULAR_FAN_ISOMORPHISM_CRITERION_EOF"

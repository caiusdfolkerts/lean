module

public import Continuation.Runtime.HellerRecoveredNative
public import Recovery.Unimodular.PriorExtensions.FlowLattice
public import Recovery.Unimodular.PriorExtensions.FanEquivCompatibility
public import Recovery.Unimodular.NativePort.A3Geometry
public import Unimodular.FanRayTransport

/-! The historically checked arbitrary-rank type-A classification, using
its already ported geometry bodies and the actual Heller equality theorem.
The original Heller source and all retained body hashes are recorded in
`audit/theorem-7-1-composition`. This aggregate still needs a current-pin pass. -/

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false











namespace Unimodular.TypeAFanGeometry

variable {n : ℕ}

/-- The root presentation used by the fan constructions is carried to the
paper's literal zero-sum lattice by the checked integral coordinate equivalence. -/
theorem rootSet_lattice_image :
    Heller.TypeA.coordinateEquiv n '' rootSet n = Heller.TypeA.roots n := by
  ext u
  constructor
  · rintro ⟨v,⟨e,rfl⟩,rfl⟩
    refine ⟨Heller.TypeA.vertexIndex e.val.1,Heller.TypeA.vertexIndex e.val.2,
      fun he => e.property (Heller.TypeA.vertexIndex_bijective.1 he),?_⟩
    exact Heller.TypeA.coordinateEquiv_difference e.val.1 e.val.2
  · rintro ⟨i,j,hij,rfl⟩
    obtain ⟨p,rfl⟩ := Heller.TypeA.vertexIndex_bijective.2 i
    obtain ⟨q,rfl⟩ := Heller.TypeA.vertexIndex_bijective.2 j
    have hpq : p ≠ q := fun he => hij (congrArg Heller.TypeA.vertexIndex he)
    exact ⟨latticeRoot p q,⟨⟨(p,q),hpq⟩,rfl⟩,
      Heller.TypeA.coordinateEquiv_difference p q⟩


end Unimodular.TypeAFanGeometry

section Recovered71_FanTransport

noncomputable section

open TauCeti.Toric

namespace Unimodular.FanTransport

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {ι : N →+ V} {ι' : N' →+ W}

/-- An integral lattice equivalence extends uniquely to an equivalence of the
actual ambient real vector spaces. Its inverse is the extension of the inverse
integral equivalence. -/
def extendEquiv (hi : IsIntegralLattice ι) (hi' : IsIntegralLattice ι')
    (q : N ≃+ N') : V ≃ₗ[ℝ] W :=
  LinearEquiv.ofLinear (hi.extend ι' q) (hi'.extend ι q.symm)
    (by
      calc
        (hi.extend ι' q).comp (hi'.extend ι q.symm) =
            hi'.extend ι' (AddMonoidHom.id N') := hi'.eq_extend (by intro n; simp)
        _ = LinearMap.id := hi'.extend_id)
    (by
      calc
        (hi'.extend ι q.symm).comp (hi.extend ι' q) =
            hi.extend ι (AddMonoidHom.id N) := hi.eq_extend (by intro n; simp)
        _ = LinearMap.id := hi.extend_id)

@[simp] theorem extendEquiv_lattice (hi : IsIntegralLattice ι)
    (hi' : IsIntegralLattice ι') (q : N ≃+ N') (u : N) :
    extendEquiv hi hi' q (ι u) = ι' (q u) := hi.extend_apply ι' q u

/-- Actual cone images under an ambient equivalence form an equivalence of cone
sets. No fan incidence or face condition is imposed as an extra assumption. -/
def coneEquiv (p : V ≃ₗ[ℝ] W) : PointedCone ℝ V ≃ PointedCone ℝ W where
  toFun C := C.map p.toLinearMap
  invFun D := D.map p.symm.toLinearMap
  left_inv C := by
    dsimp only
    rw [PointedCone.map_map]
    have hc : p.symm.toLinearMap.comp p.toLinearMap = LinearMap.id := by ext x; simp
    rw [hc,PointedCone.map_id]
  right_inv D := by
    dsimp only
    rw [PointedCone.map_map]
    have hc : p.toLinearMap.comp p.symm.toLinearMap = LinearMap.id := by ext x; simp
    rw [hc,PointedCone.map_id]

theorem finrank_map (p : V ≃ₗ[ℝ] W) (C : PointedCone ℝ V) :
    Module.finrank ℝ (Submodule.span ℝ (C.map p.toLinearMap : Set W)) =
      Module.finrank ℝ (Submodule.span ℝ (C : Set V)) := by
  rw [PointedCone.coe_map,Submodule.span_image,p.finrank_map_eq]

theorem map_ray_via_hull (p : V ≃ₗ[ℝ] W) (v : V) :
    (AllowedBlocks.ray v).map p.toLinearMap = AllowedBlocks.ray (p v) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,ha,rfl⟩ := PointedCone.mem_hull_singleton.1 hx
    exact PointedCone.mem_hull_singleton.2 ⟨a,ha,by simp⟩
  · intro y hy
    obtain ⟨a,ha,rfl⟩ := PointedCone.mem_hull_singleton.1 hy
    exact ⟨a • v,PointedCone.mem_hull_singleton.2 ⟨a,ha,rfl⟩,by simp⟩

variable (Φ : Fan ι) (hΦ : Φ.IsComplete) (q : N ≃+ N')
    (p : V ≃ₗ[ℝ] W) (hcompat : ∀ u, p (ι u) = ι' (q u))
    (hi' : IsIntegralLattice ι')

theorem mapFan_ker_eq_span_bot :
    LinearMap.ker p.toLinearMap = Submodule.span ℝ ((⊥ : PointedCone ℝ V) : Set V) := by
  rw [LinearMap.ker_eq_bot.mpr p.injective]
  simp

theorem mapFan_bot_mem (hΦ : Φ.IsComplete) : (⊥ : PointedCone ℝ V) ∈ Φ.cones := by
  obtain ⟨C,hC,_⟩ := Φ.isComplete_iff.1 hΦ 0
  exact Φ.bot_mem hC

/-- The image of every cone of a complete fan under compatible integral and
real equivalences. It is obtained from the already proved quotient-star
construction at the zero face, so rationality and all fan axioms are proved. -/
def mapFan : Fan ι' :=
  StarQuotients.starFan (p := p.toLinearMap) (hker := mapFan_ker_eq_span_bot p)
    (Φ := Φ) (q := q.toAddMonoidHom) (hq := hcompat) (hι' := hi')
    (F := ⊥) (hF := mapFan_bot_mem Φ hΦ)

@[simp] theorem mem_mapFan (C : PointedCone ℝ V) :
    C.map p.toLinearMap ∈ (mapFan Φ hΦ q p hcompat hi').cones ↔ C ∈ Φ.cones := by
  change (coneEquiv p C) ∈ (mapFan Φ hΦ q p hcompat hi').cones ↔ C ∈ Φ.cones
  rw [mapFan,StarQuotients.mem_starFan_cones]
  constructor
  · rintro ⟨D,hD,_,hDC⟩
    exact (coneEquiv p).injective hDC ▸ hD
  · intro hC
    exact ⟨C,hC,bot_le,rfl⟩

/-- The coordinate change is an actual fan equivalence, with both the original
lattice and the real ambient space recorded. -/
def mapFanEquiv : FanEquiv Φ (mapFan Φ hΦ q p hcompat hi') where
  latticeEquiv := q
  realEquiv := p
  map_lattice := hcompat
  map_mem := mem_mapFan Φ hΦ q p hcompat hi'

/-- Completeness and actual regularity are preserved by the coordinate change. -/
theorem mapFan_complete : (mapFan Φ hΦ q p hcompat hi').IsComplete :=
  (mapFanEquiv Φ hΦ q p hcompat hi').isComplete_iff.2 hΦ

theorem mapFan_regular_iff : (mapFan Φ hΦ q p hcompat hi').IsRegular ↔ Φ.IsRegular :=
  (mapFanEquiv Φ hΦ q p hcompat hi').isRegular_iff

end Unimodular.FanTransport

namespace Unimodular.AllowedBlocks

variable {N N' V W E : Type*} [AddCommGroup N] [AddCommGroup N']
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {ι : N →+ V} {ι' : N' →+ W}

/-- Exact prescribed ray sets transport under actual fan equivalences. This
works for arbitrary complete or incomplete, smooth or singular fans. -/
theorem HasRays.transport {Φ : Fan ι} {Ψ : Fan ι'} (e : FanEquiv Φ Ψ)
    (u : E → N) (hr : HasRays ι u Φ) :
    HasRays ι' (fun a => e.latticeEquiv (u a)) Ψ := by
  intro R
  let C := R.map e.realEquiv.symm.toLinearMap
  have hC : C.map e.realEquiv.toLinearMap = R := by
    dsimp only [C]
    rw [PointedCone.map_map]
    have hh : e.realEquiv.toLinearMap.comp e.realEquiv.symm.toLinearMap = LinearMap.id := by
      ext x; simp
    rw [hh,PointedCone.map_id]
  have hd (K : PointedCone ℝ V) :
      Module.finrank ℝ (Submodule.span ℝ (K.map e.realEquiv.toLinearMap : Set W)) =
        Module.finrank ℝ (Submodule.span ℝ (K : Set V)) := by
    rw [PointedCone.coe_map,Submodule.span_image,e.realEquiv.finrank_map_eq]
  have hmapray (v : V) : (ray v).map e.realEquiv.toLinearMap = ray (e.realEquiv v) := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨a,ha,rfl⟩ := PointedCone.mem_hull_singleton.1 hx
      exact PointedCone.mem_hull_singleton.2 ⟨a,ha,by simp⟩
    · intro y hy
      obtain ⟨a,ha,rfl⟩ := PointedCone.mem_hull_singleton.1 hy
      exact ⟨a • v,PointedCone.mem_hull_singleton.2 ⟨a,ha,rfl⟩,by simp⟩
  constructor
  · rintro ⟨hR,hRdim⟩
    have hc : C ∈ Φ.cones := (e.map_mem C).1 (hC.symm ▸ hR)
    have hdim : Module.finrank ℝ (Submodule.span ℝ (C : Set V)) = 1 := by
      rw [← hd C,hC]
      exact hRdim
    obtain ⟨a,ha⟩ := (hr C).1 ⟨hc,hdim⟩
    refine ⟨a,?_⟩
    rw [← hC,ha,hmapray,e.map_lattice]
  · rintro ⟨a,rfl⟩
    obtain ⟨ha,hdim⟩ := (hr (ray (ι (u a)))).2 ⟨a,rfl⟩
    have hm := (e.map_mem (ray (ι (u a)))).2 ha
    have hd' := hd (ray (ι (u a)))
    rw [hmapray,e.map_lattice] at hm hd'
    exact ⟨hm,hd'.trans hdim⟩

end Unimodular.AllowedBlocks

end

end Recovered71_FanTransport

section Recovered71_TypeAClassification

noncomputable section

open TauCeti.Toric

namespace Unimodular.TypeAFanGeometry

/-- The geometric equality classification on the original arbitrary integral
lattice. The supplied coordinate change is a genuine fan equivalence. Its image
is exactly the fan obtained by coning compatible subdivisions of the actual
root-polytope facets, and regularity is equivalent to genuine triangulation.

The coordinate classification itself is the bijection `fanSubdivisionEquiv`;
this theorem proves its applicability to every extremal fan of Theorem 7.1. -/
theorem extremal_fan_classification {n : ℕ} (hn : 0 < n) {N V : Type*}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : N →+ V}
    (b : Module.Basis (Fin n) ℤ N) (S : Finset N)
    (Φ : Fan ι) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays ι (fun u : (S : Set N) => u.val) Φ)
    (hU : IntegralRigidity.Uniform b (fun u : (S : Set N) => u.val))
    (hzero : 0 ∉ S) (hcard : S.card = n * (n + 1)) :
    ∃ (ψ : N ≃ₗ[ℤ] Heller.TypeA.RootLattice n)
      (Γ : Fan (FanBridge.standardEmbedding n)) (e : FanEquiv Φ Γ)
      (D : CompatibleCutSubdivisions n),
      ψ '' (S : Set N) = Heller.TypeA.roots n ∧
      (∀ u, e.latticeEquiv u = (Heller.TypeA.coordinateEquiv n).symm (ψ u)) ∧
      Γ = D.toFan ∧
      (Φ.IsRegular ↔ ∀ T : ProperCut n, (D.subdivision T).IsTriangulation) := by
  classical
  obtain ⟨ψ,hψ⟩ := (Heller.theorem_7_1_bound_and_equality_general b S Φ hcomplete
    hrays hU hzero).2.1 hcard
  let q : N ≃ₗ[ℤ] Lattice n := ψ.trans (Heller.TypeA.coordinateEquiv n).symm
  have hqS : q '' (S : Set N) = rootSet n := by
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      have hm : Heller.TypeA.coordinateEquiv n (q u) ∈ Heller.TypeA.roots n := by
        rw [← hψ]
        exact ⟨u,hu,by simp [q]⟩
      rw [← rootSet_lattice_image] at hm
      obtain ⟨z,hz,he⟩ := hm
      exact (Heller.TypeA.coordinateEquiv n).injective he ▸ hz
    · intro hw
      have hm : Heller.TypeA.coordinateEquiv n w ∈ Heller.TypeA.roots n := by
        rw [← rootSet_lattice_image]
        exact ⟨w,hw,rfl⟩
      rw [← hψ] at hm
      obtain ⟨u,hu,he⟩ := hm
      refine ⟨u,hu,?_⟩
      apply (Heller.TypeA.coordinateEquiv n).injective
      simpa [q] using he
  let hi := FanBridge.standardEmbedding_isIntegralLattice n
  let p := FanTransport.extendEquiv Φ.lattice hi q.toAddEquiv
  have hcompat : ∀ u, p (ι u) = FanBridge.standardEmbedding n (q u) := by
    intro u
    exact FanTransport.extendEquiv_lattice Φ.lattice hi q.toAddEquiv u
  let Γ := FanTransport.mapFan Φ hcomplete q.toAddEquiv p hcompat hi
  let e : FanEquiv Φ Γ := FanTransport.mapFanEquiv Φ hcomplete q.toAddEquiv p hcompat hi
  have hΓ := FanTransport.mapFan_complete Φ hcomplete q.toAddEquiv p hcompat hi
  have htransport := AllowedBlocks.HasRays.transport e (fun u : (S : Set N) => u.val) hrays
  have hr : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Γ := by
    intro R
    rw [htransport R]
    constructor
    · rintro ⟨u,hu⟩
      have hm : q u.val ∈ rootSet n := hqS ▸ ⟨u.val,u.property,rfl⟩
      obtain ⟨a,ha⟩ := hm
      refine ⟨a,?_⟩
      change R = AllowedBlocks.ray (FanBridge.standardEmbedding n (q u.val)) at hu
      simpa only [ha] using hu
    · rintro ⟨a,ha⟩
      have hm : rootFamily n a ∈ rootSet n := ⟨a,rfl⟩
      rw [← hqS] at hm
      obtain ⟨u,hu,he⟩ := hm
      refine ⟨⟨u,hu⟩,?_⟩
      change R = AllowedBlocks.ray (FanBridge.standardEmbedding n (q u))
      rw [he]
      exact ha
  let D := fanCutSubdivisions Γ hΓ hr
  refine ⟨ψ,Γ,e,D,hψ,?_,?_,?_⟩
  · intro u
    rfl
  · exact (toFan_fanCutSubdivisions hn Γ hΓ hr).symm
  · exact e.isRegular_iff.symm.trans (fan_isRegular_iff_cut_triangulations hn Γ hΓ hr)

#print axioms extremal_fan_classification

end Unimodular.TypeAFanGeometry

end

end Recovered71_TypeAClassification

section Recovered71_ActualFanTheorems

noncomputable section

open TauCeti.Toric

namespace Unimodular.ActualFanTheorems

variable {N V : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι)

/-- All actual primitive rays of every finite rational fan form a finite set.
Neither regularity nor completeness is needed. -/
theorem primitive_rays_finite : {u : N | ConeBases.IsRay Φ u}.Finite := by
  classical
  letI : Fintype Φ.cones := Φ.finite_cones.fintype
  letI (C : Φ.cones) : Finite (ToricRay C.val) :=
    ToricRay.finite_of_fg (Φ.isToricCone C.property).fg
  let g : (Σ C : Φ.cones, ToricRay C.val) → N := fun r =>
    primitiveGenerator Φ.lattice (Φ.isToricCone r.1.property) r.2
  have he : {u : N | ConeBases.IsRay Φ u} = Set.range g := by
    ext u
    constructor
    · rintro ⟨C,hC,ρ,hu⟩
      exact ⟨⟨⟨C,hC⟩,ρ⟩,(hu.eq_primitiveGenerator Φ.lattice (Φ.isToricCone hC)).symm⟩
    · rintro ⟨⟨C,ρ⟩,rfl⟩
      exact ⟨C.val,C.property,ρ,
        isPrimitiveGenerator_primitiveGenerator Φ.lattice (Φ.isToricCone C.property) ρ⟩
  rw [he]
  exact Set.finite_range g

/-- The actual primitive-vector predicate agrees with the exact intrinsic
one-dimensional cones of the fan, including their orientations. -/
theorem primitive_rays_hasRays :
    AllowedBlocks.HasRays ι (fun u : {u : N | ConeBases.IsRay Φ u} => u.val) Φ := by
  intro R
  constructor
  · rintro ⟨hR,hd⟩
    let ρ : ToricRay R := ⟨⟨R,PointedCone.IsFaceOf.refl R⟩,hd⟩
    let u := primitiveGenerator Φ.lattice (Φ.isToricCone hR) ρ
    have hu : IsPrimitiveGenerator ι ρ u :=
      isPrimitiveGenerator_primitiveGenerator Φ.lattice (Φ.isToricCone hR) ρ
    refine ⟨⟨u,⟨R,hR,ρ,hu⟩⟩,?_⟩
    exact ρ.eq_hull_singleton (Φ.isToricCone hR).salient hu.mem
      (by simpa using Φ.lattice.injective.ne hu.ne_zero)
  · rintro ⟨u,rfl⟩
    obtain ⟨C,hC,ρ,hu⟩ := u.property
    have he : ρ.toPointedCone = AllowedBlocks.ray (ι u.val) :=
      ρ.eq_hull_singleton ((Φ.isToricCone hC).salient.anti ρ.val.isFaceOf.le)
        hu.mem (by simpa using Φ.lattice.injective.ne hu.ne_zero)
    constructor
    · rw [← he]
      exact Φ.mem_of_isFaceOf hC ρ.val.isFaceOf
    · rw [← he]
      exact ρ.property

/-- The actual primitive ray set excludes zero, by primitive-generator
nonvanishing, not by a separate hypothesis on a supplied list. -/
theorem zero_not_primitive_rays : (0 : N) ∉ {u : N | ConeBases.IsRay Φ u} := by
  rintro ⟨C,hC,ρ,hu⟩
  exact hu.ne_zero rfl

/-- The bound and integral equality classification of Theorem 7.1 directly on
the original fan's actual primitive-ray set. Finiteness, spanning, and the exact
ray-list identification are all derived; they are not input assumptions. -/
theorem theorem_7_1_bound_and_equality {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (hcomplete : Φ.IsComplete)
    (hU : IntegralRigidity.Uniform b
      (fun u : {u : N | ConeBases.IsRay Φ u} => u.val)) :
    Set.ncard {u : N | ConeBases.IsRay Φ u} ≤ n * (n + 1) ∧
      (Set.ncard {u : N | ConeBases.IsRay Φ u} = n * (n + 1) ↔
        ∃ ψ : N ≃ₗ[ℤ] Heller.TypeA.RootLattice n,
          ψ '' {u : N | ConeBases.IsRay Φ u} = Heller.TypeA.roots n) := by
  classical
  let S := (primitive_rays_finite Φ).toFinset
  have hS : (S : Set N) = {u : N | ConeBases.IsRay Φ u} := by simp [S]
  have hmem (u : N) : u ∈ (S : Set N) ↔ ConeBases.IsRay Φ u := by
    rw [hS]
    rfl
  have hr : AllowedBlocks.HasRays ι (fun u : (S : Set N) => u.val) Φ := by
    intro R
    constructor
    · intro hR
      obtain ⟨u,hu⟩ := (primitive_rays_hasRays Φ R).1 hR
      exact ⟨⟨u.val,(hmem u.val).2 u.property⟩,hu⟩
    · rintro ⟨u,hu⟩
      exact (primitive_rays_hasRays Φ R).2
        ⟨⟨u.val,(hmem u.val).1 u.property⟩,hu⟩
  have hu : IntegralRigidity.Uniform b (fun u : (S : Set N) => u.val) := by
    intro a
    exact hU (fun j => ⟨(a j).val,(hmem (a j).val).1 (a j).property⟩)
  have hz : (0 : N) ∉ S := by
    change (0 : N) ∉ (S : Set N)
    rw [hS]
    exact zero_not_primitive_rays Φ
  have h := Heller.theorem_7_1_bound_and_equality_general b S Φ hcomplete hr hu hz
  rw [← hS,Set.ncard_coe_finset]
  exact h

/-- The full fan/subdivision and smoothness classification applies directly to
an arbitrary extremal complete fan on its original lattice and actual rays. -/
theorem theorem_7_1_geometric_equality {n : ℕ} (hn : 0 < n)
    (b : Module.Basis (Fin n) ℤ N) (hcomplete : Φ.IsComplete)
    (hU : IntegralRigidity.Uniform b
      (fun u : {u : N | ConeBases.IsRay Φ u} => u.val))
    (hcard : Set.ncard {u : N | ConeBases.IsRay Φ u} = n * (n + 1)) :
    ∃ (ψ : N ≃ₗ[ℤ] Heller.TypeA.RootLattice n)
      (Γ : Fan (FanBridge.standardEmbedding n)) (e : FanEquiv Φ Γ)
      (D : TypeAFanGeometry.CompatibleCutSubdivisions n),
      ψ '' {u : N | ConeBases.IsRay Φ u} = Heller.TypeA.roots n ∧
      (∀ u, e.latticeEquiv u = (Heller.TypeA.coordinateEquiv n).symm (ψ u)) ∧
      Γ = D.toFan ∧
      (Φ.IsRegular ↔ ∀ T : TypeAFanGeometry.ProperCut n,
        (D.subdivision T).IsTriangulation) := by
  classical
  let S := (primitive_rays_finite Φ).toFinset
  have hS : (S : Set N) = {u : N | ConeBases.IsRay Φ u} := by simp [S]
  have hmem (u : N) : u ∈ (S : Set N) ↔ ConeBases.IsRay Φ u := by
    rw [hS]
    rfl
  have hr : AllowedBlocks.HasRays ι (fun u : (S : Set N) => u.val) Φ := by
    intro R
    constructor
    · intro hR
      obtain ⟨u,hu⟩ := (primitive_rays_hasRays Φ R).1 hR
      exact ⟨⟨u.val,(hmem u.val).2 u.property⟩,hu⟩
    · rintro ⟨u,hu⟩
      exact (primitive_rays_hasRays Φ R).2
        ⟨⟨u.val,(hmem u.val).1 u.property⟩,hu⟩
  have hu : IntegralRigidity.Uniform b (fun u : (S : Set N) => u.val) := by
    intro a
    exact hU (fun j => ⟨(a j).val,(hmem (a j).val).1 (a j).property⟩)
  have hz : (0 : N) ∉ S := by
    change (0 : N) ∉ (S : Set N)
    rw [hS]
    exact zero_not_primitive_rays Φ
  have hc : S.card = n * (n + 1) := by
    simpa only [← hS,Set.ncard_coe_finset] using hcard
  simpa only [hS] using TypeAFanGeometry.extremal_fan_classification
    hn b S Φ hcomplete hr hu hz hc

#print axioms theorem_7_1_bound_and_equality
#print axioms theorem_7_1_geometric_equality

end Unimodular.ActualFanTheorems

end

end Recovered71_ActualFanTheorems


module

public import Recovery.Unimodular.NativePort.A3Projectivity

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual integer dual points and lattice normal polytopes.
All input rays, cones, and strict support inequalities are geometric. -/

/- Exact current draft body: A3IntegralProjectivity. -/
section Projectivity_A3IntegralProjectivity



/-! UNVERIFIED. Integral ray heights on a full root cone give an integral
actual dual functional: the roots in that cone contain a proved integral
basis. Thus the normal polytope constructed for the A3 sign criterion can
be chosen to be a lattice polytope, including for nonsimplicial fans. -/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.IntegralNormalPolytopes

open TypeAFanGeometry NormalFanSupport StrictSupportNormalFan LocalSupportGluing
open TauCeti.Toric

variable {n : ℕ}

/-- Membership in the actual dual lattice, expressed by integer evaluation
on every point of the original lattice. -/
def IsIntegralDual (p : Module.Dual ℝ (Ambient n)) : Prop :=
  ∀ x : Lattice n, ∃ z : ℤ, p (embed x) = (z : ℝ)

/-- A finite lattice polytope, with equality of every one of its normal
cones and every cone of the given fan. -/
def HasLatticePolytopeNormalFan (Φ : Fan (FanBridge.standardEmbedding n)) : Prop :=
  ∃ s : Finset (Module.Dual ℝ (Ambient n)),
    (∀ p ∈ s, IsIntegralDual p) ∧
    ∀ D : PointedCone ℝ (Ambient n), D ∈ Φ.cones ↔
      ∃ q ∈ convexHull ℝ (s : Set (Module.Dual ℝ (Ambient n))),
        D = normalCone (convexHull ℝ (s : Set (Module.Dual ℝ (Ambient n)))) q

theorem HasLatticePolytopeNormalFan.to_real
    {Φ : Fan (FanBridge.standardEmbedding n)} (h : HasLatticePolytopeNormalFan Φ) :
    HasPolytopeNormalFan Φ := by
  obtain ⟨s,hint,hfan⟩ := h
  exact ⟨s,hfan⟩

/-- No regularity assumption is needed: uniform unimodularity supplies
an integral basis inside every full cone, even a nonsimplicial one. -/
theorem full_cone_integral_basis (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (C : FullCone Φ) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      ∀ i, b i ∈ rootSet n ∧ embed (b i) ∈ C.val.val := by
  let U : Set (Lattice n) := {v | v ∈ rootSet n ∧ embed v ∈ C.val.val}
  have hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : U => v.val) := by
    intro a
    exact rootSet_uniform (fun j => (⟨(a j).val,(a j).property.1⟩ : rootSet n))
  have hset : embed '' U = coneRootSet C.val.val := by
    ext x
    constructor
    · rintro ⟨v,⟨⟨e,rfl⟩,hv⟩,rfl⟩
      exact ⟨e,hv,rfl⟩
    · rintro ⟨e,he,rfl⟩
      exact ⟨rootFamily n e,⟨⟨e,rfl⟩,he⟩,rfl⟩
  have hspan : Submodule.span ℝ (embed '' U) = ⊤ := by
    apply top_unique
    rw [← C.property]
    apply Submodule.span_le.mpr
    rw [hset]
    intro x hx
    rw [fan_cone_eq_hull_roots Φ hrays C.val.property] at hx
    exact PointedCone.hull_le_span ℝ _ hx
  obtain ⟨b,hb,hba⟩ := LatticeHull.exists_lattice_basis_extension U hU hspan
    (fun j : Fin 0 => Fin.elim0 j) (linearIndependent_empty_type)
  exact ⟨b,hb⟩

/-- Every support point forced by integer heights belongs to the dual
lattice. The proof checks evaluation on arbitrary lattice vectors. -/
theorem strict_point_integral (Φ : Fan (FanBridge.standardEmbedding n))
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (d : StrictSupportData Φ rootRay) (H : Edge n → ℤ)
    (hH : ∀ e, d.height e = (H e : ℝ)) (C : FullCone Φ) : IsIntegralDual (d.point C) := by
  classical
  obtain ⟨b,hb⟩ := full_cone_integral_basis Φ hrays C
  have hex : ∀ i, ∃ e : Edge n, rootFamily n e = b i := fun i => (hb i).1
  choose e he using hex
  have hpoint (i : Fin n) : d.point C (embed (b i)) = (H (e i) : ℝ) := by
    rw [← he i]
    have hmem : rootRay (e i) ∈ C.val.val := by
      change embed (rootFamily n (e i)) ∈ C.val.val
      rw [he i]
      exact (hb i).2
    exact (d.on_ray C (e i) hmem).trans (hH (e i))
  intro x
  refine ⟨∑ i, b.repr x i * H (e i),?_⟩
  calc
    d.point C (embed x) =
        d.point C (∑ i, realCoordinates b (embed x) i • embed (b i)) :=
      congrArg (d.point C) (sum_basis_realCoordinates b (embed x)).symm
    _ = ∑ i, realCoordinates b (embed x) i * d.point C (embed (b i)) := by
      rw [map_sum]
      simp only [map_smul,smul_eq_mul]
    _ = ((∑ i, b.repr x i * H (e i) : ℤ) : ℝ) := by
      simp only [realCoordinates_embed,hpoint,Int.cast_sum,Int.cast_mul]

/-- The same exact normal-polytope construction now records that every
chosen vertex lies in the actual dual lattice. -/
theorem lattice_normalFan_of_strict_integer_heights
    (Φ : Fan (FanBridge.standardEmbedding n)) (hcomplete : Φ.IsComplete)
    (hrays : AllowedBlocks.HasRays (FanBridge.standardEmbedding n) (rootFamily n) Φ)
    (d : StrictSupportData Φ rootRay) (H : Edge n → ℤ)
    (hH : ∀ e, d.height e = (H e : ℝ)) : HasLatticePolytopeNormalFan Φ := by
  classical
  letI : Fintype (FullCone Φ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image d.point,?_,?_⟩
  · intro p hp
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hp
    exact strict_point_integral Φ hrays d H hH C
  · intro D
    have hnormal := normalCone_eq_full Φ rootRay d hcomplete
      (fun C hC => fan_cone_eq_hull_roots Φ hrays hC)
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using
      cones_iff_normalCone_of_full Φ hcomplete d.point hnormal D

end Unimodular.IntegralNormalPolytopes

namespace Unimodular.A3IntegralProjectivity

open A3RegularFanCount A3CanonicalSigns A3SupportForms A3SignPatterns A3LocalSupports
open A3ProjectiveNecessity A3ProjectiveCounts LocalSupportGluing
open IntegralNormalPolytopes NormalFanSupport

/-- Every admissible pattern has an actual lattice-polytope realization,
not merely a real support function. -/
theorem lattice_normalFan_of_admissible (Φ : CompleteRootFan)
    (ha : Admissible (normalizedSignEquiv Φ)) : HasLatticePolytopeNormalFan Φ.val := by
  obtain ⟨h,hh⟩ := (exists_integral_heights_with_sign_iff (a3SignEquiv Φ)).mpr ha
  obtain ⟨d⟩ := localSupportData_exists Φ (edgeHeight (fun e => (h e : ℝ)))
    (prescribedSigns_of_forms Φ _ hh)
  obtain ⟨N,hN,s,hs⟩ := exists_strictSupportData d
  apply lattice_normalFan_of_strict_integer_heights Φ.val Φ.property.1 Φ.property.2 s
    (fun e => h (edgeEquiv.symm e) + (N : ℤ))
  intro e
  rw [hs]
  simp only [edgeHeight,Int.cast_add,Int.cast_natCast]

theorem normalFan_iff_lattice_normalFan (Φ : CompleteRootFan) :
    HasPolytopeNormalFan Φ.val ↔ HasLatticePolytopeNormalFan Φ.val := by
  exact ⟨fun h => lattice_normalFan_of_admissible Φ ((normalFan_iff_admissible Φ).mp h),
    HasLatticePolytopeNormalFan.to_real⟩

def latticeProjectiveFanEquiv :
    {Φ : CompleteRootFan // HasLatticePolytopeNormalFan Φ.val} ≃
      {Φ : CompleteRootFan // HasPolytopeNormalFan Φ.val} :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun Φ => (normalFan_iff_lattice_normalFan Φ).symm)

/-- The count remains 603 with literal lattice vertices required. -/
theorem a3_lattice_projective_fan_count :
    Nat.card {Φ : CompleteRootFan // HasLatticePolytopeNormalFan Φ.val} = 603 := by
  rw [Nat.card_congr latticeProjectiveFanEquiv]
  exact a3_projective_fan_count

#print axioms IntegralNormalPolytopes.full_cone_integral_basis
#print axioms IntegralNormalPolytopes.strict_point_integral
#print axioms IntegralNormalPolytopes.lattice_normalFan_of_strict_integer_heights
#print axioms lattice_normalFan_of_admissible
#print axioms normalFan_iff_lattice_normalFan
#print axioms a3_lattice_projective_fan_count

end Unimodular.A3IntegralProjectivity
end

end Projectivity_A3IntegralProjectivity

#check "UNIMODULAR_A3_INTEGRAL_PROJECTIVITY_EOF_V1"

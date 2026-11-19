module

public import Unimodular.MainFanTheorems

@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.AllowedBlocks

attribute [local instance] Classical.propDecidable

variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- Stack the paper's complete facet boundary matrix and its generic-direction row. -/
noncomputable def equationMap (w : V) :
    (FullBlock ι u → ℤ) →+ ((FacetBlock ι u → ℤ) × ℤ) where
  toFun c := (fun b => ∑ s, boundary ι u b s * c s, ∑ s, degreeRow ι u w s * c s)
  map_zero' := by
    apply Prod.ext
    · funext b
      simp
    · simp
  map_add' c d := by
    apply Prod.ext
    · funext b
      simp [mul_add, Finset.sum_add_distrib]
    · simp [mul_add, Finset.sum_add_distrib]

theorem equationMap_eq_target_iff (w : V) (c : FullBlock ι u → ℤ) :
    equationMap ι u w c = (0, 1) ↔
      BoundaryCycle ι u c ∧ (∑ s, degreeRow ι u w s * c s) = 1 := by
  constructor
  · intro h
    exact ⟨fun b => congrFun (congrArg Prod.fst h) b, congrArg Prod.snd h⟩
  · rintro ⟨hb, hd⟩
    apply Prod.ext
    · exact funext hb
    · exact hd

def IsSolution (w : V) (c : FullBlock ι u → ℤ) : Prop :=
  (∀ s, 0 ≤ c s) ∧ BoundaryCycle ι u c ∧ (∑ s, degreeRow ι u w s * c s) = 1

theorem isSolution_iff (w : V) (c : FullBlock ι u → ℤ) :
    IsSolution ι u w c ↔ (∀ s, 0 ≤ c s) ∧ equationMap ι u w c = (0, 1) := by
  rw [equationMap_eq_target_iff]
  rfl

/-- Genuine complete fans with exactly the given ray configuration. -/
def FanOnRays := {Φ : Fan ι // Φ.IsComplete ∧ HasRays ι u Φ}

noncomputable def indicator (Φ : FanOnRays ι u) : FullBlock ι u → ℤ :=
  fun s => if blockCone ι u s.1 ∈ Φ.1.cones then 1 else 0

@[simp] theorem indicator_eq_one_iff (Φ : FanOnRays ι u) (s : FullBlock ι u) :
    indicator ι u Φ s = 1 ↔ blockCone ι u s.1 ∈ Φ.1.cones := by simp [indicator]

@[simp] theorem indicator_eq_zero_iff (Φ : FanOnRays ι u) (s : FullBlock ι u) :
    indicator ι u Φ s = 0 ↔ blockCone ι u s.1 ∉ Φ.1.cones := by simp [indicator]

theorem indicator_injective (hnz : ∀ e, ι (u e) ≠ 0) :
    Function.Injective (indicator ι u) := by
  intro Φ Ψ he
  have hsubset : ∀ (A B : FanOnRays ι u), indicator ι u A = indicator ι u B →
      A.1.cones ⊆ B.1.cones := by
    intro A B h C hC
    obtain ⟨D, hD, hfull, hCD⟩ := FanMaximalCones.exists_full_supercone A.1 A.2.1 hC
    obtain ⟨s, hs⟩ := full_fan_cone_eq_block ι u hnz A.2.2 hD hfull
    change blockCone ι u s.1 = D at hs
    have hsa : indicator ι u A s = 1 :=
      (indicator_eq_one_iff ι u A s).2 (by rw [hs]; exact hD)
    have hsb : indicator ι u B s = 1 := by rw [← h]; exact hsa
    have hDB : D ∈ B.1.cones := by
      rw [← hs]
      exact (indicator_eq_one_iff ι u B s).1 hsb
    exact B.1.mem_of_isFaceOf hDB hCD
  apply Subtype.ext
  exact Fan.ext (Set.Subset.antisymm (hsubset Φ Ψ he) (hsubset Ψ Φ he.symm))

theorem indicator_isSolution (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (Φ : FanOnRays ι u) : IsSolution ι u w (indicator ι u Φ) :=
  (theorem_3_1 ι u hι hnz hpos (indicator ι u Φ) hw).2 ⟨Φ.1, Φ.2.1, Φ.2.2, fun _ => rfl⟩

noncomputable def realization (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (c : FullBlock ι u → ℤ) (hc : IsSolution ι u w c) : FanOnRays ι u :=
  let h := (theorem_3_1 ι u hι hnz hpos c hw).1 hc
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩

theorem indicator_realization (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (c : FullBlock ι u → ℤ) (hc : IsSolution ι u w c) :
    indicator ι u (realization ι u hι hnz hpos hw c hc) = c := by
  funext s
  exact ((theorem_3_1 ι u hι hnz hpos c hw).1 hc).choose_spec.2.2 s |>.symm

/-- Every maximal cone is drawn from one of the two endpoint fans. -/
def UsesEndpointCones (Φ Ψ Θ : FanOnRays ι u) : Prop :=
  ∀ C ∈ Θ.1.cones, Submodule.span ℝ (C : Set V) = ⊤ → C ∈ Φ.1.cones ∨ C ∈ Ψ.1.cones

theorem usesEndpointCones_of_between (hnz : ∀ e, ι (u e) ≠ 0)
    (Φ Ψ Θ : FanOnRays ι u)
    (hb : Graver.Between (indicator ι u Φ) (indicator ι u Ψ) (indicator ι u Θ)) :
    UsesEndpointCones ι u Φ Ψ Θ := by
  intro C hC hfull
  obtain ⟨s, hs⟩ := full_fan_cone_eq_block ι u hnz Θ.2.2 hC hfull
  change blockCone ι u s.1 = C at hs
  by_contra hn
  push_neg at hn
  have hΦ : indicator ι u Φ s = 0 :=
    (indicator_eq_zero_iff ι u Φ s).2 (by simpa only [hs] using hn.1)
  have hΨ : indicator ι u Ψ s = 0 :=
    (indicator_eq_zero_iff ι u Ψ s).2 (by simpa only [hs] using hn.2)
  have hΘ : indicator ι u Θ s = 1 :=
    (indicator_eq_one_iff ι u Θ s).2 (by simpa only [hs] using hC)
  have hz := hb.coordinate_zero hΦ hΨ
  omega

/-- The connectivity assertion of Theorem 1.1. The vertices of this path are actual
complete fans with exactly the prescribed rays, its moves are precisely Graver-primitive
integer relations for the paper's full equation matrix, and all intermediate maximal
cones belong to the two endpoint fans. -/
theorem theorem_1_1_connectivity (hι : IsIntegralLattice ι) (hnz : ∀ e, ι (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => ι (u e))) = ⊤)
    {w : V} (hw : RayHyperplanes.GenericDirection (fun e => ι (u e)) w)
    (Φ Ψ : FanOnRays ι u) :
    ∃ G : Finset (FullBlock ι u → ℤ),
      (∀ g, g ∈ G ↔ Graver.Primitive (equationMap ι u w).ker g) ∧
      Relation.ReflTransGen
        (fun A B : FanOnRays ι u =>
          indicator ι u B - indicator ι u A ∈ G ∧
          UsesEndpointCones ι u Φ Ψ A ∧ UsesEndpointCones ι u Φ Ψ B) Φ Ψ := by
  classical
  let c := indicator ι u Φ
  let d := indicator ι u Ψ
  have hc := (isSolution_iff ι u w c).1 (indicator_isSolution ι u hι hnz hpos hw Φ)
  have hd := (isSolution_iff ι u w d).1 (indicator_isSolution ι u hι hnz hpos hw Ψ)
  have hcd : equationMap ι u w c = equationMap ι u w d := hc.2.trans hd.2.symm
  obtain ⟨G, hG, hpath⟩ := Graver.finite_nonnegative_fiber_connectivity
    (equationMap ι u w) c d hcd hc.1 hd.1
  let realize : (FullBlock ι u → ℤ) → FanOnRays ι u := fun a =>
    if ha : IsSolution ι u w a then realization ι u hι hnz hpos hw a ha else Φ
  have hrealize : ∀ a, IsSolution ι u w a → indicator ι u (realize a) = a := by
    intro a ha
    simp only [realize, dif_pos ha]
    exact indicator_realization ι u hι hnz hpos hw a ha
  have hstart : realize c = Φ := by
    apply indicator_injective ι u hnz
    exact hrealize c ((isSolution_iff ι u w c).2 hc)
  have hend : realize d = Ψ := by
    apply indicator_injective ι u hnz
    exact hrealize d ((isSolution_iff ι u w d).2 hd)
  refine ⟨G, hG, ?_⟩
  have hlift : Relation.ReflTransGen
      (fun A B : FanOnRays ι u => indicator ι u B - indicator ι u A ∈ G ∧
        UsesEndpointCones ι u Φ Ψ A ∧ UsesEndpointCones ι u Φ Ψ B)
      (realize c) (realize d) := by
    apply Relation.ReflTransGen.lift realize (fun a b hab => ?_) _ _ hpath
    obtain ⟨hmove, haA, hbA, habox, hbbox, han, hbn⟩ := hab
    have hasol : IsSolution ι u w a := (isSolution_iff ι u w a).2 ⟨han, haA.trans hc.2⟩
    have hbsol : IsSolution ι u w b := (isSolution_iff ι u w b).2 ⟨hbn, hbA.trans hc.2⟩
    have haeq := hrealize a hasol
    have hbeq := hrealize b hbsol
    refine ⟨?_, ?_, ?_⟩
    · simpa only [haeq, hbeq] using hmove
    · apply usesEndpointCones_of_between ι u hnz Φ Ψ (realize a)
      simpa only [haeq] using habox
    · apply usesEndpointCones_of_between ι u hnz Φ Ψ (realize b)
      simpa only [hbeq] using hbbox
  simpa only [hstart, hend] using hlift

end Unimodular.AllowedBlocks

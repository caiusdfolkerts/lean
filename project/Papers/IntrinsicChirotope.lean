module
public import Papers.SmallRankChirotopeDensity
public import Papers.ChirotopeRanks
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

noncomputable section

open Matrix Set Filter Topology Module
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

def frameMap {r d : ℕ} (E : Fin r → Fin d → ℝ) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x := ∑ j, x j • E j
  map_add' x y := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]

theorem frameMap_injective {r d : ℕ} {E : Fin r → Fin d → ℝ}
    (hE : LinearIndependent ℝ E) : Function.Injective (frameMap E) := by
  intro x y hxy
  have hz : ∑ j, (x-y) j • E j = 0 := by
    change frameMap E (x-y) = 0
    rw [map_sub,hxy,sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp hE (x-y) hz
  ext j
  exact sub_eq_zero.mp (hcoeff j)

def reconstruct {n r d : ℕ} (E : Fin r → Fin d → ℝ)
    (p : Fin n → Fin r → ℝ) : Fin n → Fin d → ℝ :=
  fun i => frameMap E (p i)

theorem continuous_reconstruct {n r d : ℕ} :
    Continuous (fun z : (Fin r → Fin d → ℝ) × (Fin n → Fin r → ℝ) =>
      reconstruct z.1 z.2) := by
  unfold reconstruct frameMap
  apply continuous_pi
  intro i
  exact continuous_finsetSum Finset.univ fun j _ =>
    (show Continuous (fun z : (Fin r → Fin d → ℝ) × (Fin n → Fin r → ℝ) => z.2 i j)
      from (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).smul
      (show Continuous (fun z : (Fin r → Fin d → ℝ) × (Fin n → Fin r → ℝ) => z.1 j)
        from (continuous_apply j).comp continuous_fst)

theorem RatScalar.finset_sum {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ S, RatScalar (f i)) : RatScalar (∑ i ∈ S, f i) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simpa using RatScalar.zero
  | @insert a S ha ih =>
    intro hf
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem reconstruct_rational {n r d : ℕ}
    {E : Fin r → Fin d → ℝ} {p : Fin n → Fin r → ℝ}
    (hE : RationalCoordinates E) (hp : RationalCoordinates p) :
    RationalCoordinates (reconstruct E p) := by
  intro i k
  change RatScalar ((∑ j, p i j • E j) k)
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact RatScalar.finset_sum _ _ fun j _ => (hp i j).mul (hE j k)

theorem reconstruct_independent_iff {n r d : ℕ}
    {E : Fin r → Fin d → ℝ} (hE : LinearIndependent ℝ E)
    (p : Fin n → Fin r → ℝ) (S : Set (Fin n)) :
    LinearIndepOn ℝ (reconstruct E p) S ↔ LinearIndepOn ℝ p S := by
  constructor
  · intro h
    exact LinearIndependent.of_comp (frameMap E) h
  · intro h
    exact h.map' (frameMap E) (LinearMap.ker_eq_bot.mpr (frameMap_injective hE))

/-- A concrete representation of the same oriented linear type: intrinsic
coordinates span their full rank, both embeddings are injective, and every
maximal-minor sign agrees. Thus rank, zero vectors, repeated projective
points and oriented dependence data retain their usual meaning. -/
def SameRepresentedType {n d : ℕ} (p q : Fin n → Fin d → ℝ) : Prop :=
  ∃ r : ℕ, ∃ (u v : Fin n → Fin r → ℝ) (E F : Fin r → Fin d → ℝ),
    Spans u ∧ Spans v ∧ LinearIndependent ℝ E ∧ LinearIndependent ℝ F ∧
      reconstruct E u = p ∧ reconstruct F v = q ∧ SameChirotope u v

theorem SameRepresentedType.independent_iff {n d : ℕ}
    {p q : Fin n → Fin d → ℝ} (h : SameRepresentedType p q)
    (S : Set (Fin n)) :
    LinearIndepOn ℝ p S ↔ LinearIndepOn ℝ q S := by
  obtain ⟨r,u,v,E,F,hu,hv,hE,hF,rfl,rfl,hχ⟩ := h
  rw [reconstruct_independent_iff hE,reconstruct_independent_iff hF]
  exact hχ.independent_iff hu S

theorem SameRepresentedType.subset_rank_eq {n d : ℕ}
    {p q : Fin n → Fin d → ℝ} (h : SameRepresentedType p q)
    (S : Set (Fin n)) :
    finrank ℝ (Submodule.span ℝ (p '' S)) =
      finrank ℝ (Submodule.span ℝ (q '' S)) := by
  apply Nat.le_antisymm
  · exact finrank_span_image_le_of_independence_imp p q
      (fun T => (h.independent_iff T).mp) S
  · exact finrank_span_image_le_of_independence_imp q p
      (fun T => (h.independent_iff T).mpr) S

theorem embedded_density_of_intrinsic_density {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (hu : Spans u)
    (E : Fin r → Fin d → ℝ) (hE : LinearIndependent ℝ E)
    (huc : u ∈ closure (RationalRealizations u)) :
    reconstruct E u ∈ closure
      {q | RationalCoordinates q ∧ SameRepresentedType (reconstruct E u) q} := by
  have hEc : E ∈ closure {F : Fin r → Fin d → ℝ |
      RationalCoordinates F ∧ LinearIndependent ℝ F} := by
    have h := mem_closure_inter_of_eventually (rationalCoordinates_dense r d E) hE.eventually
    exact h
  have hprod : (E,u) ∈ closure
      ({F : Fin r → Fin d → ℝ | RationalCoordinates F ∧ LinearIndependent ℝ F} ×ˢ
        RationalRealizations u) := by
    rw [closure_prod_eq]
    exact ⟨hEc,huc⟩
  let G := fun z : (Fin r → Fin d → ℝ) × (Fin n → Fin r → ℝ) =>
    reconstruct z.1 z.2
  have hcl := mem_closure_image (continuous_reconstruct (n := n) (r := r) (d := d)).continuousAt
    hprod
  apply closure_mono (s := G '' _) ?_ hcl
  rintro _ ⟨⟨F,v⟩,⟨hF,hv⟩,rfl⟩
  refine ⟨reconstruct_rational hF.1 hv.1,?_⟩
  exact ⟨r,u,v,E,F,hu,spans_of_zero_minor_pattern hu hv.2.zero_iff,
    hE,hF.2,rfl,rfl,hv.2⟩

theorem embedded_rational_density {n r d : ℕ}
    (hn : n ≤ 8) (hr : r ≤ 3)
    (u : Fin n → Fin r → ℝ) (hu : Spans u)
    (E : Fin r → Fin d → ℝ) (hE : LinearIndependent ℝ E) :
    reconstruct E u ∈ closure
      {q | RationalCoordinates q ∧ SameRepresentedType (reconstruct E u) q} :=
  embedded_density_of_intrinsic_density u hu E hE
    (rational_chirotope_dense_le_three hn hr u)

/-- Every actual vector configuration has full intrinsic coordinates and
an injective real linear embedding into its original ambient space. -/
theorem exists_intrinsic_linear_configuration {n d : ℕ}
    (p : Fin n → Fin d → ℝ) :
    ∃ r ≤ d, ∃ (u : Fin n → Fin r → ℝ) (E : Fin r → Fin d → ℝ),
      Spans u ∧ LinearIndependent ℝ E ∧ reconstruct E u = p := by
  classical
  let S := Submodule.span ℝ (Set.range p)
  let r := finrank ℝ S
  let B : Basis (Fin r) ℝ S := Module.finBasis ℝ S
  let pS : Fin n → S := fun i => ⟨p i,Submodule.subset_span ⟨i,rfl⟩⟩
  let u : Fin n → Fin r → ℝ := fun i => B.equivFun (pS i)
  let E : Fin r → Fin d → ℝ := fun j => (B j : Fin d → ℝ)
  have hsdim : r ≤ d := by
    have h := S.finrank_le
    simpa [r,Module.finrank_fintype_fun_eq_card] using h
  have hpS : Submodule.span ℝ (Set.range pS) = ⊤ := by
    apply top_unique
    intro x _
    have hmap : S ≤ (Submodule.span ℝ (Set.range pS)).map S.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨pS i,Submodule.subset_span ⟨i,rfl⟩,rfl⟩
    obtain ⟨y,hy,hyx⟩ := hmap x.2
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  have huspan : Spans u := by
    change Submodule.span ℝ (Set.range (B.equivFun ∘ pS)) = ⊤
    rw [Set.range_comp]
    change Submodule.span ℝ (B.equivFun.toLinearMap '' Set.range pS) = ⊤
    rw [← Submodule.map_span, hpS, Submodule.map_top, LinearEquiv.range]
  have hELI : LinearIndependent ℝ E :=
    B.linearIndependent.map' S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨r,hsdim,u,E,huspan,hELI,?_⟩
  ext i k
  have h := congrArg (fun x : S => (x : Fin d → ℝ) k) (B.sum_equivFun (pS i))
  change (∑ j, B.equivFun (pS i) j • (B j : Fin d → ℝ)) k = p i k
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

/-- Lemma 10 for literal homogeneous three-vectors. The formulation includes
collinear configurations, repeated projective labels, and zero vectors. -/
theorem projective_plane_rational_density {n : ℕ}
    (hn : n ≤ 8) (p : Fin n → Fin 3 → ℝ) :
    p ∈ closure {q | RationalCoordinates q ∧ SameRepresentedType p q} := by
  obtain ⟨r,hr,u,E,hu,hE,hp⟩ := exists_intrinsic_linear_configuration p
  have h := embedded_rational_density hn hr u hu E hE
  simpa only [hp] using h

end Papers.RationalityTen.ChirotopeDensity

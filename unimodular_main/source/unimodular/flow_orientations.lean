module

public import Unimodular.Extensions
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

noncomputable section

namespace Unimodular.FlowOrientations

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- The integral relation module of a labelled family of lattice vectors. -/
def relations {n : ℕ} (u : E → Lattice n) : Submodule ℤ (E → ℤ) :=
  (Fintype.linearCombination ℤ u).ker

@[simp] theorem mem_relations_iff {n : ℕ} (u : E → Lattice n) (r : E → ℤ) :
    r ∈ relations u ↔ (∑ e, r e • u e) = 0 := Iff.rfl

/-- Finitely many coordinate hyperplanes fail to cover an integral relation module as soon
as each is proper. This includes the empty set of coordinates and the zero module. -/
theorem exists_relation_avoiding (L : Submodule ℤ (E → ℤ)) (D : Set E) :
    (∃ r ∈ L, ∀ e, e ∉ D → r e ≠ 0) ↔
      ∀ e, e ∉ D → ∃ r ∈ L, r e ≠ 0 := by
  classical
  constructor
  · rintro ⟨r, hr, hne⟩ e he
    exact ⟨r, hr, hne e he⟩
  · intro h
    let K := {e : E // e ∉ D}
    have hex : ∀ k : K, ∃ r : E → ℤ, r ∈ L ∧ r k.val ≠ 0 :=
      fun k => h k.val k.property
    choose g hg hgne using hex
    let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
    obtain ⟨t, ht, havoid⟩ := GenericWeights.exists_geometric_progression
      (fun k : K => fun j : Fin (Fintype.card K) => g (e j) k.val)
      (fun k => ⟨e.symm k, by simpa using hgne k⟩)
    let r : E → ℤ := ∑ j : Fin (Fintype.card K), (t ^ j.val) • g (e j)
    refine ⟨r, L.sum_mem (fun j _ => L.smul_mem _ (hg (e j))), ?_⟩
    intro k hk
    have ha := havoid ⟨k, hk⟩
    simpa only [r, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using ha

/-- The ordinary linear-algebra criterion for a coloop: the selected vector does not lie
in the real span of all the other labelled vectors. -/
def IsColoop {n : ℕ} (u : E → Lattice n) (e : E) : Prop :=
  embed (u e) ∉ Submodule.span ℝ ((fun f => embed (u f)) '' {f | f ≠ e})

end Unimodular.FlowOrientations

end

noncomputable section

namespace Unimodular.FlowOrientations

open scoped BigOperators

variable {E : Type*} [Fintype E] {n : ℕ}

@[simp] theorem embed_zero : embed (0 : Lattice n) = 0 := by ext i; simp [embed]

@[simp] theorem embed_neg (x : Lattice n) : embed (-x) = -embed x := by
  ext i
  simp [embed]

@[simp] theorem embed_int_combination (u : E → Lattice n) (c : E → ℤ) :
    embed (∑ e, c e • u e) = ∑ e, (c e : ℝ) • embed (u e) := by
  ext i
  simp [embed, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Uniform unimodularity is inherited by an arbitrary labelled subfamily, with repetitions
permitted. This is used only to change indices, not to add a mathematical hypothesis. -/
theorem uniform_subfamily (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    {F : Type*} (v : F → Lattice n) (hv : ∀ f, ∃ e, v f = u e) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) v := by
  intro a
  choose e he using (fun i : Fin n => hv (a i))
  have hcomp : v ∘ a = u ∘ e := funext he
  rw [hcomp]
  exact hu e

/-- A full-rank uniformly unimodular family spans its actual integral lattice. -/
theorem integer_span_of_uniform_full (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) :
    Submodule.span ℤ (Set.range u) = ⊤ := by
  classical
  let U : Set (Lattice n) := Set.range u
  have hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun v : U => v.val) :=
    uniform_subfamily u hu (fun v : U => v.val)
      (fun v => by obtain ⟨e, he⟩ := v.property; exact ⟨e, he.symm⟩)
  have hUspan : Submodule.span ℝ (embed '' U) = ⊤ := by
    change Submodule.span ℝ (embed '' Set.range u) = ⊤
    rw [← Set.range_comp']
    exact hspan
  let a : Fin 0 → U := Fin.elim0
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension U hU hUspan a
    (linearIndependent_empty_type : LinearIndependent ℝ (fun j => embed (a j).val))
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_mono (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hb i)

/-- A nonzero coefficient in an integral relation witnesses that the corresponding vector
is in the real span of the other vectors. -/
theorem not_isColoop_of_relation (u : E → Lattice n) {e : E} {r : E → ℤ}
    (hr : r ∈ relations u) (hne : r e ≠ 0) : ¬ IsColoop u e := by
  classical
  let P := Submodule.span ℝ ((fun f => embed (u f)) '' {f | f ≠ e})
  have hreal : (∑ f, (r f : ℝ) • embed (u f)) = 0 := by
    simpa only [embed_int_combination, embed_zero] using congrArg embed ((mem_relations_iff u r).1 hr)
  have hsum : (r e : ℝ) • embed (u e) +
      (∑ f ∈ Finset.univ.erase e, (r f : ℝ) • embed (u f)) = 0 := by
    exact (Finset.add_sum_erase Finset.univ
      (fun f => (r f : ℝ) • embed (u f)) (Finset.mem_univ e)).trans hreal
  have hother : (∑ f ∈ Finset.univ.erase e, (r f : ℝ) • embed (u f)) ∈ P := by
    apply P.sum_mem
    intro f hf
    exact P.smul_mem _ (Submodule.subset_span ⟨f, (Finset.mem_erase.mp hf).1, rfl⟩)
  have hmem : (r e : ℝ) • embed (u e) ∈ P := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact P.neg_mem hother
  have hm : embed (u e) ∈ P :=
    (P.smul_mem_iff (by exact_mod_cast hne : (r e : ℝ) ≠ 0)).1 hmem
  exact fun hc => hc hm

/-- Every non-coloop of a spanning uniformly unimodular family has an integral relation
whose selected coefficient is exactly one. -/
theorem exists_relation_at_one (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    {e : E} (he : ¬ IsColoop u e) :
    ∃ r ∈ relations u, r e = 1 := by
  classical
  have hem : embed (u e) ∈
      Submodule.span ℝ ((fun f => embed (u f)) '' {f | f ≠ e}) := by
    simpa only [IsColoop, not_not] using he
  have hdelete : Submodule.span ℝ ((fun f => embed (u f)) '' {f | f ≠ e}) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.2
    rintro x ⟨f, rfl⟩
    by_cases hfe : f = e
    · subst f; exact hem
    · exact Submodule.subset_span ⟨f, hfe, rfl⟩
  let F := {f : E // f ≠ e}
  let v : F → Lattice n := fun f => u f.val
  have hv : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) v :=
    uniform_subfamily u hu v (fun f => ⟨f.val, rfl⟩)
  have hvspan : Submodule.span ℝ (Set.range (fun f : F => embed (v f))) = ⊤ := by
    have hrange : Set.range (fun f : F => embed (v f)) =
        (fun f => embed (u f)) '' {f | f ≠ e} := by
      ext x
      constructor
      · rintro ⟨f, rfl⟩; exact ⟨f.val, f.property, rfl⟩
      · rintro ⟨f, hf, rfl⟩; exact ⟨⟨f, hf⟩, rfl⟩
    rw [hrange]
    exact hdelete
  have hZ := integer_span_of_uniform_full v hv hvspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1
    (show u e ∈ Submodule.span ℤ (Set.range v) by rw [hZ]; trivial)
  let d : E → ℤ := fun f => if h : f ≠ e then c ⟨f, h⟩ else 0
  have hd : (∑ f, d f • u f) = u e := by
    rw [← Fintype.sum_of_injective Subtype.val Subtype.val_injective
      (fun f : F => c f • v f) (fun f => d f • u f)
      (by
        intro f hf
        have hfe : f = e := by
          by_contra hne
          exact hf ⟨⟨f, hne⟩, rfl⟩
        simp [d, hfe]) (by intro f; simp [d, v, f.property])]
    exact hc
  refine ⟨Pi.single e 1 - d, ?_, ?_⟩
  · change Fintype.linearCombination ℤ u (Pi.single e 1 - d) = 0
    rw [map_sub, Fintype.linearCombination_apply_single, one_smul]
    change u e - (∑ f, d f • u f) = 0
    rw [hd, sub_self]
  · simp [d]

/-- The exact coloop criterion for the integral relation space. -/
theorem isColoop_iff_all_relations_zero (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) (e : E) :
    IsColoop u e ↔ ∀ r ∈ relations u, r e = 0 := by
  constructor
  · intro he r hr
    by_contra hne
    exact not_isColoop_of_relation u hr hne he
  · intro h
    by_contra he
    obtain ⟨r, hr, hre⟩ := exists_relation_at_one u hu hspan he
    have := h r hr
    omega

/-- The existence assertion (2.2) in Proposition 2.3, with every finite rank and every
choice of doubled labels. Coloops are defined by the actual represented linear dependence. -/
theorem proposition_2_3_integral_relation (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) (D : Set E) :
    (∃ r ∈ relations u, ∀ e, e ∉ D → r e ≠ 0) ↔
      ∀ e, IsColoop u e → e ∈ D := by
  rw [exists_relation_avoiding]
  constructor
  · intro h e he
    by_contra hn
    obtain ⟨r, hr, hne⟩ := h e hn
    exact not_isColoop_of_relation u hr hne he
  · intro h e he
    have hc : ¬ IsColoop u e := fun hc => he (h e hc)
    obtain ⟨r, hr, hre⟩ := exists_relation_at_one u hu hspan hc
    exact ⟨r, hr, by omega⟩

end Unimodular.FlowOrientations

end


/-! ## Rational nonnegative relations

The two proofs in this section are adapted verbatim, apart from namespace qualification,
from TauCeti/Geometry/Toric/Algebraic/Cone/Inf.lean, commit
06d5bb4e3ebb737dc6538567f5c53bf8800b9362. Copyright 2026 the Tau Ceti contributors;
Apache 2.0 license. They are compiled here because that source module was not included
in the recovered checked-artifact closure. No assertion from it is imported without proof.
-/

noncomputable section

namespace Unimodular.FlowOrientations.RationalRelations

open scoped BigOperators

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- The induction step for `mem_hull_natCast_relations_iff_of_liftBaseChange_injective`: an
integral relation `k` among the `v j`, supported in the support of a nonnegative real relation `c`
and positive somewhere, writes `c` as a nonnegative combination of nonnegative real relations of
smaller support and, when `k` is nonnegative, of `k` itself. -/
private theorem mem_hull_natCast_relations_of_int_relation {ι : Type*} [Fintype ι] {v : ι → N}
    {c : ι → ℝ} (hc : 0 ≤ c) (hcv : ∑ j, c j • i (v j) = 0)
    (step : ∀ u : ι → ℝ, 0 ≤ u → ∑ j, u j • i (v j) = 0 → Function.support u ⊂ Function.support c →
      u ∈ PointedCone.hull ℝ ((fun k : ι → ℕ ↦ fun j ↦ (k j : ℝ)) '' {k | ∑ j, k j • v j = 0}))
    {k : ι → ℤ} (hkv : ∑ j, k j • v j = 0) (hk : ∀ j, c j = 0 → k j = 0) (hpos : ∃ j, 0 < k j) :
    c ∈ PointedCone.hull ℝ ((fun k : ι → ℕ ↦ fun j ↦ (k j : ℝ)) '' {k | ∑ j, k j • v j = 0}) := by
  set C := PointedCone.hull ℝ ((fun k : ι → ℕ ↦ fun j ↦ (k j : ℝ)) '' {k | ∑ j, k j • v j = 0})
  let kR : ι → ℝ := fun j ↦ (k j : ℝ)
  have hrel : ∀ s : ℝ, ∑ j, (c - s • kR) j • i (v j) = 0 := fun s ↦ by
    have hkR : ∑ j, kR j • i (v j) = 0 := by
      simpa only [kR, map_sum, map_zsmul, map_zero, Int.cast_smul_eq_zsmul] using congrArg i hkv
    simp [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hcv, hkR]
  obtain ⟨s, hs, hu, hsub⟩ := TauCeti.exists_pos_sub_smul_nonneg_support_ssubset hc (Set.toFinite _)
    (k := kR) (fun j h ↦ by simp [kR, hk j h]) (let ⟨j, hj⟩ := hpos; ⟨j, by simpa [kR]⟩)
  have hu₁ := step _ hu (hrel s) hsub
  by_cases hneg : ∃ j, k j < 0
  · -- Both directions along `k` leave the cone: `c` lies between two smaller relations.
    obtain ⟨t, ht, hu', hsub'⟩ :=
      TauCeti.exists_pos_sub_smul_nonneg_support_ssubset hc (Set.toFinite _)
      (k := -kR) (fun j h ↦ by simp [kR, hk j h]) (let ⟨j, hj⟩ := hneg; ⟨j, by simpa [kR]⟩)
    have hu₂ := step _ hu' (by simpa [sub_eq_add_neg] using hrel (-t)) hsub'
    have hcomb : c = (t / (s + t)) • (c - s • kR) + (s / (s + t)) • (c - t • -kR) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
      field_simp
      ring
    rw [hcomb]
    exact C.add_mem (C.smul_mem (by positivity) hu₁) (C.smul_mem (by positivity) hu₂)
  · -- `k` itself is a natural-number relation, so `c` is a smaller relation plus `s • k`.
    simp only [not_exists, not_lt] at hneg
    have hk₀ : kR ∈ C := PointedCone.subset_hull ⟨fun j ↦ (k j).toNat, ?_, ?_⟩
    · rw [← sub_add_cancel c (s • kR)]
      exact C.add_mem hu₁ (C.smul_mem hs.le hk₀)
    · simpa [← natCast_zsmul, Int.toNat_of_nonneg (hneg _)] using hkv
    · ext j
      simp only [kR]
      exact_mod_cast Int.toNat_of_nonneg (hneg j)

/-- **Rational generation of nonnegative relations.** When the real-linear map
`ℝ ⊗[ℤ] N →ₗ[ℝ] V` induced by `i` is injective (for instance when `i` is an integral lattice, or
more generally extends scalars from `ℤ` to `ℝ`), for finitely many lattice vectors `v j`, a real
vector `c` is a nonnegative linear combination of natural-number relations `k` (those with
`∑ j, k j • v j = 0`) exactly when it is a nonnegative real relation among the vectors
`i (v j)`. -/
theorem mem_hull_natCast_relations_iff_of_liftBaseChange_injective
    (hi : Function.Injective (i.toIntLinearMap.liftBaseChange ℝ))
    {ι : Type*} [Fintype ι] (v : ι → N) {c : ι → ℝ} :
    c ∈ PointedCone.hull ℝ
        ((fun k : ι → ℕ ↦ fun j ↦ (k j : ℝ)) '' {k | ∑ j, k j • v j = 0}) ↔
      0 ≤ c ∧ ∑ j, c j • i (v j) = 0 := by
  classical
  refine ⟨i.nonneg_relation_of_mem_hull_natCast_relations, ?_⟩
  rintro ⟨hc, hcv⟩
  -- Strong induction on the number of nonzero coordinates of `c`.
  induction hn : (Function.support c).ncard using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  have step : ∀ u : ι → ℝ, 0 ≤ u → ∑ j, u j • i (v j) = 0 →
      Function.support u ⊂ Function.support c → u ∈ PointedCone.hull ℝ
        ((fun k : ι → ℕ ↦ fun j ↦ (k j : ℝ)) '' {k | ∑ j, k j • v j = 0}) :=
    fun u hu huv hsub ↦ ih _ (hn ▸ Set.ncard_lt_ncard hsub (Set.toFinite _)) hu huv rfl
  by_cases hli : LinearIndependent ℤ fun j : {j // c j ≠ 0} ↦ v j
  · -- Independent vectors in the support have no nonzero real relation, so `c = 0`.
    have hsupp : ∑ j : {j // c j ≠ 0}, c j • i (v j) = 0 := by
      rw [Fintype.sum_of_injective Subtype.val Subtype.val_injective
        (fun j : {j // c j ≠ 0} ↦ c j • i (v j)) (fun j ↦ c j • i (v j))
        (by simp +contextual) (by simp), hcv]
    have hzero := Fintype.linearIndependent_iff.1
      ((TauCeti.Toric.linearIndependent_comp_iff_of_liftBaseChange_injective hi).2 hli) (fun j ↦ c j) hsupp
    have : c = 0 := funext fun j ↦ by_contra fun hj ↦ hj (hzero ⟨j, hj⟩)
    exact this ▸ Submodule.zero_mem _
  · -- A dependence among the vectors in the support gives an integral relation.
    obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.1 hli
    let k : ι → ℤ := fun j ↦ if h : c j ≠ 0 then g ⟨j, h⟩ else 0
    have hk : ∀ j, c j = 0 → k j = 0 := fun j h ↦ by simp [k, h]
    have hkg : ∀ j : {j // c j ≠ 0}, k j = g j := fun j ↦ by simp [k, j.2]
    have hkv : ∑ j, k j • v j = 0 := by
      rw [← Fintype.sum_of_injective Subtype.val Subtype.val_injective
        (fun j : {j // c j ≠ 0} ↦ g j • v j) (fun j ↦ k j • v j)
        (by simp +contextual [k]) (by simp [hkg])]
      exact hg
    have hkj₀ : k j₀ ≠ 0 := hkg j₀ ▸ hj₀
    rcases hkj₀.lt_or_gt with hlt | hgt
    · exact mem_hull_natCast_relations_of_int_relation hc hcv step (k := -k)
        (by simpa [neg_smul] using hkv) (fun j h ↦ by simp [hk j h]) ⟨j₀, by simpa using hlt⟩
    · exact mem_hull_natCast_relations_of_int_relation hc hcv step hkv hk ⟨j₀, hgt⟩


end Unimodular.FlowOrientations.RationalRelations

end

noncomputable section

namespace Unimodular.FlowOrientations

open scoped BigOperators

variable {E V : Type*} [Fintype E] [AddCommGroup V] [Module ℝ V]

/-- A finite positively spanning family has a relation with every coefficient strictly
positive. No independence, salience, or integrality is assumed. -/
theorem exists_positive_real_relation_of_hull_top (v : E → V)
    (hv : PointedCone.hull ℝ (Set.range v) = ⊤) :
    ∃ c : E → ℝ, (∀ e, 0 < c e) ∧ (∑ e, c e • v e) = 0 := by
  classical
  have hex : ∀ e : E, ∃ b : E → ℝ, (∀ f, 0 ≤ b f) ∧
      (∑ f, b f • v f) = -v e := by
    intro e
    have hm : -v e ∈ PointedCone.hull ℝ (Set.range v) := by rw [hv]; trivial
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).1 hm
    exact ⟨fun f => (b f : ℝ), fun f => (b f).property, by
      simpa only [Nonneg.coe_smul] using hb⟩
  choose b hb hrel using hex
  let c : E → ℝ := fun f => 1 + ∑ e, b e f
  refine ⟨c, ?_, ?_⟩
  · intro f
    have hsum : 0 ≤ ∑ e, b e f := Finset.sum_nonneg (fun e _ => hb e f)
    dsimp [c]
    linarith
  · calc
      (∑ f, c f • v f) = (∑ f, v f) + ∑ f, ∑ e, b e f • v f := by
        simp only [c, add_smul, one_smul, Finset.sum_smul, Finset.sum_add_distrib]
      _ = (∑ f, v f) + ∑ e, ∑ f, b e f • v f := by rw [Finset.sum_comm]
      _ = 0 := by simp_rw [hrel]; simp

/-- A spanning family with a strictly positive dependence spans positively. The proof
puts both signs of every generator in the actual conic hull. -/
theorem hull_top_of_positive_real_relation (v : E → V)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (c : E → ℝ) (hc : ∀ e, 0 < c e) (hrel : (∑ e, c e • v e) = 0) :
    PointedCone.hull ℝ (Set.range v) = ⊤ := by
  classical
  let C := PointedCone.hull ℝ (Set.range v)
  have hneg : ∀ e, -v e ∈ C := by
    intro e
    have hother : (∑ f ∈ Finset.univ.erase e, c f • v f) ∈ C := by
      apply C.sum_mem
      intro f hf
      exact C.smul_mem (hc f).le (PointedCone.subset_hull ⟨f, rfl⟩)
    have hsum : c e • v e + (∑ f ∈ Finset.univ.erase e, c f • v f) = 0 := by
      exact (Finset.add_sum_erase Finset.univ (fun f => c f • v f)
        (Finset.mem_univ e)).trans hrel
    have heq : c e • -v e = ∑ f ∈ Finset.univ.erase e, c f • v f := by
      rw [smul_neg]
      exact neg_eq_iff_eq_neg.2 (eq_neg_of_add_eq_zero_left hsum)
    exact (C.smul_mem_iff (hc e)).1 (heq.symm ▸ hother)
  have hlineal : Submodule.span ℝ (Set.range v) ≤ C.lineal :=
    Submodule.span_le.2 (fun x hx => by
      obtain ⟨e, rfl⟩ := hx
      exact ⟨PointedCone.subset_hull ⟨e, rfl⟩, hneg e⟩)
  apply top_unique
  intro x hx
  apply C.lineal_le
  apply hlineal
  rw [hspan]
  trivial

/-- Real positive spanning is equivalent to linear spanning and a strictly positive
relation; this includes empty families and rank zero. -/
theorem hull_top_iff_span_and_positive_relation (v : E → V) :
    PointedCone.hull ℝ (Set.range v) = ⊤ ↔
      Submodule.span ℝ (Set.range v) = ⊤ ∧
      ∃ c : E → ℝ, (∀ e, 0 < c e) ∧ (∑ e, c e • v e) = 0 := by
  constructor
  · intro h
    refine ⟨?_, exists_positive_real_relation_of_hull_top v h⟩
    apply top_unique
    intro x hx
    apply PointedCone.hull_le_span ℝ (Set.range v)
    rw [h]
    trivial
  · rintro ⟨hspan, c, hc, hrel⟩
    exact hull_top_of_positive_real_relation v hspan c hc hrel

variable {n : ℕ}

/-- Rational generation of a real relation cone gives an integral relation positive at
every coordinate whenever a strictly positive real relation exists. This proves, rather
than assumes, the denominator-clearing step in Proposition 2.3. -/
theorem exists_positive_integer_relation_of_real (u : E → Lattice n)
    (c : E → ℝ) (hc : ∀ e, 0 < c e)
    (hrel : (∑ e, c e • embed (u e)) = 0) :
    ∃ r ∈ relations u, ∀ e, 0 < r e := by
  classical
  let S : Set (E → ℝ) :=
    (fun k : E → ℕ => fun e => (k e : ℝ)) '' {k | (∑ e, k e • u e) = 0}
  have hi := (TauCeti.Toric.isIntegralLattice_intCast n).isBaseChange.liftBaseChange_injective
  have hmem : c ∈ PointedCone.hull ℝ S :=
    (RationalRelations.mem_hull_natCast_relations_iff_of_liftBaseChange_injective hi u).2
      ⟨fun e => (hc e).le, hrel⟩
  have hex : ∀ e : E, ∃ k : E → ℕ, (∑ f, k f • u f) = 0 ∧ 0 < k e := by
    intro e
    by_contra hn
    push_neg at hn
    let P : Submodule ℝ (E → ℝ) := (LinearMap.proj e).ker
    have hS : S ⊆ P := by
      rintro x ⟨k, hk, rfl⟩
      change (k e : ℝ) = 0
      have hz : k e = 0 := Nat.eq_zero_of_le_zero (hn k hk)
      simp [hz]
    have hcone : PointedCone.hull ℝ S ≤ PointedCone.ofSubmodule P :=
      Submodule.span_le.2 hS
    have hzero : c e = 0 := hcone hmem
    exact (ne_of_gt (hc e)) hzero
  choose k hk hpos using hex
  let r : E → ℤ := fun f => ∑ e, (k e f : ℤ)
  refine ⟨r, ?_, ?_⟩
  · rw [mem_relations_iff]
    calc
      (∑ f, r f • u f) = ∑ f, ∑ e, (k e f : ℤ) • u f := by
        simp only [r, Finset.sum_smul]
      _ = ∑ e, ∑ f, (k e f : ℤ) • u f := Finset.sum_comm
      _ = 0 := by
        have hk' : ∀ e, (∑ f, (k e f : ℤ) • u f) = 0 :=
          fun e => by simpa only [natCast_zsmul] using hk e
        simp only [hk', Finset.sum_const_zero]
  · intro f
    have hle : (k f f : ℤ) ≤ r f :=
      Finset.single_le_sum (fun e _ => Int.natCast_nonneg _) (Finset.mem_univ f)
    have hpf : (0 : ℤ) < k f f := by exact_mod_cast hpos f
    exact hpf.trans_le hle

/-- The full positive-spanning/integral-flow equivalence for arbitrary finite integer
configurations. Uniform unimodularity is not needed for this part. -/
theorem hull_top_iff_span_and_positive_integer_relation (u : E → Lattice n) :
    PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤ ↔
      Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤ ∧
        ∃ r ∈ relations u, ∀ e, 0 < r e := by
  rw [hull_top_iff_span_and_positive_relation]
  constructor
  · rintro ⟨hs, c, hc, hr⟩
    exact ⟨hs, exists_positive_integer_relation_of_real u c hc hr⟩
  · rintro ⟨hs, r, hr, hpos⟩
    refine ⟨hs, (fun e => (r e : ℝ)), ?_, ?_⟩
    · intro e
      change (0 : ℝ) < (r e : ℝ)
      exact_mod_cast hpos e
    · simpa only [embed_int_combination, embed_zero] using congrArg embed ((mem_relations_iff u r).1 hr)

end Unimodular.FlowOrientations

end

noncomputable section

namespace Unimodular.FlowOrientations

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] {n : ℕ}

/-- Keep one ray on every reference line and add its negative exactly on the doubled lines. -/
abbrev OrientedIndex (D : Set E) := E ⊕ {e : E // e ∈ D}

noncomputable def leftSign (D : Set E) (ε : E → ℤ) (e : E) : ℤ :=
  if e ∈ D then 1 else ε e

noncomputable def orientedFamily (u : E → Lattice n) (D : Set E) (ε : E → ℤ) :
    OrientedIndex D → Lattice n :=
  Sum.elim (fun e => leftSign D ε e • u e) (fun e => -u e.val)

noncomputable def secondCoefficient (D : Set E) (p : OrientedIndex D → ℤ) (e : E) : ℤ :=
  if h : e ∈ D then p (Sum.inr ⟨e, h⟩) else 0

noncomputable def combineCoefficients (D : Set E) (ε : E → ℤ)
    (p : OrientedIndex D → ℤ) : E → ℤ :=
  fun e => p (Sum.inl e) * leftSign D ε e - secondCoefficient D p e

/-- Combining coefficients along doubled lines is the literal integral pushforward of
relations, including the signs of undoubled rays. -/
theorem sum_orientedFamily (u : E → Lattice n) (D : Set E) (ε : E → ℤ)
    (p : OrientedIndex D → ℤ) :
    (∑ j, p j • orientedFamily u D ε j) =
      ∑ e, combineCoefficients D ε p e • u e := by
  classical
  have hsecond : (∑ e, secondCoefficient D p e • u e) =
      ∑ e : {e : E // e ∈ D}, p (Sum.inr e) • u e.val := by
    rw [← Fintype.sum_of_injective Subtype.val Subtype.val_injective
      (fun e : {e : E // e ∈ D} => p (Sum.inr e) • u e.val)
      (fun e => secondCoefficient D p e • u e)
      (by simp +contextual [secondCoefficient]) (by simp [secondCoefficient])]
  rw [Fintype.sum_sum_type]
  simp only [orientedFamily, Sum.elim_inl, Sum.elim_inr, smul_smul, smul_neg,
    Finset.sum_neg_distrib, combineCoefficients, sub_smul, Finset.sum_sub_distrib]
  rw [hsecond]
  rfl

theorem sign_abs_mul (z : ℤ) : |z| * z.sign = z := by
  by_cases hp : 0 < z
  · rw [Int.sign_eq_one_of_pos hp, abs_of_pos hp, mul_one]
  · by_cases hn : z < 0
    · rw [Int.sign_eq_neg_one_of_neg hn, abs_of_neg hn]
      ring
    · have hz : z = 0 := by omega
      simp [hz]

theorem abs_sign_eq_one {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rcases lt_or_gt_of_ne hz with hn | hp
  · rw [Int.sign_eq_neg_one_of_neg hn]; norm_num
  · rw [Int.sign_eq_one_of_pos hp]; norm_num

noncomputable def flowWeights (D : Set E) (r : E → ℤ) : OrientedIndex D → ℤ :=
  Sum.elim (fun e => if e ∈ D then 1 + max (r e) 0 else |r e|)
    (fun e => 1 + max (-r e.val) 0)

theorem flowWeights_positive (D : Set E) (r : E → ℤ)
    (hr : ∀ e, e ∉ D → r e ≠ 0) : ∀ j, 0 < flowWeights D r j := by
  classical
  intro j
  cases j with
  | inl e =>
    by_cases he : e ∈ D
    · simp only [flowWeights, Sum.elim_inl, if_pos he]
      have := le_max_right (r e) 0
      omega
    · simp only [flowWeights, Sum.elim_inl, if_neg he]
      exact abs_pos.2 (hr e he)
  | inr e =>
    simp only [flowWeights, Sum.elim_inr]
    have := le_max_right (-r e.val) 0
    omega

theorem combine_flowWeights (D : Set E) (r : E → ℤ) :
    combineCoefficients D (fun e => (r e).sign) (flowWeights D r) = r := by
  classical
  funext e
  by_cases he : e ∈ D
  · simp only [combineCoefficients, flowWeights, Sum.elim_inl, Sum.elim_inr,
      leftSign, secondCoefficient, if_pos he, dif_pos he, mul_one]
    omega
  · simp only [combineCoefficients, flowWeights, Sum.elim_inl,
      leftSign, secondCoefficient, if_neg he, dif_neg he, sub_zero]
    exact sign_abs_mul (r e)

/-- The strictly positive integral relation written explicitly in Proposition 2.3. -/
theorem flowWeights_relation (u : E → Lattice n) (D : Set E) (r : E → ℤ)
    (hr : r ∈ relations u) :
    flowWeights D r ∈ relations (orientedFamily u D (fun e => (r e).sign)) := by
  rw [mem_relations_iff, sum_orientedFamily, combine_flowWeights]
  exact hr

@[simp] theorem embed_int_smul (a : ℤ) (x : Lattice n) :
    embed (a • x) = (a : ℝ) • embed x := by
  ext i
  simp [embed, Pi.smul_apply, smul_eq_mul]

/-- Orienting a reference family and doubling selected lines preserves its real span. -/
theorem orientedFamily_spans (u : E → Lattice n) (D : Set E) (ε : E → ℤ)
    (hε : ∀ e, e ∉ D → ε e ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) :
    Submodule.span ℝ (Set.range (fun j => embed (orientedFamily u D ε j))) = ⊤ := by
  classical
  let P := Submodule.span ℝ (Set.range (fun j => embed (orientedFamily u D ε j)))
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.2
  rintro x ⟨e, rfl⟩
  have hleft : embed (orientedFamily u D ε (Sum.inl e)) ∈ P :=
    Submodule.subset_span ⟨Sum.inl e, rfl⟩
  change embed (leftSign D ε e • u e) ∈ P at hleft
  rw [embed_int_smul] at hleft
  have hne : leftSign D ε e ≠ 0 := by
    by_cases he : e ∈ D
    · simp [leftSign, he]
    · simpa [leftSign, he] using hε e he
  exact (P.smul_mem_iff (by exact_mod_cast hne : (leftSign D ε e : ℝ) ≠ 0)).1 hleft

/-- Forward geometric assertion of Proposition 2.3: an integral relation nonzero on
undoubled labels produces a ray system whose actual real conic hull is the entire space. -/
theorem proposition_2_3_positive_span (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (D : Set E) (r : E → ℤ) (hr : r ∈ relations u)
    (hne : ∀ e, e ∉ D → r e ≠ 0) :
    PointedCone.hull ℝ
      (Set.range (fun j => embed (orientedFamily u D (fun e => (r e).sign) j))) = ⊤ := by
  apply (hull_top_iff_span_and_positive_integer_relation _).2
  refine ⟨orientedFamily_spans u D _ ?_ hspan,
    flowWeights D r, flowWeights_relation u D r hr, flowWeights_positive D r hne⟩
  intro e he
  have ha := abs_sign_eq_one (hne e he)
  intro hz
  rw [hz, abs_zero] at ha
  omega

/-- Changing column signs and duplicating columns preserves the maximal-minor definition
of uniform unimodularity. -/
theorem uniform_signed_family (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    {F : Type*} (source : F → E) (sign : F → ℤ) (hs : ∀ j, |sign j| = 1) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun j => sign j • u (source j)) := by
  intro a
  change |(Pi.basisFun ℤ (Fin n)).det
    (fun i => sign (a i) • u (source (a i)))| ≤ 1
  rw [AlternatingMap.map_smul_univ, smul_eq_mul, abs_mul, Finset.abs_prod]
  simp_rw [hs]
  simp only [Finset.prod_const_one, one_mul]
  exact hu (source ∘ a)

/-- The output of the flow construction retains uniform unimodularity in all ranks. -/
theorem orientedFamily_uniform (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (D : Set E) (ε : E → ℤ) (hε : ∀ e, e ∉ D → |ε e| = 1) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (orientedFamily u D ε) := by
  let source : OrientedIndex D → E := Sum.elim id Subtype.val
  let sign : OrientedIndex D → ℤ := Sum.elim (leftSign D ε) (fun _ => -1)
  have hs : ∀ j, |sign j| = 1 := by
    intro j
    cases j with
    | inl e =>
      by_cases he : e ∈ D
      · simp [sign, leftSign, he]
      · simpa [sign, leftSign, he] using hε e he
    | inr e => simp [sign]
  have heq : orientedFamily u D ε = fun j => sign j • u (source j) := by
    funext j
    cases j <;> simp [orientedFamily, source, sign]
  rw [heq]
  exact uniform_signed_family u hu source sign hs

/-- A positive orientation is recovered from an integral flow with exactly its prescribed
signs on undoubled lines. The coefficients on doubled lines remain unrestricted. -/
theorem integral_flow_of_positive_orientation (u : E → Lattice n)
    (D : Set E) (ε : E → ℤ) (hε : ∀ e, e ∉ D → |ε e| = 1)
    (hpos : PointedCone.hull ℝ
      (Set.range (fun j => embed (orientedFamily u D ε j))) = ⊤) :
    ∃ r ∈ relations u, ∀ e, e ∉ D → r e ≠ 0 ∧ (r e).sign = ε e := by
  obtain ⟨_, p, hp, hp0⟩ := (hull_top_iff_span_and_positive_integer_relation _).1 hpos
  let r := combineCoefficients D ε p
  refine ⟨r, ?_, ?_⟩
  · rw [mem_relations_iff]
    rw [← sum_orientedFamily]
    exact hp
  · intro e he
    have hr : r e = p (Sum.inl e) * ε e := by
      simp [r, combineCoefficients, leftSign, secondCoefficient, he]
    have heps : ε e = 1 ∨ ε e = -1 :=
      abs_eq_abs.1 (by simpa using hε e he : |ε e| = |(1 : ℤ)|)
    rcases heps with heps | heps
    · rw [hr, heps, mul_one]
      exact ⟨ne_of_gt (hp0 (Sum.inl e)), Int.sign_eq_one_of_pos (hp0 (Sum.inl e))⟩
    · rw [hr, heps, mul_neg_one]
      exact ⟨neg_ne_zero.2 (ne_of_gt (hp0 (Sum.inl e))),
        Int.sign_eq_neg_one_of_neg (Int.neg_neg_of_pos (hp0 (Sum.inl e)))⟩

/-- Exact orientation characterization on a fixed reference line configuration. These are
the two geometric directions of Proposition 2.3, stated without matroid terminology. -/
theorem proposition_2_3_orientation_iff (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (D : Set E) (ε : E → ℤ) (hε : ∀ e, e ∉ D → |ε e| = 1) :
    PointedCone.hull ℝ (Set.range (fun j => embed (orientedFamily u D ε j))) = ⊤ ↔
      ∃ r ∈ relations u, ∀ e, e ∉ D → r e ≠ 0 ∧ (r e).sign = ε e := by
  constructor
  · exact integral_flow_of_positive_orientation u D ε hε
  · rintro ⟨r, hr, hsign⟩
    have heq : orientedFamily u D ε = orientedFamily u D (fun e => (r e).sign) := by
      funext j
      cases j with
      | inl e =>
        by_cases he : e ∈ D
        · simp [orientedFamily, leftSign, he]
        · simp [orientedFamily, leftSign, he, (hsign e he).2]
      | inr e => rfl
    rw [heq]
    exact proposition_2_3_positive_span u hspan D r hr (fun e he => (hsign e he).1)

/-- Full fixed-configuration existence statement: a uniformly unimodular spanning family
admits a positively spanning signed orientation with precisely the prescribed doubled
labels if and only if every coloop is doubled. -/
theorem proposition_2_3 (u : E → Lattice n)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) (D : Set E) :
    (∃ r ∈ relations u, (∀ e, e ∉ D → r e ≠ 0) ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (orientedFamily u D (fun e => (r e).sign)) ∧
      PointedCone.hull ℝ
        (Set.range (fun j => embed (orientedFamily u D (fun e => (r e).sign) j))) = ⊤) ↔
      ∀ e, IsColoop u e → e ∈ D := by
  constructor
  · rintro ⟨r, hr, hne, _, _⟩
    exact (proposition_2_3_integral_relation u hu hspan D).1 ⟨r, hr, hne⟩
  · intro h
    obtain ⟨r, hr, hne⟩ := (proposition_2_3_integral_relation u hu hspan D).2 h
    exact ⟨r, hr, hne,
      orientedFamily_uniform u hu D _ (fun e he => abs_sign_eq_one (hne e he)),
      proposition_2_3_positive_span u hspan D r hr hne⟩

/-- The labelled construction has precisely the ray-vector set displayed in (2.2). -/
theorem range_orientedFamily (u : E → Lattice n) (D : Set E) (r : E → ℤ) :
    Set.range (orientedFamily u D (fun e => (r e).sign)) =
      {x | (∃ e, e ∉ D ∧ x = (r e).sign • u e) ∨
        ∃ e, e ∈ D ∧ (x = u e ∨ x = -u e)} := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    cases j with
    | inl e =>
      by_cases he : e ∈ D
      · exact Or.inr ⟨e, he, Or.inl (by simp [orientedFamily, leftSign, he])⟩
      · exact Or.inl ⟨e, he, by simp [orientedFamily, leftSign, he]⟩
    | inr e =>
      exact Or.inr ⟨e.val, e.property, Or.inr rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl | rfl⟩)
    · exact ⟨Sum.inl e, by simp [orientedFamily, leftSign, he]⟩
    · exact ⟨Sum.inl e, by simp [orientedFamily, leftSign, he]⟩
    · exact ⟨Sum.inr ⟨e, he⟩, rfl⟩

theorem orientedFamily_nonzero (u : E → Lattice n) (hnz : ∀ e, u e ≠ 0)
    (D : Set E) (ε : E → ℤ) (hε : ∀ e, e ∉ D → |ε e| = 1) :
    ∀ j, orientedFamily u D ε j ≠ 0 := by
  intro j
  cases j with
  | inl e =>
    by_cases he : e ∈ D
    · simpa [orientedFamily, leftSign, he] using hnz e
    · have heps : ε e = 1 ∨ ε e = -1 :=
        abs_eq_abs.1 (by simpa using hε e he : |ε e| = |(1 : ℤ)|)
      rcases heps with heps | heps <;>
        simpa [orientedFamily, leftSign, he, heps] using hnz e
  | inr e => simpa [orientedFamily] using hnz e.val

/-- A complete recorded output of the flow construction: nonzero lattice vectors, uniform
unimodularity and genuine positive spanning. The displayed ray-set equality is
`range_orientedFamily`. -/
theorem flow_construction (u : E → Lattice n) (hnz : ∀ e, u e ≠ 0)
    (hu : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) u)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (D : Set E) (r : E → ℤ) (hr : r ∈ relations u)
    (hne : ∀ e, e ∉ D → r e ≠ 0) :
    (∀ j, orientedFamily u D (fun e => (r e).sign) j ≠ 0) ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (orientedFamily u D (fun e => (r e).sign)) ∧
      PointedCone.hull ℝ
        (Set.range (fun j => embed (orientedFamily u D (fun e => (r e).sign) j))) = ⊤ := by
  have hs : ∀ e, e ∉ D → |(r e).sign| = 1 := fun e he => abs_sign_eq_one (hne e he)
  exact ⟨orientedFamily_nonzero u hnz D _ hs, orientedFamily_uniform u hu D _ hs,
    proposition_2_3_positive_span u hspan D r hr hne⟩

end Unimodular.FlowOrientations

end

noncomputable section

namespace Unimodular.FlowOrientations

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- Every nonzero vector of a full uniformly unimodular configuration is part of an
actual basis of the entire lattice, not merely of a finite-index sublattice. -/
theorem exists_basis_containing (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    {x : Lattice n} (hx : x ∈ U) (hn : x ≠ 0) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∃ i, b i = x := by
  let a : Unit → U := fun _ => ⟨x, hx⟩
  have ha : LinearIndependent ℝ (fun j => embed (a j).val) := by
    apply linearIndependent_unique_iff.2
    intro hz
    exact hn (LatticeHull.embed_injective (hz.trans embed_zero.symm))
  obtain ⟨b, _, hb⟩ := LatticeHull.exists_lattice_basis_extension U hU hspan a ha
  obtain ⟨i, hi⟩ := hb ()
  exact ⟨b, i, hi⟩

theorem basis_vector_primitive (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    PrimitiveLatticeVector (b i) := by
  intro k z hz
  have h : (1 : ℤ) = k * b.repr z i := by
    have h := congrArg (fun w => b.repr w i) hz
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using h
  exact IsUnit.of_mul_eq_one (a := k) (b.repr z i) h.symm

theorem configuration_vector_primitive (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    {x : Lattice n} (hx : x ∈ U) (hn : x ≠ 0) : PrimitiveLatticeVector x := by
  obtain ⟨b, i, hi⟩ := exists_basis_containing U hU hspan hx hn
  rw [← hi]
  exact basis_vector_primitive b i

/-- Real proportionality between two nonzero configuration vectors is exactly equality
up to sign. This justifies simplifying by antipodal classes rather than by arbitrary
real rescalings. -/
theorem proportional_eq_or_neg (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    {x y : Lattice n} (hx : x ∈ U) (hy : y ∈ U) (hxn : x ≠ 0) (hyn : y ≠ 0)
    {t : ℝ} (he : embed y = t • embed x) : y = x ∨ y = -x := by
  obtain ⟨b, i, hi⟩ := exists_basis_containing U hU hspan hx hxn
  have ht : (b.repr y i : ℝ) = t := by
    have h := congrArg (fun z => realCoordinates b z i) he
    rw [realCoordinates_embed, ← hi, map_smul, realCoordinates_basis] at h
    simpa only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] using h
  have hyk : y = (b.repr y i) • x := by
    apply LatticeHull.embed_injective
    rw [embed_int_smul, ht]
    exact he
  have hk := configuration_vector_primitive U hU hspan hy hyn (b.repr y i) x hyk
  have hkabs := Int.isUnit_iff_abs_eq.1 hk
  rcases abs_eq_abs.1 (by simpa using hkabs : |b.repr y i| = |(1 : ℤ)|) with hk | hk
  · exact Or.inl (by simpa only [hk, one_smul] using hyk)
  · exact Or.inr (by simpa only [hk, neg_one_smul] using hyk)

/-- Equality of the two unoriented lattice directions. -/
def antipodalSetoid (U : Set (Lattice n)) : Setoid U where
  r x y := x.val = y.val ∨ x.val = -y.val
  iseqv := ⟨fun x => Or.inl rfl, by
    intro x y h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg]), by
    intro x y z hxy hyz
    rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (hxy.trans hyz)
    · exact Or.inr (hxy.trans (congrArg Neg.neg hyz))
    · exact Or.inl (by simpa only [hyz, neg_neg] using hxy)⟩

abbrev LineIndex (U : Set (Lattice n)) := Quotient (antipodalSetoid U)

noncomputable def referenceFamily (U : Set (Lattice n)) : LineIndex U → Lattice n :=
  fun q => q.out.val

noncomputable def doubledLines (U : Set (Lattice n)) : Set (LineIndex U) :=
  {q | -referenceFamily U q ∈ U}

theorem reference_mem (U : Set (Lattice n)) (q : LineIndex U) :
    referenceFamily U q ∈ U := q.out.property

theorem reference_eq_or_neg (U : Set (Lattice n)) (x : U) :
    referenceFamily U (Quotient.mk (antipodalSetoid U) x) = x.val ∨
      referenceFamily U (Quotient.mk (antipodalSetoid U) x) = -x.val :=
  Quotient.mk_out (s := antipodalSetoid U) x

/-- Each antipodal class occurs once; the construction adds its opposite precisely when
that opposite belongs to the original configuration. -/
theorem oriented_reference_range (U : Set (Lattice n)) :
    Set.range (orientedFamily (referenceFamily U) (doubledLines U) (fun _ => 1)) = U := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    cases j with
    | inl q => simpa [orientedFamily, leftSign] using reference_mem U q
    | inr q => exact q.property
  · intro hx
    let q : LineIndex U := Quotient.mk (antipodalSetoid U) ⟨x, hx⟩
    rcases reference_eq_or_neg U ⟨x, hx⟩ with he | he
    · exact ⟨Sum.inl q, by simpa [orientedFamily, leftSign, q] using he⟩
    · have hD : q ∈ doubledLines U := by
        change -referenceFamily U q ∈ U
        dsimp [q]
        rw [he, neg_neg]
        exact hx
      exact ⟨Sum.inr ⟨q, hD⟩, by simpa [orientedFamily, q, he]⟩

/-- The reference realization has no zero vector and no two proportional vectors. -/
theorem reference_simple (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤) (hnz : ∀ x ∈ U, x ≠ 0) :
    (∀ q, referenceFamily U q ≠ 0) ∧
      ∀ q r, (∃ t : ℝ, embed (referenceFamily U r) = t • embed (referenceFamily U q)) →
        q = r := by
  refine ⟨fun q => hnz _ (reference_mem U q), ?_⟩
  rintro q r ⟨t, ht⟩
  have he := proportional_eq_or_neg U hU hspan (reference_mem U q) (reference_mem U r)
    (hnz _ (reference_mem U q)) (hnz _ (reference_mem U r)) ht
  have hclass : (antipodalSetoid U).r r.out q.out := he
  exact (Quotient.out_equiv_out.1 hclass).symm

/-- Every finite integral positive ray configuration has a flow normal form on its
antipodal reference classes. Uniform unimodularity gives a simple, uniformly unimodular
reference realization. The separate regular-matroid decomposition theorem is not assumed
in this statement. -/
theorem positive_configuration_flow_normal_form (U : Set (Lattice n)) [Fintype U]
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hnz : ∀ x ∈ U, x ≠ 0) (hpos : PointedCone.hull ℝ (embed '' U) = ⊤) :
    let v := referenceFamily U
    let D := doubledLines U
    (∀ q, v q ≠ 0) ∧
      (∀ q r, (∃ t : ℝ, embed (v r) = t • embed (v q)) → q = r) ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) v ∧
      Submodule.span ℝ (Set.range (fun q => embed (v q))) = ⊤ ∧
      ∃ r ∈ relations v, (∀ q, q ∉ D → r q ≠ 0) ∧
        (∀ q, IsColoop v q → q ∈ D) ∧
        Set.range (orientedFamily v D (fun q => (r q).sign)) = U := by
  classical
  let v := referenceFamily U
  let D := doubledLines U
  have hfull : Submodule.span ℝ (embed '' U) = ⊤ := by
    apply top_unique
    intro x hx
    apply PointedCone.hull_le_span ℝ (embed '' U)
    rw [hpos]
    trivial
  have hsimp := reference_simple U hU hfull hnz
  have hv : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) v :=
    uniform_subfamily (fun x : U => x.val) hU v (fun q => ⟨q.out, rfl⟩)
  have hvspan : Submodule.span ℝ (Set.range (fun q => embed (v q))) = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply Submodule.span_le.2
    rintro x ⟨y, hy, rfl⟩
    change embed y ∈ Submodule.span ℝ (Set.range (fun q => embed (v q)))
    let q : LineIndex U := Quotient.mk (antipodalSetoid U) ⟨y, hy⟩
    have hq : embed (v q) ∈ Submodule.span ℝ (Set.range (fun q => embed (v q))) :=
      Submodule.subset_span ⟨q, rfl⟩
    rcases reference_eq_or_neg U ⟨y, hy⟩ with he | he
    · have he' : v q = y := he
      rw [he'] at hq
      exact hq
    · have hq' := (Submodule.span ℝ (Set.range (fun q => embed (v q)))).neg_mem hq
      have he' : v q = -y := he
      rw [he', embed_neg, neg_neg] at hq'
      exact hq'
  have horange : Set.range (fun j => embed (orientedFamily v D (fun _ => 1) j)) =
      embed '' U := by
    rw [Set.range_comp', oriented_reference_range]
  have hopos : PointedCone.hull ℝ
      (Set.range (fun j => embed (orientedFamily v D (fun _ => 1) j))) = ⊤ := by
    rw [horange]
    exact hpos
  obtain ⟨r, hr, hsign⟩ := integral_flow_of_positive_orientation v D (fun _ => 1)
    (fun _ _ => by norm_num) hopos
  have hne : ∀ q, q ∉ D → r q ≠ 0 := fun q hq => (hsign q hq).1
  have heq : orientedFamily v D (fun q => (r q).sign) =
      orientedFamily v D (fun _ => 1) := by
    funext j
    cases j with
    | inl q =>
      by_cases hq : q ∈ D
      · simp [orientedFamily, leftSign, hq]
      · simp [orientedFamily, leftSign, hq, (hsign q hq).2]
    | inr q => rfl
  refine ⟨hsimp.1, hsimp.2, hv, hvspan, r, hr, hne, ?_, ?_⟩
  · exact (proposition_2_3_integral_relation v hv hvspan D).1 ⟨r, hr, hne⟩
  · rw [heq]
    exact oriented_reference_range U

end Unimodular.FlowOrientations

end

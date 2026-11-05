module

public import PaperVerification.AlternatingFormsDuality
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The exact dimension contribution of two independent extra syzygies

The result is ordinary finite-dimensional rank-nullity. A checked injection
of the Koszul term together with two extra cycles into the full kernel
produces an integer lower bound for the genuine cokernel. No maximal-rank
assertion or Hilbert function is built into a definition.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

section LinearAlgebra

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]

/-- The two extra vectors are independent modulo the image of `ψ`.
The hypothesis is the literal relation in `B`, not a presumed dimension. -/
theorem cokernel_finrank_lower_of_two_extra_cycles
    (φ : B →ₗ[K] A) (ψ : C →ₗ[K] B)
    (hcomp : φ.comp ψ = 0) (hψ : Function.Injective ψ)
    (z₁ z₂ : B) (hz₁ : φ z₁ = 0) (hz₂ : φ z₂ = 0)
    (hrel : ∀ (c : C) (α β : K),
      ψ c + α • z₁ + β • z₂ = 0 → α = 0 ∧ β = 0) :
    (Module.finrank K A : ℤ) - (Module.finrank K B : ℤ) +
        (Module.finrank K C : ℤ) + 2 ≤
      (Module.finrank K (A ⧸ LinearMap.range φ) : ℤ) := by
  let e : C × (K × K) →ₗ[K] B :=
    { toFun x := ψ x.1 + x.2.1 • z₁ + x.2.2 • z₂
      map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]; abel
      map_smul' a x := by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
          smul_smul, RingHom.id_apply, smul_eq_mul] }
  have heker (x : C × (K × K)) : e x ∈ LinearMap.ker φ := by
    change φ (ψ x.1 + x.2.1 • z₁ + x.2.2 • z₂) = 0
    have hc : φ (ψ x.1) = 0 := LinearMap.congr_fun hcomp x.1
    simp only [map_add, map_smul, hc, hz₁, hz₂, smul_zero, add_zero]
  let e' : C × (K × K) →ₗ[K] LinearMap.ker φ := e.codRestrict _ heker
  have he : Function.Injective e' := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨c, α, β⟩ hx
    have hx' : ψ c + α • z₁ + β • z₂ = 0 := congrArg Subtype.val hx
    obtain ⟨hα, hβ⟩ := hrel c α β hx'
    have hc : c = 0 := hψ (by simpa only [hα, hβ, zero_smul, add_zero, map_zero] using hx')
    change (c, (α, β)) = (0, (0, 0))
    exact Prod.ext hc (Prod.ext hα hβ)
  have hdim : Module.finrank K C + 2 ≤ Module.finrank K (LinearMap.ker φ) := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_assoc] using
      (LinearMap.finrank_le_finrank_of_injective he)
  have hnull := φ.finrank_range_add_finrank_ker
  have hquot := (LinearMap.range φ).finrank_quotient_add_finrank
  omega

end LinearAlgebra

section ExteriorComplex

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The literal degree `q+4` relation map. -/
def exteriorRelationMapDegree (f g : ⋀[K]^2 M) (q : ℕ) :
    (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) →ₗ[K] ⋀[K]^(q+4) M where
  toFun x := ⟨(f : ExteriorAlgebra K M) * x.1 + (g : ExteriorAlgebra K M) * x.2, by
    apply Submodule.add_mem
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded f.property x.1.property
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded g.property x.2.property⟩
  map_add' x y := by apply Subtype.ext; simp only [Prod.fst_add, Prod.snd_add,
    AddMemClass.coe_add, mul_add]; abel
  map_smul' a x := by apply Subtype.ext; simp only [Prod.smul_fst, Prod.smul_snd,
    SetLike.val_smul, mul_smul_comm, smul_add, RingHom.id_apply]

/-- The actual Koszul syzygy `(Gh,-Fh)`, with its genuine degree. -/
def exteriorKoszulMapDegree (f g : ⋀[K]^2 M) (q : ℕ) :
    ⋀[K]^q M →ₗ[K] (⋀[K]^(q+2) M × ⋀[K]^(q+2) M) where
  toFun h :=
    (⟨(g : ExteriorAlgebra K M) * h, by
      simpa only [Nat.add_comm] using SetLike.mul_mem_graded g.property h.property⟩,
     ⟨-((f : ExteriorAlgebra K M) * h), by
      apply Submodule.neg_mem
      simpa only [Nat.add_comm] using SetLike.mul_mem_graded f.property h.property⟩)
  map_add' x y := by apply Prod.ext <;> apply Subtype.ext <;>
    simp only [AddMemClass.coe_add, mul_add, neg_add_rev, Prod.fst_add, Prod.snd_add,
      add_comm]
  map_smul' a x := by apply Prod.ext <;> apply Subtype.ext <;>
    simp only [SetLike.val_smul, mul_smul_comm, smul_neg, Prod.smul_fst,
      Prod.smul_snd, RingHom.id_apply]

theorem exteriorRelationMapDegree_comp (f g : ⋀[K]^2 M) (q : ℕ) :
    (exteriorRelationMapDegree f g q).comp (exteriorKoszulMapDegree f g q) = 0 := by
  apply LinearMap.ext
  intro h
  apply Subtype.ext
  change (f : ExteriorAlgebra K M) * ((g : ExteriorAlgebra K M) * h) +
    (g : ExteriorAlgebra K M) * (-((f : ExteriorAlgebra K M) * h)) = 0
  rw [mul_neg, ← mul_assoc, ← mul_assoc, (twoForm_commute f (g : ExteriorAlgebra K M)).eq]
  exact add_neg_cancel _

theorem exteriorKoszulMapDegree_injective (f g : ⋀[K]^2 M) (q : ℕ)
    (hF : ∀ h : ⋀[K]^q M, (f : ExteriorAlgebra K M) * h = 0 → h = 0) :
    Function.Injective (exteriorKoszulMapDegree f g q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro h hh
  have hx := congrArg (fun x : ⋀[K]^(q+2) M × ⋀[K]^(q+2) M =>
    (x.2 : ExteriorAlgebra K M)) hh
  change -((f : ExteriorAlgebra K M) * h) = 0 at hx
  exact hF h (neg_eq_zero.mp hx)

/-- The range is precisely the degree of the genuine two-generated ideal. -/
theorem exteriorRelationMapDegree_range (f g : ⋀[K]^2 M) (q : ℕ) :
    LinearMap.range (exteriorRelationMapDegree f g q) =
      exteriorDegreeRelations f g (q+4) := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩, rfl⟩
    change (f : ExteriorAlgebra K M) * a + (g : ExteriorAlgebra K M) * b ∈
      exteriorRelationIdeal f g
    apply Ideal.mem_span_pair.mpr
    refine ⟨(a : ExteriorAlgebra K M), (b : ExteriorAlgebra K M), ?_⟩
    rw [(twoForm_commute f a).eq, (twoForm_commute g b).eq]
  · intro hx
    let x' : ⋀[K]^(2+(q+2)) M := ⟨x.val, by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using x.property⟩
    have hx' : x' ∈ exteriorDegreeRelations f g (2+(q+2)) := hx
    rw [exteriorDegreeRelations_eq_images] at hx'
    obtain ⟨a, ⟨a', rfl⟩, b, ⟨b', rfl⟩, hab⟩ := Submodule.mem_sup.mp hx'
    refine ⟨(a',b'), ?_⟩
    apply Subtype.ext
    change (f : ExteriorAlgebra K M) * (a' : ExteriorAlgebra K M) +
      (g : ExteriorAlgebra K M) * (b' : ExteriorAlgebra K M) = x.val
    simpa only [AddMemClass.coe_add, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]
      using congrArg (fun z : ⋀[K]^(2+(q+2)) M => (z : ExteriorAlgebra K M)) hab


end ExteriorComplex

end PaperVerification.AlternatingForms

module

public import Papers.GraphicalZonotopes.Gluing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators
variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j, Fintype (K j)] [∀ j, Fintype (I j)] [∀ j, Fintype (X j)]
variable [DecidableEq J]
variable (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
variable (hmin : ∀ j b x, m j b ≤ M.response j b x (f j))
variable (hatt : ∀ j b, ∃ x, M.response j b x (f j) = m j b)
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j, 0 < lam j)
variable (hcone : Polyhedral.Nonnegative M.row (assemble z lam f))

include hmin hatt hlam hcone in
/-- At an arbitrary feasible glued point, every tight boundary row uses a
minimizer in every branch. It is not assumed that all boundary types are tight. -/
theorem tight_boundary_uses_minima (b : B) (x : ∀ j, X j)
    (ht : M.row (Sum.inr (b,x)) (assemble z lam f) = 0) :
    ∀ j, M.response j b (x j) (f j) = m j b := by
  classical
  choose xmin hxmin using fun j : J => hatt j b
  have hbase := hcone (Sum.inr (b,xmin))
  change 0 ≤ M.boundary z b + ∑ j, M.response j b (xmin j) (lam j • f j) at hbase
  simp only [map_smul, smul_eq_mul, hxmin] at hbase
  change M.boundary z b + ∑ j, M.response j b (x j) (lam j • f j) = 0 at ht
  simp only [map_smul, smul_eq_mul] at ht
  have hnn : ∀ j ∈ (univ : Finset J),
      0 ≤ lam j * (M.response j b (x j) (f j) - m j b) :=
    fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))
  have hsum : ∑ j, lam j * (M.response j b (x j) (f j) - m j b) = 0 := by
    have hsum0 := sum_nonneg hnn
    rw [show (∑ j, lam j * (M.response j b (x j) (f j) - m j b)) =
      (∑ j, lam j * M.response j b (x j) (f j)) - ∑ j, lam j * m j b by
        simp [mul_sub, sum_sub_distrib]] at hsum0 ⊢
    linarith
  have hterm := (sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro j
  exact sub_eq_zero.mp ((mul_eq_zero.mp (hterm j (mem_univ j))).resolve_left (ne_of_gt (hlam j)))

/-- Every solution of all aggregated boundary equations gives a true global
tight variation. Additional aggregated equations on nontight types are harmless;
they are counted in the upper bound exactly once each. -/
def capacityEmbedding : M.closedRelations m →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 y.1.2 f, by
    intro r hr
    rcases r with ⟨j,i⟩ | ⟨b,x⟩
    · change M.internal j i (lam j • f j) = 0 at hr
      rw [map_smul, smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (y.1.2 j • f j) = 0
      rw [map_smul, hi, smul_zero]
    · have hx := tight_boundary_uses_minima M f m hmin hatt z lam hlam hcone b x hr
      have hcl := (mem_closedRelations M m y.1.1 y.1.2).mp y.2 b
      change M.boundary y.1.1 b + ∑ j, M.response j b (x j) (y.1.2 j • f j) = 0
      simpa only [map_smul, smul_eq_mul, hx] using hcl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble, smul_smul,mul_assoc]

theorem capacityEmbedding_injective (hfinj : ∀ j, f j ≠ 0) :
    Function.Injective (capacityEmbedding M f m hmin hatt z lam hlam hcone) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j) he
    change x.1.2 j • f j = y.1.2 j • f j at h
    have hnonzero : ∃ k, f j k ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hfinj j (funext hn)
    obtain ⟨k,hk⟩ := hnonzero
    have hh := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

include hmin hatt hlam in
/-- The general separator-capacity inequality. Unlike positive-response gluing,
no private-kernel rigidity and no simultaneous boundary-closing condition are
assumed. Every nonzero private block is permitted to vary by its own scalar. -/
theorem separator_capacity (hfinj : ∀ j, f j ≠ 0)
    (hext : Polyhedral.ExtremeRay M.row (assemble z lam f)) :
    Fintype.card J ≤ Fintype.card B - Fintype.card D + 1 := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (capacityEmbedding_injective M f m hmin hatt z lam hlam hext.1 hfinj)
  rw [hext.tightKernel_eq_span, finrank_span_singleton hext.2.1] at hle
  have hnull := (M.closureLinear m).ker.finrank_quotient_add_finrank
  rw [(M.closureLinear m).quotKerEquivRange.finrank_eq,
    Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hnull
  have hrange := Submodule.finrank_le (M.closureLinear m).range
  rw [Module.finrank_fintype_fun_eq_card] at hrange
  change Module.finrank ℝ (M.closureLinear m).ker ≤ 1 at hle
  omega

/-- Adding a boundary lift to each branch changes responses by the boundary
slack image. The quotient response map is literally unchanged. -/
theorem relationLinear_boundary_lift (h : J → D → ℝ) :
    M.relationLinear (fun j b => m j b + M.boundary (h j) b) = M.relationLinear m := by
  apply LinearMap.ext
  intro c
  change (LinearMap.range M.boundary).mkQ
      (responseLinear (fun j b => m j b + M.boundary (h j) b) c) =
    (LinearMap.range M.boundary).mkQ (responseLinear m c)
  have he : responseLinear (fun j b => m j b + M.boundary (h j) b) c =
      responseLinear m c + M.boundary (∑ j, c j • h j) := by
    ext b
    simp [responseLinear, mul_add, sum_add_distrib, map_sum]
  rw [he, map_add]
  have hz : (LinearMap.range M.boundary).mkQ (M.boundary (∑ j, c j • h j)) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact ⟨_,rfl⟩
  rw [hz, add_zero]

end Gluing
end GraphicalZonotopes

module

public import Papers.GraphicalZonotopes.PolyhedralCone
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
An abstract finite-inequality version of positive response gluing. Internal rows
and all boundary choices are retained. The private hypothesis is the actual kernel
of internal zero rows and differences of minimizing boundary rows.
-/
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

abbrev Global (J : Type*) (K : J → Type*) (D : Type*) := (D → ℝ) × (∀ j, K j → ℝ)
abbrev Row (B J : Type*) (I X : J → Type*) := (Σ j, I j) ⊕ (B × (∀ j, X j))

structure Data (B J : Type*) (K : J → Type*) (D : Type*) (I X : J → Type*) where
  boundary : (D → ℝ) →ₗ[ℝ] (B → ℝ)
  internal : (j : J) → I j → (K j → ℝ) →ₗ[ℝ] ℝ
  response : (j : J) → B → X j → (K j → ℝ) →ₗ[ℝ] ℝ

def Data.row (M : Data B J K D I X) : Row B J I X → Global J K D →ₗ[ℝ] ℝ
  | Sum.inl ⟨j, i⟩ =>
    { toFun := fun y => M.internal j i (y.2 j)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  | Sum.inr (b, x) =>
    { toFun := fun y => M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j)
      map_add' := by intros; simp [Finset.sum_add_distrib]; ring
      map_smul' a y := by
        change M.boundary (a • y.1) b + (∑ j, M.response j b (x j) (a • y.2 j)) =
          a * (M.boundary y.1 b + ∑ j, M.response j b (x j) (y.2 j))
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        rw [mul_add, Finset.mul_sum] }

/-- The complete private equations at a branch point. -/
def Data.PrivateKernel (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
    (j : J) (g : K j → ℝ) : Prop :=
  (∀ i, M.internal j i (f j) = 0 → M.internal j i g = 0) ∧
    ∀ b x y, M.response j b x (f j) = m j b → M.response j b y (f j) = m j b →
      M.response j b x g = M.response j b y g

def Data.Closure (M : Data B J K D I X) (m : J → B → ℝ)
    (z : D → ℝ) (c : J → ℝ) : Prop :=
  ∀ b, M.boundary z b + ∑ j, c j * m j b = 0

def assemble (z : D → ℝ) (c : J → ℝ) (f : ∀ j, K j → ℝ) : Global J K D :=
  (z, fun j => c j • f j)

variable (M : Data B J K D I X) (f : ∀ j, K j → ℝ) (m : J → B → ℝ)
variable (hmin : ∀ j b x, m j b ≤ M.response j b x (f j))
variable (hatt : ∀ j b, ∃ x, M.response j b x (f j) = m j b)
variable (hinternal : ∀ j i, 0 ≤ M.internal j i (f j))
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j, 0 < lam j)
variable (hclose : M.Closure m z lam)

include hclose in
/-- The closing relation turns every boundary row into a sum of nonnegative
excesses above genuine conditional minima. -/
theorem row_boundary_eq_excess (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) =
      ∑ j, lam j * (M.response j b (x j) (f j) - m j b) := by
  have hc := hclose b
  simp only [Data.row, assemble, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, smul_eq_mul, Pi.smul_apply]
  simp only [mul_sub, sum_sub_distrib]
  linarith

include hmin hinternal hlam hclose in
theorem assembled_nonnegative : Polyhedral.Nonnegative M.row (assemble z lam f) := by
  intro r
  rcases r with ⟨j, i⟩ | ⟨b, x⟩
  · change 0 ≤ M.internal j i (lam j • f j)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hlam j).le (hinternal j i)
  · rw [row_boundary_eq_excess M f m z lam hclose]
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))

include hmin hlam hclose in
/-- With strictly positive branch scales, a boundary row is tight exactly when
each branch independently minimizes its contribution. -/
theorem boundary_tight_iff (b : B) (x : ∀ j, X j) :
    M.row (Sum.inr (b, x)) (assemble z lam f) = 0 ↔
      ∀ j, M.response j b (x j) (f j) = m j b := by
  rw [row_boundary_eq_excess M f m z lam hclose]
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ lam j * (M.response j b (x j) (f j) - m j b) :=
    fun j _ => mul_nonneg (hlam j).le (sub_nonneg.mpr (hmin j b (x j)))
  rw [sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h j
    have hj := h j (mem_univ j)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left (ne_of_gt (hlam j)))
  · intro h j hj
    rw [h j, sub_self, mul_zero]

/-- Varying only one branch choice isolates exactly that branch's response
change. This uses every global boundary row, not a selected submatrix. -/
theorem row_boundary_update_difference (g : Global J K D) (b : B) (x : ∀ j, X j)
    (j : J) (a a' : X j) :
    M.row (Sum.inr (b, Function.update x j a)) g -
      M.row (Sum.inr (b, Function.update x j a')) g =
        M.response j b a (g.2 j) - M.response j b a' (g.2 j) := by
  classical
  simp only [Data.row, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a k) (g.2 k)) -
      (M.boundary g.1 b + ∑ k, M.response k b (Function.update x j a' k) (g.2 k)) =
        ∑ k, (M.response k b (Function.update x j a k) (g.2 k) -
          M.response k b (Function.update x j a' k) (g.2 k)) by rw [sum_sub_distrib]; ring]
  rw [sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [Function.update_of_ne hkj]
  · simp

include hmin hatt hlam hclose in
/-- Every branch's complete private equations are inherited from the complete
global tight kernel. -/
theorem privateKernel_of_global {g : Global J K D}
    (hg : g ∈ Polyhedral.tightKernel M.row (assemble z lam f)) (j : J) :
    M.PrivateKernel f m j (g.2 j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i hi
    have hrow : M.row (Sum.inl ⟨j, i⟩) (assemble z lam f) = 0 := by
      change M.internal j i (lam j • f j) = 0
      rw [map_smul, hi, smul_zero]
    exact hg _ hrow
  · intro b a a' ha ha'
    choose x hx using fun k : J => hatt k b
    have hx1 : ∀ k, M.response k b (Function.update x j a k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha
      · simpa [Function.update_of_ne hkj] using hx k
    have hx2 : ∀ k, M.response k b (Function.update x j a' k) (f k) = m k b := by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using ha'
      · simpa [Function.update_of_ne hkj] using hx k
    have h1 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx1)
    have h2 := hg _ ((boundary_tight_iff M f m hmin z lam hlam hclose b _).mpr hx2)
    have hdiff := row_boundary_update_difference M g b x j a a'
    rw [h1, h2] at hdiff
    linarith

variable (hprivate : ∀ j g, M.PrivateKernel f m j g → ∃ c : ℝ, g = c • f j)

include hmin hatt hlam hclose hprivate in
/-- Exact reconstruction of the complete tight kernel by branch scales and
boundary closure, including all boundary and all unused private coordinates. -/
theorem tightKernel_iff {g : Global J K D} :
    g ∈ Polyhedral.tightKernel M.row (assemble z lam f) ↔
      ∃ c : J → ℝ, (∀ j, g.2 j = c j • f j) ∧ M.Closure m g.1 c := by
  constructor
  · intro hg
    have hsc : ∀ j, ∃ c : ℝ, g.2 j = c • f j :=
      fun j => hprivate j (g.2 j) (privateKernel_of_global M f m hmin hatt z lam hlam hclose hg j)
    choose c hc using hsc
    refine ⟨c, hc, ?_⟩
    intro b
    choose x hx using fun j : J => hatt j b
    have ht := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mpr hx
    have hgzero := hg _ ht
    change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0 at hgzero
    simpa only [hc, map_smul, smul_eq_mul, hx] using hgzero
  · rintro ⟨c, hc, hcl⟩ r hr
    rcases r with ⟨j, i⟩ | ⟨b, x⟩
    · change M.internal j i (lam j • f j) = 0 at hr
      rw [map_smul, smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (g.2 j) = 0
      rw [hc j, map_smul, hi, smul_zero]
    · have hx := (boundary_tight_iff M f m hmin z lam hlam hclose b x).mp hr
      change M.boundary g.1 b + ∑ j, M.response j b (x j) (g.2 j) = 0
      simpa only [hc, map_smul, smul_eq_mul, hx] using hcl b


def responseLinear (m : J → B → ℝ) : (J → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun c := fun b => ∑ j, c j * m j b
  map_add' c d := by ext b; simp [add_mul, sum_add_distrib]
  map_smul' a c := by ext b; simp [mul_assoc, mul_sum]

def Data.closureLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    ((D → ℝ) × (J → ℝ)) →ₗ[ℝ] (B → ℝ) where
  toFun y := M.boundary y.1 + responseLinear m y.2
  map_add' x y := by simp; abel
  map_smul' a x := by simp [smul_add]

def Data.closedRelations (M : Data B J K D I X) (m : J → B → ℝ) :
    Submodule ℝ ((D → ℝ) × (J → ℝ)) := LinearMap.ker (M.closureLinear m)

@[simp] theorem mem_closedRelations (w : D → ℝ) (c : J → ℝ) :
    (w, c) ∈ M.closedRelations m ↔ M.Closure m w c := by
  simp only [Data.closedRelations, LinearMap.mem_ker, Data.closureLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Data.Closure, responseLinear, Pi.add_apply,
    funext_iff, Pi.zero_apply]

def Data.relationLinear (M : Data B J K D I X) (m : J → B → ℝ) :
    (J → ℝ) →ₗ[ℝ] ((B → ℝ) ⧸ LinearMap.range M.boundary) :=
  (LinearMap.range M.boundary).mkQ ∘ₗ responseLinear m

theorem closure_mem_relationKernel {w : D → ℝ} {c : J → ℝ}
    (hc : M.Closure m w c) : c ∈ LinearMap.ker (M.relationLinear m) := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  refine ⟨-w, ?_⟩
  ext b
  have h := hc b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk]
  linarith

theorem exists_closure_of_relationKernel {c : J → ℝ}
    (hc : c ∈ LinearMap.ker (M.relationLinear m)) : ∃ w, M.Closure m w c := by
  change (LinearMap.range M.boundary).mkQ (responseLinear m c) = 0 at hc
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨-w, ?_⟩
  intro b
  have h := congrFun hw b
  simp only [map_neg, Pi.neg_apply, responseLinear, LinearMap.coe_mk, AddHom.coe_mk] at h ⊢
  linarith

variable (hfinj : ∀ j, f j ≠ 0)

def closedToTight : M.closedRelations m →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 y.1.2 f,
    (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mpr
      ⟨y.1.2, fun _ => rfl, (mem_closedRelations M m _ _).mp y.2⟩⟩
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
      simp [assemble, smul_smul, mul_assoc]

include hfinj in
theorem closedToTight_injective : Function.Injective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
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
    obtain ⟨k, hk⟩ := hnonzero
    have hh := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

theorem closedToTight_surjective : Function.Surjective
    (closedToTight M f m hmin hatt z lam hlam hclose hprivate) := by
  intro g
  obtain ⟨c, hc, hcl⟩ := (tightKernel_iff M f m hmin hatt z lam hlam hclose hprivate).mp g.2
  refine ⟨⟨(g.1.1, c), (mem_closedRelations M m _ _).mpr hcl⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    exact (hc j).symm

def closedTightEquiv : M.closedRelations m ≃ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) :=
  LinearEquiv.ofBijective (closedToTight M f m hmin hatt z lam hlam hclose hprivate)
    ⟨closedToTight_injective M f m hmin hatt z lam hlam hclose hprivate hfinj,
      closedToTight_surjective M f m hmin hatt z lam hlam hclose hprivate⟩

variable (hboundary : Function.Injective M.boundary)

def closedToRelation : M.closedRelations m →ₗ[ℝ] LinearMap.ker (M.relationLinear m) where
  toFun y := ⟨y.1.2, closure_mem_relationKernel M m ((mem_closedRelations M m _ _).mp y.2)⟩
  map_add' x y := rfl
  map_smul' a x := rfl

include hboundary in
theorem closedToRelation_injective : Function.Injective (closedToRelation M m) := by
  intro x y hxy
  have hc : x.1.2 = y.1.2 := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · apply hboundary
    ext b
    have hx := ((mem_closedRelations M m _ _).mp x.2) b
    have hy := ((mem_closedRelations M m _ _).mp y.2) b
    rw [hc] at hx
    linarith
  · exact hc

theorem closedToRelation_surjective : Function.Surjective (closedToRelation M m) := by
  intro c
  obtain ⟨w, hw⟩ := exists_closure_of_relationKernel M m c.2
  exact ⟨⟨(w, c.1), (mem_closedRelations M m _ _).mpr hw⟩, rfl⟩

def closedRelationEquiv : M.closedRelations m ≃ₗ[ℝ] LinearMap.ker (M.relationLinear m) :=
  LinearEquiv.ofBijective (closedToRelation M m)
    ⟨closedToRelation_injective M m hboundary, closedToRelation_surjective M m⟩

/-- The exact linear equivalence asserted by response gluing: every global tight
variation corresponds to exactly one relation among branch response classes. -/
def tightRelationEquiv : Polyhedral.tightKernel M.row (assemble z lam f) ≃ₗ[ℝ]
    LinearMap.ker (M.relationLinear m) :=
  (closedTightEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj).symm.trans
    (closedRelationEquiv M m hboundary)

include hmin hatt hlam hclose hprivate hfinj hboundary in
/-- The dimension assertion holds for the complete tight kernel, including all
rows, with the boundary quotient and branch scales explicitly constructed. -/
theorem tightKernel_finrank_eq_relationKernel :
    Module.finrank ℝ (Polyhedral.tightKernel M.row (assemble z lam f)) =
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) :=
  (tightRelationEquiv M f m hmin hatt z lam hlam hclose hprivate hfinj hboundary).finrank_eq


include hlam hfinj in
theorem assemble_ne_zero [Nonempty J] : assemble z lam f ≠ 0 := by
  intro he
  obtain ⟨j⟩ := ‹Nonempty J›
  have h := congrArg (fun g : Global J K D => g.2 j) he
  change lam j • f j = 0 at h
  exact hfinj j ((smul_eq_zero.mp h).resolve_left (ne_of_gt (hlam j)))

include hmin hatt hinternal hlam hclose hprivate hfinj hboundary in
/-- The extremality equivalence in the positive response gluing theorem. The
finite inequality cone is required to be pointed, as the normalized graphical
cone is by its proved zero-elemental-difference criterion. -/
theorem extreme_iff_relation_finrank_one
    (hpointed : Polyhedral.Pointed M.row) :
    Polyhedral.ExtremeRay M.row (assemble z lam f) ↔
      Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1 := by
  classical
  by_cases hJ : Nonempty J
  · letI := hJ
    have hn := assemble_ne_zero f z lam hlam hfinj
    have hdim := tightKernel_finrank_eq_relationKernel M f m hmin hatt z lam hlam hclose
      hprivate hfinj hboundary
    constructor
    · intro he
      rw [← hdim, he.tightKernel_eq_span]
      exact finrank_span_singleton hn
    · intro hd
      apply Polyhedral.extremeRay_of_tightKernel hpointed
        (assembled_nonnegative M f m hmin hinternal z lam hlam hclose) hn
      exact eq_span_singleton_of_mem_of_finrank_eq_one (hdim.trans hd)
        (Polyhedral.self_mem_tightKernel M.row (assemble z lam f)) hn
  · haveI : IsEmpty J := not_nonempty_iff.mp hJ
    have hz0 : z = 0 := by
      apply hboundary
      ext b
      have h := hclose b
      simpa using h
    have hp0 : assemble z lam f = 0 := by
      apply Prod.ext
      · exact hz0
      · funext j
        exact isEmptyElim j
    have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_of_isEmpty] at hk
    constructor
    · intro he
      exact False.elim (he.2.1 hp0)
    · intro hd
      omega

include hlam hclose in
/-- In the extreme case the relation line is exactly the line through the
strictly positive vector of the construction. -/
theorem relationKernel_eq_span_scales
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    LinearMap.ker (M.relationLinear m) = Submodule.span ℝ {lam} := by
  have hmem := closure_mem_relationKernel M m hclose
  have hk := Submodule.finrank_le (LinearMap.ker (M.relationLinear m))
  rw [hd, Module.finrank_fintype_fun_eq_card] at hk
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hne : lam ≠ 0 := by
    intro h
    obtain ⟨j⟩ := ‹Nonempty J›
    have hp := hlam j
    rw [h] at hp
    simp at hp
  exact eq_span_singleton_of_mem_of_finrank_eq_one hd hmem hne

include hboundary in
/-- The sharp universal branch-count bound follows from the dimension of the
boundary response quotient, with its boundary-coordinate subtraction justified
by injectivity of the boundary slack map. -/
theorem branch_count_le_capacity
    (hd : Module.finrank ℝ (LinearMap.ker (M.relationLinear m)) = 1) :
    Fintype.card J ≤ Fintype.card B - Fintype.card D + 1 := by
  have hrn := (LinearMap.ker (M.relationLinear m)).finrank_quotient_add_finrank
  rw [(M.relationLinear m).quotKerEquivRange.finrank_eq, hd,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hrle := Submodule.finrank_le (LinearMap.range (M.relationLinear m))
  have hquot := (LinearMap.range M.boundary).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hboundary, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hquot
  omega

end Gluing
end GraphicalZonotopes

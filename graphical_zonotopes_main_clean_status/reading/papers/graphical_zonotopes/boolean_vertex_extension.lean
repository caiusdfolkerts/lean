module

public import Papers.GraphicalZonotopes.BookPositiveCircuit
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingDirections
public import Papers.GraphicalZonotopes.ConnectedDimension

/-! # Attaching a single Boolean private vertex

This operation retains the original set function as its restriction to the
old vertices. A single tight old-edge equation identifies the old and new
scales, giving an economical extension of the ten-vertex ray of Section 8.2.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Vertex (V : Type*) := V ⊕ Fin 1

def append (z F : SetFunction V) : SetFunction (Vertex V) :=
  assembled z (fun _ : Fin 1 => F) (fun _ => 1)

@[simp] theorem append_at_hubs (z F : SetFunction V) (S : Finset V) :
    append z F (hubSet S) = z S := by
  exact assembled_at_hubs z (fun _ : Fin 1 => F) (fun _ => 1) S

@[simp] theorem append_at_new (z F : SetFunction V) (S : Finset V) :
    append z F (insert (Sum.inr 0) (hubSet S)) = z S + F S := by
  simpa only [append,one_mul] using
    assembled_at_one_outer z (fun _ : Fin 1 => F) (fun _ => 1) 0 S

theorem append_normalized {z F : SetFunction V}
    (hz : TranslationNormalized z) (hF : IsMonotoneBoolean F) :
    TranslationNormalized (append z F) :=
  assembled_normalized hz _ (fun _ => hF) _

theorem append_delta_old (z F : SetFunction V) (u v : V) (A : Finset (Vertex V)) :
    delta (append z F) (Sum.inl u) (Sum.inl v) A =
      delta z u v (hubs A) + if Sum.inr 0 ∈ A then delta F u v (hubs A) else 0 := by
  rw [append,delta_assembled_hubs]
  simp

theorem append_delta_new (z F : SetFunction V) (u : V)
    (A : Finset (Vertex V)) (hw : Sum.inr 0 ∉ A) :
    delta (append z F) (Sum.inl u) (Sum.inr 0) A =
      F (insert u (hubs A))-F (hubs A) := by
  rw [append,delta_assembled_spoke _ _ _ _ _ _ hw,one_mul]

/-- The two old-vertex slices and monotonicity of the new marginal are
exactly the elemental supermodularity conditions for a single new vertex. -/
theorem append_supermodular {z F : SetFunction V} (hz : Supermodular z)
    (hF : Monotone F) (hplus : Supermodular (z+F)) :
    Supermodular (append z F) := by
  apply ElementallyNonnegative.supermodular
  intro x y hxy A hx hy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u ≠ v := fun he => hxy (congrArg Sum.inl he)
      have hu : u ∉ hubs A := by simpa using hx
      have hv : v ∉ hubs A := by simpa using hy
      rw [append_delta_old]
      split_ifs with hw
      · simpa only [delta_add] using hplus.elemental u v huv (hubs A) hu hv
      · simpa only [add_zero] using hz.elemental u v huv (hubs A) hu hv
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [append_delta_new _ _ _ _ hy]
      exact sub_nonneg.mpr (hF (subset_insert _ _))
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      rw [delta_comm,append_delta_new _ _ _ _ hx]
      exact sub_nonneg.mpr (hF (subset_insert _ _))
    | inr j =>
      exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

theorem boundarySlice_supermodular {f : SetFunction (Vertex V)}
    (hf : Supermodular f) : Supermodular (boundarySlice f) := by
  intro A B
  simpa only [boundarySlice,hubSet,map_union,map_inter] using hf (hubSet A) (hubSet B)

/-- A strict old response canceled by the Boolean marginal fixes the new
private scale. The proof quantifies over every actual cone decomposition. -/
theorem append_extreme {z F : SetFunction V} (hz : ExtremeSupermodular z)
    (hF : IsMonotoneBoolean F) (hplus : Supermodular (z+F))
    (hcontact : ∃ u v : V, u ≠ v ∧ ∃ S : Finset V,
      u ∉ S ∧ v ∉ S ∧ delta z u v S = 1 ∧ delta F u v S = -1) :
    ExtremeSupermodular (append z F) := by
  have hn := append_normalized hz.1 hF
  have hs := append_supermodular hz.2.1 hF.monotone hplus
  have hne : append z F ≠ 0 := by
    intro he
    apply hz.2.2.1
    funext S
    have h := congrFun he (hubSet S)
    simpa only [append_at_hubs,Pi.zero_apply] using h
  refine ⟨hn,hs,hne,?_⟩
  intro f g hfn hgn hfs hgs he
  have hsum : boundarySlice f + boundarySlice g = z := by
    funext S
    have h := congrFun he (hubSet S)
    simpa only [Pi.add_apply,append_at_hubs,boundarySlice] using h
  obtain ⟨a,ha,hfa⟩ := hz.2.2.2 (boundarySlice f) (boundarySlice g)
    (boundarySlice_normalized hfn) (boundarySlice_normalized hgn)
    (boundarySlice_supermodular hfs) (boundarySlice_supermodular hgs) hsum
  have ht : ∀ u v, u ≠ v → ∀ A, u ∉ A → v ∉ A →
      delta (append z F) u v A = 0 → delta f u v A = 0 := by
    intro u v huv A hu hv hzero
    have hf := hfs.elemental u v huv A hu hv
    have hg := hgs.elemental u v huv A hu hv
    rw [← he,delta_add] at hzero
    linarith
  let b : Fin 1 → ℝ := fun j => privateSlice f j univ
  have hparts : ∀ j : Fin 1, privateSlice f j = b j • F :=
    fun j => privateSlice_scalar_of_spokeZeros (fun _ => hF) hfn ht j
  have houter : OuterZero f := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  have hrep := eq_assembled_of_privateSlices houter (fun _ : Fin 1 => F) b hparts
  obtain ⟨u,v,huv,S,hu,hv,hzrow,hFrow⟩ := hcontact
  let A : Finset (Vertex V) := insert (Sum.inr 0) (hubSet S)
  have huA : Sum.inl u ∉ A := by simpa [A] using hu
  have hvA : Sum.inl v ∉ A := by simpa [A] using hv
  have hzA : delta (append z F) (Sum.inl u) (Sum.inl v) A = 0 := by
    rw [append_delta_old]
    simp only [A,hubs_insert_outer,hubs_hubSet,mem_insert_self,ite_true,hzrow,hFrow]
    norm_num
  have hfA := ht (Sum.inl u) (Sum.inl v)
    (fun h => huv (Sum.inl_injective h)) A huA hvA hzA
  rw [hrep,hfa,delta_assembled_hubs,delta_smul] at hfA
  have hab : b 0 = a := by
    simp only [A,hubs_insert_outer,hubs_hubSet,hzrow,hFrow,mul_one,
      Fin.sum_univ_one,mem_insert_self,ite_true,mul_neg_one] at hfA
    linarith
  refine ⟨a,ha,?_⟩
  have hb : b = a • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simp [hj,hab]
  rw [hrep,hfa,hb,assembled_smul]
  rfl

/-- The old slack bound rises by at most one. This will give the exact
`n-6` dilation after starting with the ten-vertex bound four. -/
theorem append_delta_upper {z F : SetFunction V} (hF : IsMonotoneBoolean F)
    {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ M) :
    ∀ u v : Vertex V, u ≠ v → ∀ A, u ∉ A → v ∉ A →
      delta (append z F) u v A ≤ M+1 := by
  intro x y hxy A hx hy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have h := hz u v (fun he => hxy (congrArg Sum.inl he)) (hubs A)
        (by simpa using hx) (by simpa using hy)
      rw [append_delta_old]
      split_ifs
      · rcases delta_values hF u v (hubs A) with hh | hh | hh <;> rw [hh] <;> linarith
      · linarith
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [append_delta_new _ _ _ _ hy]
      rcases cover_values hF u (hubs A) with hh | hh <;> rw [hh] <;> linarith
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      rw [delta_comm,append_delta_new _ _ _ _ hx]
      rcases cover_values hF v (hubs A) with hh | hh <;> rw [hh] <;> linarith
    | inr j =>
      exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

end BooleanVertexExtension
end GraphicalZonotopes

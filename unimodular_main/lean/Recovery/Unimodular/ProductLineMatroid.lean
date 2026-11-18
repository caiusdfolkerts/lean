module

public import Recovery.Unimodular.ProductVectorMatroid
public import Recovery.Unimodular.ProductParallelComponents

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set
open scoped Matroid

namespace Unimodular.LineMatroid

variable {K E F V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Per-label multiplication by actual units and identification of repeated
labels produce the ordinary matroid comap, with its full independence rule. -/
theorem ofFamily_eq_comap_of_units (v : E → V) (w : F → V) (f : E → F)
    (a : E → Kˣ) (ha : ∀ e, a e • v e = w (f e)) :
    VectorMatroid.ofFamily (K := K) v =
      (VectorMatroid.ofFamily (K := K) w).comap f := by
  apply Matroid.ext_indep (by simp)
  intro I _
  rw [VectorMatroid.ofFamily_indep, Matroid.comap_indep_iff,
    VectorMatroid.ofFamily_indep]
  have hs : LinearIndepOn K (w ∘ f) I ↔ LinearIndepOn K v I := by
    change LinearIndependent K (fun e : I => w (f e.val)) ↔
      LinearIndependent K (fun e : I => v e.val)
    have he : (fun e : I => w (f e.val)) =
        (fun e : I => a e.val) • (fun e : I => v e.val) := by
      funext e
      exact (ha e.val).symm
    rw [he, LinearIndependent.units_smul_iff]
  constructor
  · intro hi
    have hc := hs.mpr hi
    refine ⟨hc.image_of_comp f w, ?_⟩
    intro e he d hd hed
    exact hc.injOn he hd (congrArg w hed)
  · rintro ⟨hi, hf⟩
    exact hs.mp (hi.comp_of_image hf)

/-- The labels are literally the one-dimensional spans of configuration
vectors, not a quotient defined using the desired component decomposition. -/
def line (v : E → V) (e : E) : Submodule K V := Submodule.span K {v e}

abbrev Lines (v : E → V) := Set.range (line (K := K) v)

def projection (v : E → V) (e : E) : Lines (K := K) v :=
  ⟨line (K := K) v e, e, rfl⟩

def representative (v : E → V) (l : Lines (K := K) v) : E :=
  Classical.choose l.property

theorem representative_spec (v : E → V) (l : Lines (K := K) v) :
    line (K := K) v (representative (K := K) v l) = l.val := Classical.choose_spec l.property

theorem projection_surjective (v : E → V) :
    Function.Surjective (projection (K := K) v) := by
  intro l
  exact ⟨representative (K := K) v l, Subtype.ext (representative_spec v l)⟩

def matroid (v : E → V) : Matroid (Lines (K := K) v) :=
  VectorMatroid.ofFamily (K := K) (fun l => v (representative (K := K) v l))

/-- The labelled vector matroid is exactly the parallel replication of its
ordinary line matroid. This theorem retains every original label. -/
theorem represented_eq_comap (v : E → V) :
    VectorMatroid.ofFamily (K := K) v = (matroid (K := K) v).comap (projection (K := K) v) := by
  have hs : ∀ e : E, ∃ a : Kˣ, a • v e = v (representative (K := K) v (projection (K := K) v e)) := by
    intro e
    apply Submodule.span_singleton_eq_span_singleton.mp
    exact (representative_spec v (projection (K := K) v e)).symm
  choose a ha using hs
  exact ofFamily_eq_comap_of_units v (fun l => v (representative (K := K) v l))
    (projection (K := K) v) a ha

theorem matroid_loopless (v : E → V) (hv : ∀ e, v e ≠ 0) :
    (matroid (K := K) v).Loopless := by
  rw [Matroid.loopless_iff_forall_not_isLoop]
  intro l _
  simp only [matroid, VectorMatroid.ofFamily_isLoop_iff]
  exact hv (representative (K := K) v l)

theorem cast_component {M N : Matroid E} (h : M = N) (e : E) :
    Equiv.cast (congrArg MatroidComponents.Component h)
      (MatroidComponents.component M e) = MatroidComponents.component N e := by
  cases h
  rfl

/-- Passing to literal lines preserves the canonical connected-component
partition for every nonzero vector family, without rank or finiteness restrictions. -/
def componentEquiv (v : E → V) (hv : ∀ e, v e ≠ 0) :
    MatroidComponents.Component (VectorMatroid.ofFamily (K := K) v) ≃
      MatroidComponents.Component (matroid (K := K) v) := by
  letI := matroid_loopless (K := K) v hv
  exact (Equiv.cast (congrArg MatroidComponents.Component (represented_eq_comap (K := K) v))).trans
    (MatroidComponents.comapComponentEquiv (matroid (K := K) v) (projection (K := K) v) rfl
      (projection_surjective v))

@[simp] theorem componentEquiv_component (v : E → V) (hv : ∀ e, v e ≠ 0) (e : E) :
    componentEquiv (K := K) v hv
        (MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) e) =
      MatroidComponents.component (matroid (K := K) v) (projection (K := K) v e) := by
  dsimp only [componentEquiv, Equiv.trans_apply]
  rw [cast_component (represented_eq_comap (K := K) v) e]
  rfl

theorem component_eq_iff (v : E → V) (hv : ∀ e, v e ≠ 0) (e d : E) :
    MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) e =
        MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) d ↔
      MatroidComponents.component (matroid (K := K) v) (projection (K := K) v e) =
        MatroidComponents.component (matroid (K := K) v) (projection (K := K) v d) := by
  rw [← componentEquiv_component (K := K) v hv e, ← componentEquiv_component (K := K) v hv d]
  exact (componentEquiv (K := K) v hv).injective.eq_iff.symm

end Unimodular.LineMatroid

#print axioms Unimodular.LineMatroid.ofFamily_eq_comap_of_units
#print axioms Unimodular.LineMatroid.represented_eq_comap
#print axioms Unimodular.LineMatroid.matroid_loopless
#print axioms Unimodular.LineMatroid.componentEquiv
#print axioms Unimodular.LineMatroid.component_eq_iff
#check "UNIMODULAR_LINE_MATROID_EOF_V2"

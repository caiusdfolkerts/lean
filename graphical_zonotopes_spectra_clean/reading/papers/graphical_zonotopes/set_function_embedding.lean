module

public import Papers.GraphicalZonotopes.BoundaryContexts
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def pullSet (e : W ↪ V) (S : Finset V) : Finset W :=
  univ.filter fun w => e w∈S

@[simp] theorem mem_pullSet (e : W ↪ V) (S : Finset V) (w : W) :
    w∈pullSet e S ↔ e w∈S := by simp [pullSet]

@[simp] theorem pullSet_empty (e : W ↪ V) : pullSet e ∅=∅ := by
  ext w
  simp

@[simp] theorem pullSet_map (e : W ↪ V) (S : Finset W) : pullSet e (S.map e)=S := by
  ext w
  simp

@[simp] theorem pullSet_insert_image (e : W ↪ V) (w : W) (S : Finset V) :
    pullSet e (insert (e w) S)=insert w (pullSet e S) := by
  ext x
  simp [e.injective.eq_iff]

theorem pullSet_insert_not_range (e : W ↪ V) (v : V) (hv : v∉Set.range e)
    (S : Finset V) : pullSet e (insert v S)=pullSet e S := by
  ext w
  have h : e w≠v := fun he => hv ⟨w,he⟩
  simp [h]

@[simp] theorem pullSet_union (e : W ↪ V) (S T : Finset V) :
    pullSet e (S∪T)=pullSet e S∪pullSet e T := by ext w; simp

@[simp] theorem pullSet_inter (e : W ↪ V) (S T : Finset V) :
    pullSet e (S∩T)=pullSet e S∩pullSet e T := by ext w; simp

def restrict (e : W ↪ V) (f : SetFunction V) : SetFunction W := fun S => f (S.map e)
def extend (e : W ↪ V) (f : SetFunction W) : SetFunction V := fun S => f (pullSet e S)

@[simp] theorem restrict_smul (e : W ↪ V) (c : ℝ) (f : SetFunction V) :
    restrict e (c • f)=c • restrict e f := rfl

@[simp] theorem extend_smul (e : W ↪ V) (c : ℝ) (f : SetFunction W) :
    extend e (c • f)=c • extend e f := rfl

@[simp] theorem extend_sub (e : W ↪ V) (f g : SetFunction W) :
    extend e (f-g)=extend e f-extend e g := rfl

@[simp] theorem restrict_extend (e : W ↪ V) (f : SetFunction W) :
    restrict e (extend e f)=f := by funext S; simp [restrict,extend]

theorem extend_injective (e : W ↪ V) : Function.Injective (extend e) := by
  intro f g he
  have h := congrArg (restrict e) he
  simpa using h

theorem restrict_translationNormalized (e : W ↪ V) {f : SetFunction V}
    (hf : TranslationNormalized f) : TranslationNormalized (restrict e f) := by
  exact ⟨by simpa [Normalized,restrict] using hf.1,fun w => by simpa [restrict] using hf.2 (e w)⟩

theorem extend_translationNormalized (e : W ↪ V) {f : SetFunction W}
    (hf : TranslationNormalized f) : TranslationNormalized (extend e f) := by
  refine ⟨by simpa [Normalized,extend] using hf.1,?_⟩
  intro v
  by_cases hv : v∈Set.range e
  · obtain ⟨w,rfl⟩ := hv
    change f (pullSet e (insert (e w) ∅))=0
    rw [pullSet_insert_image,pullSet_empty]
    exact hf.2 w
  · change f (pullSet e (insert v ∅))=0
    rw [pullSet_insert_not_range e v hv,pullSet_empty]
    exact hf.1

theorem delta_restrict (e : W ↪ V) (f : SetFunction V) (u v : W) (S : Finset W) :
    delta (restrict e f) u v S=delta f (e u) (e v) (S.map e) := by
  simp only [delta,restrict,map_insert]

theorem delta_extend (e : W ↪ V) (f : SetFunction W) (u v : W) (S : Finset V) :
    delta (extend e f) (e u) (e v) S=delta f u v (pullSet e S) := by
  simp only [delta,extend,pullSet_insert_image]

theorem delta_extend_not_range (e : W ↪ V) (f : SetFunction W) (u v : V)
    (hu : u∉Set.range e) (S : Finset V) : delta (extend e f) u v S=0 := by
  simp only [delta,extend,pullSet_insert_not_range e u hu]
  ring

theorem restrict_graphical (e : W ↪ V) {G : SimpleGraph V} {f : SetFunction V}
    (hf : Graphical G f) : Graphical (G.comap e) (restrict e f) := by
  intro u v huv hnon S hu hv
  rw [delta_restrict]
  exact hf (e u) (e v) (fun h => huv (e.injective h)) hnon _
    (by simpa using hu) (by simpa using hv)

theorem extend_graphical (e : W ↪ V) {G : SimpleGraph V} {f : SetFunction W}
    (hf : Graphical (G.comap e) f) : Graphical G (extend e f) := by
  intro u v huv hnon S hu hv
  by_cases huR : u∈Set.range e
  · obtain ⟨a,rfl⟩ := huR
    by_cases hvR : v∈Set.range e
    · obtain ⟨b,rfl⟩ := hvR
      rw [delta_extend]
      exact hf a b (fun he => huv (congrArg e he)) hnon _
        (by simpa using hu) (by simpa using hv)
    · rw [delta_comm]
      exact delta_extend_not_range e f v (e a) hvR S
  · exact delta_extend_not_range e f u v huR S

theorem restrict_supermodular (e : W ↪ V) {f : SetFunction V}
    (hf : Supermodular f) : Supermodular (restrict e f) := by
  intro S T
  simpa only [restrict,map_union,map_inter] using hf (S.map e) (T.map e)

theorem extend_supermodular (e : W ↪ V) {f : SetFunction W}
    (hf : Supermodular f) : Supermodular (extend e f) := by
  intro S T
  simpa only [extend,pullSet_union,pullSet_inter] using hf (pullSet e S) (pullSet e T)

theorem extend_insert_absent (e : W ↪ V) (f : SetFunction W) (v : V)
    (hv : v∉Set.range e) (S : Finset V) : extend e f (insert v S)=extend e f S := by
  simp only [extend,pullSet_insert_not_range e v hv]

/-- Restriction preserves exact Möbius coefficients on every retained
subset; no maximal-clique or cardinality assumption is needed. -/
theorem mobius_restrict (e : W ↪ V) (f : SetFunction V) (C : Finset W) :
    mobius (restrict e f) C=mobius f (C.map e) := by
  have hsum (S : Finset W) :
      zeta (fun T => mobius f (T.map e)) S=f (S.map e) := by
    conv_rhs => rw [← zeta_mobius f]
    unfold zeta
    apply sum_bij (fun T _ => T.map e)
    · intro T hT
      exact mem_powerset.mpr ((map_subset_map).mpr (mem_powerset.mp hT))
    · intro T hT U hU he
      exact Finset.map_injective e he
    · intro T hT
      refine ⟨pullSet e T,?_,?_⟩
      · apply mem_powerset.mpr
        intro w hw
        have h := (mem_powerset.mp hT) ((mem_pullSet e T w).mp hw)
        simpa using h
      · ext v
        constructor
        · rintro hv
          obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
          exact (mem_pullSet e T w).mp hw
        · intro hv
          obtain ⟨w,hw,rfl⟩ := mem_map.mp ((mem_powerset.mp hT) hv)
          exact mem_map.mpr ⟨w,(mem_pullSet e T w).mpr hv,rfl⟩
    · intro T hT
      rfl
  have he : zeta (fun T => mobius f (T.map e))=restrict e f := funext hsum
  have h := congrArg mobius he
  rw [mobius_zeta] at h
  exact congrFun h.symm C

end SetFunctionEmbedding
end GraphicalZonotopes

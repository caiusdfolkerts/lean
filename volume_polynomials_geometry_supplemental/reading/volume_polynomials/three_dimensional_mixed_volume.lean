module

public import VolumePolynomials.MixedVolumeMultilinearMap
public import VolumePolynomials.CrossPlaneVolume
public import VolumePolynomials.FirstVariableCoefficient
public import VolumePolynomials.InteractionGeometryBounds

@[expose] public section
set_option autoImplicit false

/-! # Literal mixed volume in the three coordinate planes

The coordinate order is `(z,(x,y))`; its measure is the actual product Lebesgue
measure. The trilinear laws and first derivative are obtained from the proved
volume polynomial and its normalized coefficients.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

abbrev Space := ℝ × Plane

def embedXY : Plane →L[ℝ] Space where
  toFun p := (0, p)
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def embedYZ : Plane →L[ℝ] Space where
  toFun p := (p.2, (0, p.1))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def embedXZ : Plane →L[ℝ] Space where
  toFun p := (p.2, (p.1, 0))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

theorem space_finrank : finrank ℝ Space = 3 := by
  first
  | simp [Space, Plane, Module.finrank_prod, Module.finrank_self]

def mixed3 (A B C : ConvexBody Space) : ℝ := mixedVolume volume ![A, B, C]

theorem mixed3_swap_first (A B C : ConvexBody Space) : mixed3 A B C = mixed3 B A C := by
  first
  | have h := mixedVolume_reindex volume ![A, B, C] (Equiv.swap (0 : Fin 3) 1)
    have he : (fun i => (![A, B, C] : Fin 3 → ConvexBody Space) (Equiv.swap 0 1 i)) =
        ![B, A, C] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [he, mixed3] using h.symm

theorem mixed3_swap_last (A B C : ConvexBody Space) : mixed3 A B C = mixed3 A C B := by
  first
  | have h := mixedVolume_reindex volume ![A, B, C] (Equiv.swap (1 : Fin 3) 2)
    have he : (fun i => (![A, B, C] : Fin 3 → ConvexBody Space) (Equiv.swap 1 2 i)) =
        ![A, C, B] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    simpa only [he, mixed3] using h.symm

theorem mixed3_add_first (A D B C : ConvexBody Space) :
    mixed3 (A + D) B C = mixed3 A B C + mixed3 D B C := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_add volume ![A, B, C] 0 A D

theorem mixed3_add_middle (A B D C : ConvexBody Space) :
    mixed3 A (B + D) C = mixed3 A B C + mixed3 A D C := by
  first
  | rw [mixed3_swap_first A, mixed3_add_first, mixed3_swap_first B A, mixed3_swap_first D A]

theorem mixed3_add_last (A B C D : ConvexBody Space) :
    mixed3 A B (C + D) = mixed3 A B C + mixed3 A B D := by
  first
  | rw [mixed3_swap_last A B, mixed3_add_middle, mixed3_swap_last A C B, mixed3_swap_last A D B]

theorem mixed3_smul_first (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 (r • A) B C = r * mixed3 A B C := by
  first
  | simpa only [mixed3, Matrix.vecCons, Fin.update_cons_zero] using
      mixedVolume_smul volume ![A, B, C] 0 A hr

theorem mixed3_smul_middle (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 A (r • B) C = r * mixed3 A B C := by
  first
  | rw [mixed3_swap_first A, mixed3_smul_first B A C hr, mixed3_swap_first B A]

theorem mixed3_smul_last (A B C : ConvexBody Space) {r : ℝ} (hr : 0 ≤ r) :
    mixed3 A B (r • C) = r * mixed3 A B C := by
  first
  | rw [mixed3_swap_last A B, mixed3_smul_middle A C B hr, mixed3_swap_last A C B]

theorem mixed3_diagonal (A : ConvexBody Space) : mixed3 A A A = volume.real (A : Set Space) := by
  first
  | have he : (![A, A, A] : Fin 3 → ConvexBody Space) = fun _ => A := by
      first
      | funext i; fin_cases i <;> rfl
    simpa only [mixed3, he] using mixedVolume_diagonal volume space_finrank A

theorem mixed3_translate (A B C : ConvexBody Space) (a b c : Space) :
    mixed3 (translateBody a A) (translateBody b B) (translateBody c C) = mixed3 A B C := by
  first
  | have he : (fun i : Fin 3 => translateBody (![a, b, c] i) (![A, B, C] i)) =
        ![translateBody a A, translateBody b B, translateBody c C] := by
      first
      | funext i; fin_cases i <;> rfl
    simpa only [mixed3, he] using mixedVolume_translate volume ![A, B, C] ![a, b, c]

theorem cubic_volume_expansion (A S : ConvexBody Space) {t : ℝ} (ht : 0 ≤ t) :
    volume.real ((S + t • A : ConvexBody Space) : Set Space) =
      volume.real (S : Set Space) + 3 * t * mixed3 A S S +
        3 * t ^ 2 * mixed3 A A S + t ^ 3 * volume.real (A : Set Space) := by
  first
  | rw [← mixed3_diagonal]
    simp only [mixed3_add_first, mixed3_add_middle, mixed3_add_last,
      mixed3_smul_first _ _ _ ht, mixed3_smul_middle _ _ _ ht,
      mixed3_smul_last _ _ _ ht]
    rw [mixed3_diagonal S, mixed3_diagonal A,
      mixed3_swap_first S A S, mixed3_swap_last S S A,
      mixed3_swap_first S A S, mixed3_swap_last A S A,
      mixed3_swap_first S A A, mixed3_swap_last A S A]
    ring

theorem mixed3_hasDerivWithinAt_volume (A S : ConvexBody Space) :
    HasDerivWithinAt (fun t : ℝ => volume.real ((S + t • A : ConvexBody Space) : Set Space))
      (3 * mixed3 A S S) (Ioi 0) 0 := by
  first
  | have hd : HasDerivAt (fun t : ℝ => volume.real (S : Set Space) +
        3 * t * mixed3 A S S + 3 * t ^ 2 * mixed3 A A S +
        t ^ 3 * volume.real (A : Set Space)) (3 * mixed3 A S S) 0 := by
      first
      | convert (((hasDerivAt_const (0 : ℝ) (volume.real (S : Set Space))).add
          (((hasDerivAt_id (0 : ℝ)).const_mul 3).mul_const (mixed3 A S S))).add
          ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 3).mul_const (mixed3 A A S))).add
          (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (volume.real (A : Set Space))) using 1 <;> norm_num <;> rfl
    exact hd.hasDerivWithinAt.congr (fun t ht => cubic_volume_expansion A S ht.le)
      (cubic_volume_expansion A S le_rfl)

def triple (A B C : ConvexBody Plane) : ℝ :=
  mixed3 (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)

end VolumePolynomials.PlanarInteraction

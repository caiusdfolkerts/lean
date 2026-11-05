module

public import Papers.GraphicalZonotopes.PathJoinCoordinateRows

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def TightOn {n : ℕ} (f : SetFunction (Vertex n)) : Prop :=
  ∀ u v,u≠v → ∀ S,u∉S → v∉S → delta (setFunction n) u v S=0 → delta f u v S=0

theorem tight_graphical {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    Graphical (graph n) f := by
  intro u v huv hadj S hu hv
  exact h u v huv S hu hv (graphical n u v huv hadj S hu hv)

@[simp] theorem aCoeff_paper {n : ℕ} (i : Fin (n+2)) : aCoeff (setFunction n) i=1 := by
  simp [aCoeff,coefficient]
@[simp] theorem bCoeff_paper {n : ℕ} (i : Fin (n+2)) :
    bCoeff (setFunction n) i=if i=0 then 0 else 1 := by simp [bCoeff,coefficient]
@[simp] theorem eCoeff_paper {n : ℕ} (i : Fin (n+2)) :
    eCoeff (setFunction n) i=if i=0 then 0 else -1 := by simp [eCoeff,coefficient]
@[simp] theorem dCoeff_paper {n : ℕ} (i : Fin (n+1)) : dCoeff (setFunction n) i=1 := by
  simp [dCoeff,coefficient]
@[simp] theorem taCoeff_paper {n : ℕ} (i : Fin (n+1)) :
    taCoeff (setFunction n) i=if i.val%2=0 then -1 else 0 := by simp [taCoeff,coefficient]
@[simp] theorem tbCoeff_paper {n : ℕ} (i : Fin (n+1)) :
    tbCoeff (setFunction n) i=if i.val%2=0 then 0 else -1 := by simp [tbCoeff,coefficient]
@[simp] theorem hCoeff_paper {n : ℕ} (i : Fin (n+1)) : hCoeff (setFunction n) i=1 := by
  simp [hCoeff,coefficient]

def nearSpoke {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) (i : Fin (n+2)) :=
  if j.val%2=0 then aCoeff f i else bCoeff f i

theorem tight_a_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : aCoeff f i+eCoeff f i=0 := by
  have hz := h (hubA n) (vertex i) (hubA_ne_vertex i) {hubB n}
    (by simp) (by simp) (by rw [delta_a_hub]; simp [hi])
  rwa [delta_a_hub] at hz

theorem tight_b_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : bCoeff f i+eCoeff f i=0 := by
  have hz := h (hubB n) (vertex i) (hubB_ne_vertex i) {hubA n}
    (by simp) (by simp) (by rw [delta_b_hub]; simp [hi])
  rwa [delta_b_hub] at hz

theorem tight_a_eq_b {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : aCoeff f i=bCoeff f i := by
  have ha := tight_a_e h i hi
  have hb := tight_b_e h i hi
  linarith

theorem nearSpoke_eq_a {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) (i : Fin (n+2)) (hi : i≠0) : nearSpoke f j i=aCoeff f i := by
  unfold nearSpoke
  split_ifs
  · rfl
  · exact (tight_a_eq_b h i hi).symm

theorem tight_near_right {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nearSpoke f j j.succ+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.succ) (hubA_ne_vertex j.succ) {vertex j.castSucc}
      (by simp) (by simp) (by rw [delta_a_right]; simp [he])
    simpa only [delta_a_right,nearSpoke,nCoeff,he,ite_true] using hz
  · have hz := h (hubB n) (vertex j.succ) (hubB_ne_vertex j.succ) {vertex j.castSucc}
      (by simp) (by simp) (by rw [delta_b_right]; simp [he])
    simpa only [delta_b_right,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_near_left {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nearSpoke f j j.castSucc+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.castSucc) (hubA_ne_vertex j.castSucc) {vertex j.succ}
      (by simp) (by simp) (by rw [delta_a_left]; simp [he])
    simpa only [delta_a_left,nearSpoke,nCoeff,he,ite_true] using hz
  · have hj : j.castSucc≠0 := by
      intro hz
      have hz' := congrArg Fin.val hz
      simp only [Fin.val_castSucc,Fin.val_zero] at hz'
      omega
    have hz := h (hubB n) (vertex j.castSucc) (hubB_ne_vertex j.castSucc) {vertex j.succ}
      (by simp) (by simp) (by rw [delta_b_left]; simp [he,hj])
    simpa only [delta_b_left,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_near_right_hub {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) :
    nearSpoke f j j.succ+eCoeff f j.succ+nCoeff f j+hCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.succ) (hubA_ne_vertex j.succ)
      {hubB n,vertex j.castSucc} (by simp) (by simp)
      (by rw [delta_a_right_hub]; simp [he])
    simpa only [delta_a_right_hub,nearSpoke,nCoeff,he,ite_true] using hz
  · have hz := h (hubB n) (vertex j.succ) (hubB_ne_vertex j.succ)
      {hubA n,vertex j.castSucc} (by simp) (by simp)
      (by rw [delta_b_right_hub]; simp [he])
    simpa only [delta_b_right_hub,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_path_near {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : dCoeff f j+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (vertex j.castSucc) (vertex j.succ) (vertex_left_ne_right j) {hubA n}
      (by simp) (by simp) (by rw [delta_path_a]; simp [he])
    simpa only [delta_path_a,nCoeff,he,ite_true] using hz
  · have hz := h (vertex j.castSucc) (vertex j.succ) (vertex_left_ne_right j) {hubB n}
      (by simp) (by simp) (by rw [delta_path_b]; simp [he])
    simpa only [delta_path_b,nCoeff,he,ite_false] using hz

theorem tight_first_b {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    bCoeff f (0 : Fin (n+2))=0 := by
  have hdelta (g : SetFunction (Vertex n)) :
      delta g (hubB n) (vertex (0 : Fin (n+2))) ∅=bCoeff g 0 := by
    rw [←zeta_mobius g,delta_zeta_empty (mobius g) (hubB_ne_vertex _)]
    simp [bCoeff,coordinate,clique]
  have hz := h (hubB n) (vertex (0 : Fin (n+2))) (hubB_ne_vertex _) ∅
    (by simp) (by simp) (by rw [hdelta]; simp)
  rwa [hdelta] at hz

theorem tight_first_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    eCoeff f (0 : Fin (n+2))=0 := by
  have hz := h (hubB n) (vertex (0 : Fin (n+2))) (hubB_ne_vertex _) {hubA n}
    (by simp) (by simp) (by rw [delta_b_hub]; simp)
  rw [delta_b_hub,tight_first_b h,zero_add] at hz
  exact hz

theorem tight_first_z {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    zCoeff f (0 : Fin (n+1))=0 := by
  have hz := h (hubB n) (vertex (0 : Fin (n+1)).castSucc) (hubB_ne_vertex _)
    {vertex (0 : Fin (n+1)).succ} (by simp) (by simp)
    (by rw [delta_b_left]; simp)
  rw [delta_b_left] at hz
  simpa [zCoeff,tight_first_b h] using hz

theorem tight_two_neighbors {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) (j : Fin n) :
    nearSpoke f j.castSucc j.castSucc.succ+nCoeff f j.castSucc+zCoeff f j.succ=0 := by
  have hne : vertex j.castSucc.succ≠vertex j.succ.succ := by
    rw [consecutive_middle]
    exact vertex_left_ne_right j.succ
  by_cases he : j.val%2=0
  · have ho : (j.val+1)%2≠0 := by omega
    have hz := h (hubA n) (vertex j.castSucc.succ) (hubA_ne_vertex _)
      {vertex j.castSucc.castSucc,vertex j.succ.succ} (by simp) (by simp [hne])
      (by rw [delta_a_two_neighbors _ (normalized n) (graphical n)]; simp [he,ho])
    rw [delta_a_two_neighbors _ hn (tight_graphical h)] at hz
    simpa [nearSpoke,nCoeff,zCoeff,he,ho] using hz
  · have ho : (j.val+1)%2=0 := by omega
    have hz := h (hubB n) (vertex j.castSucc.succ) (hubB_ne_vertex _)
      {vertex j.castSucc.castSucc,vertex j.succ.succ} (by simp) (by simp [hne])
      (by rw [delta_b_two_neighbors _ (normalized n) (graphical n)]; simp [he,ho])
    rw [delta_b_two_neighbors _ hn (tight_graphical h)] at hz
    simpa [nearSpoke,nCoeff,zCoeff,he,ho] using hz

end GraphicalZonotopes.PathJoin

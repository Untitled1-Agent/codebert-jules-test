import TuzaDelta8.KernelScratch
import TuzaDelta8.AbstractReduction

namespace TuzaDelta8

theorem triangleHit_iff (t : Tri) (X : List Edge) :
    t.edgeList.any (fun e => X.contains e) = true ↔ Hits Tri.edgeList X t := by
  simp [Hits, List.any_eq_true, List.contains_iff_mem]

namespace FGraph

@[simp] theorem hasEdge_true_iff (g : FGraph) (u v : Nat) :
    g.hasEdge u v = true ↔ u ≠ v ∧ Edge.norm u v ∈ g.edges := by
  by_cases h : u = v
  · subst v
    simp [hasEdge]
  · simp [hasEdge, h, List.contains_iff_mem]

theorem isTriangle_iff_edges (g : FGraph) (t : Tri) :
    g.isTriangle t = true ↔
      t.wellFormed g.n = true ∧ ∀ e, e ∈ t.edgeList → e ∈ g.edges := by
  constructor
  · intro ht
    have h : t.wellFormed g.n = true ∧ g.hasEdge t.a t.b = true ∧
        g.hasEdge t.a t.c = true ∧ g.hasEdge t.b t.c = true := by
      simpa only [isTriangle, Bool.and_eq_true, and_assoc] using ht
    refine ⟨h.1, ?_⟩
    intro e he
    simp only [Tri.edgeList, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ((hasEdge_true_iff g _ _).mp h.2.1).2
    · exact ((hasEdge_true_iff g _ _).mp h.2.2.1).2
    · exact ((hasEdge_true_iff g _ _).mp h.2.2.2).2
  · rintro ⟨hw, he⟩
    have hb : t.a < t.b ∧ t.b < t.c ∧ t.c < g.n :=
      of_decide_eq_true hw
    have hab : g.hasEdge t.a t.b = true :=
      (hasEdge_true_iff g _ _).mpr ⟨by omega, he _ (by simp [Tri.edgeList])⟩
    have hac : g.hasEdge t.a t.c = true :=
      (hasEdge_true_iff g _ _).mpr ⟨by omega, he _ (by simp [Tri.edgeList])⟩
    have hbc : g.hasEdge t.b t.c = true :=
      (hasEdge_true_iff g _ _).mpr ⟨by omega, he _ (by simp [Tri.edgeList])⟩
    simp [isTriangle, hw, hab, hac, hbc]

theorem mem_allTriangles_iff (g : FGraph) (t : Tri) :
    t ∈ g.allTriangles ↔ g.isTriangle t = true := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨a, _, ha⟩
    rcases List.mem_flatMap.mp ha with ⟨b, _, hb⟩
    rcases List.mem_filterMap.mp hb with ⟨c, _, hc⟩
    by_cases hab : a < b
    · by_cases hbc : b < c
      · by_cases htri : g.isTriangle ⟨a, b, c⟩ = true
        · have heq : (⟨a, b, c⟩ : Tri) = t := by
            simpa [hab, hbc, htri] using hc
          simpa [← heq] using htri
        · simp [hab, hbc, htri] at hc
      · simp [hab, hbc] at hc
    · simp [hab] at hc
  · intro ht
    have hw := ((isTriangle_iff_edges g t).mp ht).1
    have hb : t.a < t.b ∧ t.b < t.c ∧ t.c < g.n :=
      of_decide_eq_true hw
    apply List.mem_flatMap.mpr
    refine ⟨t.a, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨t.b, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨t.c, List.mem_range.mpr hb.2.2, ?_⟩
    simpa [hb.1, hb.2.1, ht]

theorem isTrianglePacking_iff_spec (g : FGraph) (S : List Tri) :
    g.isTrianglePacking S = true ↔
      TrianglePackingSpec Tri.edgeList (fun t => g.isTriangle t = true) S := by
  simp [isTrianglePacking, TrianglePackingSpec, EdgeDisjointFamily,
    List.all_eq_true]

theorem isTriangleTransversal_iff_spec (g : FGraph) (X : List Edge) :
    g.isTriangleTransversal X = true ↔
      X.Nodup ∧ (∀ e, e ∈ X → e ∈ g.edges) ∧
      TriangleCoverSpec Tri.edgeList (fun t => g.isTriangle t = true) X := by
  constructor
  · intro h
    have hh : X.Nodup ∧
        (∀ e, e ∈ X → e ∈ g.edges) ∧
        (∀ t, t ∈ g.allTriangles →
          t.edgeList.any (fun e => X.contains e) = true) := by
      simpa [isTriangleTransversal, List.all_eq_true] using h
    refine ⟨hh.1, hh.2.1, ?_⟩
    intro t ht
    exact (triangleHit_iff t X).mp
      (hh.2.2 t ((mem_allTriangles_iff g t).mpr ht))
  · rintro ⟨hn, he, hc⟩
    have hh :
        (∀ t, t ∈ g.allTriangles →
          t.edgeList.any (fun e => X.contains e) = true) := by
      intro t ht
      exact (triangleHit_iff t X).mpr
        (hc t ((mem_allTriangles_iff g t).mp ht))
    simp [isTriangleTransversal, List.all_eq_true, hn, he, hh]


end FGraph
end TuzaDelta8

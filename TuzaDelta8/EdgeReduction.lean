import TuzaDelta8.GraphSemantics

namespace TuzaDelta8
namespace FGraph

private theorem guardedEdgeCover (p q : Bool) :
    (if p then q else true) = true ↔ (p = true → q = true) := by
  cases p <;> simp

private theorem guardedEdgeProtection (p q : Bool) :
    (if p then true else q) = true ↔ (p ≠ true → q = true) := by
  cases p <;> simp

structure EdgeReductionConditions (g : FGraph) (E0 : List Edge)
    (S : List Tri) (X : List Edge) : Prop where
  removedNodup : E0.Nodup
  removedNonempty : E0 ≠ []
  removedEdges : ∀ e, e ∈ E0 → e ∈ g.edges
  packing : TrianglePackingSpec Tri.edgeList (fun t => g.isTriangle t = true) S
  coverNodup : X.Nodup
  coverEdges : ∀ e, e ∈ X → e ∈ g.edges
  budget : X.length ≤ 2 * S.length
  localCover : ∀ t, g.isTriangle t = true → Hits Tri.edgeList E0 t →
    Hits Tri.edgeList X t
  protection : ∀ t, t ∈ S → ∀ e, e ∈ t.edgeList →
    e ∉ E0 → e ∈ X

theorem isEdgeReductionCertificate_iff_conditions
    (g : FGraph) (E0 : List Edge) (S : List Tri) (X : List Edge) :
    g.isEdgeReductionCertificate E0 S X = true ↔
      EdgeReductionConditions g E0 S X := by
  have hexpand : g.isEdgeReductionCertificate E0 S X = true ↔
      E0.Nodup ∧ E0 ≠ [] ∧
      (∀ e, e ∈ E0 → e ∈ g.edges) ∧
      g.isTrianglePacking S = true ∧
      X.Nodup ∧ (∀ e, e ∈ X → e ∈ g.edges) ∧
      X.length ≤ 2 * S.length ∧
      (∀ t, t ∈ g.allTriangles →
        Hits Tri.edgeList E0 t → Hits Tri.edgeList X t) ∧
      (∀ t, t ∈ S → ∀ e, e ∈ t.edgeList → e ∉ E0 → e ∈ X) := by
    simp [isEdgeReductionCertificate, List.all_eq_true, List.contains_iff_mem,
      guardedEdgeCover, guardedEdgeProtection, triangleHit_iff, and_assoc]
  rw [hexpand]
  constructor
  · rintro ⟨hen, hene, hee, hp, hxn, hxe, hb, hc, hprot⟩
    refine ⟨hen, hene, hee, (isTrianglePacking_iff_spec g S).mp hp,
      hxn, hxe, hb, ?_, hprot⟩
    intro t ht hlocal
    exact hc t ((mem_allTriangles_iff g t).mpr ht) hlocal
  · intro h
    refine ⟨h.removedNodup, h.removedNonempty, h.removedEdges,
      (isTrianglePacking_iff_spec g S).mpr h.packing,
      h.coverNodup, h.coverEdges, h.budget, ?_, h.protection⟩
    intro t ht hlocal
    exact h.localCover t ((mem_allTriangles_iff g t).mp ht) hlocal

theorem isTriangle_edgeResidual_iff (g : FGraph) (E0 X : List Edge) (t : Tri) :
    (g.edgeResidual E0 X).isTriangle t = true ↔
      g.isTriangle t = true ∧
      ∀ e, e ∈ t.edgeList → e ∉ E0 ∧ e ∉ X := by
  constructor
  · intro ht
    have h := (isTriangle_iff_edges (g.edgeResidual E0 X) t).mp ht
    have hedge : ∀ e, e ∈ t.edgeList →
        e ∈ g.edges ∧ e ∉ E0 ∧ e ∉ X := by
      intro e he
      exact (mem_edgeResidual_edges_iff g E0 X e).mp (h.2 e he)
    constructor
    · exact (isTriangle_iff_edges g t).mpr ⟨h.1, fun e he => (hedge e he).1⟩
    · exact fun e he => (hedge e he).2
  · rintro ⟨ht, havoid⟩
    have h := (isTriangle_iff_edges g t).mp ht
    apply (isTriangle_iff_edges (g.edgeResidual E0 X) t).mpr
    refine ⟨h.1, ?_⟩
    intro e he
    exact (mem_edgeResidual_edges_iff g E0 X e).mpr
      ⟨h.2 e he, (havoid e he).1, (havoid e he).2⟩

theorem edgeResidual_triangle_survives
    (g : FGraph) (E0 X : List Edge) (t : Tri)
    (ht : g.isTriangle t = true)
    (he0 : ¬ Hits Tri.edgeList E0 t)
    (hx : ¬ Hits Tri.edgeList X t) :
    (g.edgeResidual E0 X).isTriangle t = true := by
  apply (isTriangle_edgeResidual_iff g E0 X t).mpr
  refine ⟨ht, ?_⟩
  intro e he
  constructor
  · intro hm
    exact he0 ⟨e, he, hm⟩
  · intro hm
    exact hx ⟨e, he, hm⟩

theorem edgeResidual_packing_lift
    (g : FGraph) (E0 X : List Edge) (R : List Tri)
    (hR : (g.edgeResidual E0 X).isTrianglePacking R = true) :
    g.isTrianglePacking R = true := by
  have h := (isTrianglePacking_iff_spec (g.edgeResidual E0 X) R).mp hR
  apply (isTrianglePacking_iff_spec g R).mpr
  refine ⟨?_, h.2⟩
  intro t ht
  exact ((isTriangle_edgeResidual_iff g E0 X t).mp (h.1 t ht)).1

theorem hasTuzaWitness_of_edgeReductionCertificate
    (g : FGraph) (E0 : List Edge) (S : List Tri) (X : List Edge)
    (hcheck : g.isEdgeReductionCertificate E0 S X = true)
    (hresidual : (g.edgeResidual E0 X).hasTuzaWitness) :
    g.hasTuzaWitness := by
  have h := (isEdgeReductionCertificate_iff_conditions g E0 S X).mp hcheck
  rcases hresidual with ⟨R, Y, hR, hY, hbudget⟩
  have hpackR :=
    (isTrianglePacking_iff_spec (g.edgeResidual E0 X) R).mp hR
  have hcoverY :=
    (isTriangleTransversal_iff_spec (g.edgeResidual E0 X) Y).mp hY
  have hRlift := (isTrianglePacking_iff_spec g R).mp
    (edgeResidual_packing_lift g E0 X R hR)
  have hcombo := reductionCombinedWitness Tri.edgeList
    (fun t => g.isTriangle t = true)
    (fun t => Hits Tri.edgeList E0 t)
    (fun e => e ∈ E0)
    S R X Y
    h.packing hRlift h.localCover
    (by
      intro t ht hnotlocal hnotx
      exact hcoverY.2.2 t
        (edgeResidual_triangle_survives g E0 X t ht hnotlocal hnotx))
    h.protection
    (by
      intro r hr e he
      have ha :=
        ((isTriangle_edgeResidual_iff g E0 X r).mp (hpackR.1 r hr)).2 e he
      exact ⟨ha.2, ha.1⟩)
    h.budget hbudget
  have hxy : ∀ e, e ∈ X → e ∈ Y → False := by
    intro e hex hey
    have hmem := (mem_edgeResidual_edges_iff g E0 X e).mp
      (hcoverY.2.1 e hey)
    exact hmem.2.2 hex
  refine ⟨S ++ R, X ++ Y,
    (isTrianglePacking_iff_spec g (S ++ R)).mpr hcombo.1, ?_, ?_⟩
  · apply (isTriangleTransversal_iff_spec g (X ++ Y)).mpr
    refine ⟨nodupAppendOfNoCommon h.coverNodup hcoverY.1 hxy, ?_, hcombo.2.1⟩
    intro e he
    rcases List.mem_append.mp he with hex | hey
    · exact h.coverEdges e hex
    · exact ((mem_edgeResidual_edges_iff g E0 X e).mp
        (hcoverY.2.1 e hey)).1
  · simpa only [List.length_append] using hcombo.2.2

end FGraph
end TuzaDelta8

import Std

namespace TuzaDelta8

def Hits {T E : Type} (edgesOf : T → List E) (X : List E) (t : T) : Prop :=
  ∃ e, e ∈ edgesOf t ∧ e ∈ X

def CrossEdgeDisjoint {T E : Type} (edgesOf : T → List E)
    (S R : List T) : Prop :=
  ∀ t, t ∈ S → ∀ r, r ∈ R → ∀ e, e ∈ edgesOf t → e ∈ edgesOf r → False

theorem Hits.appendLeft {T E : Type} (edgesOf : T → List E)
    {X Y : List E} {t : T} (h : Hits edgesOf X t) :
    Hits edgesOf (X ++ Y) t := by
  rcases h with ⟨e, heT, heX⟩
  exact ⟨e, heT, by simp [heX]⟩

theorem Hits.appendRight {T E : Type} (edgesOf : T → List E)
    {X Y : List E} {t : T} (h : Hits edgesOf Y t) :
    Hits edgesOf (X ++ Y) t := by
  rcases h with ⟨e, heT, heY⟩
  exact ⟨e, heT, by simp [heY]⟩

theorem reductionCoverage
    {T E : Type}
    (edgesOf : T → List E)
    (Valid Local : T → Prop)
    (X X' : List E)
    (hLocal : ∀ t, Valid t → Local t → Hits edgesOf X t)
    (hResidual : ∀ t, Valid t → ¬ Local t → ¬ Hits edgesOf X t → Hits edgesOf X' t) :
    ∀ t, Valid t → Hits edgesOf (X ++ X') t := by
  intro t ht
  by_cases hlt : Local t
  · exact Hits.appendLeft edgesOf (hLocal t ht hlt)
  · by_cases hx : Hits edgesOf X t
    · exact Hits.appendLeft edgesOf hx
    · exact Hits.appendRight edgesOf (hResidual t ht hlt hx)

theorem reductionCrossDisjoint
    {T E : Type}
    (edgesOf : T → List E)
    (touchesRemoved : E → Prop)
    (S R : List T) (X : List E)
    (hProtect : ∀ t, t ∈ S → ∀ e, e ∈ edgesOf t → ¬ touchesRemoved e → e ∈ X)
    (hResidual : ∀ r, r ∈ R → ∀ e, e ∈ edgesOf r → e ∉ X ∧ ¬ touchesRemoved e) :
    CrossEdgeDisjoint edgesOf S R := by
  intro t ht r hr e het her
  have hR := hResidual r hr e her
  by_cases hTouch : touchesRemoved e
  · exact hR.2 hTouch
  · exact hR.1 (hProtect t ht e het hTouch)

theorem reductionCombinedBudget
    (x x' s s' : Nat)
    (hLocal : x ≤ 2 * s)
    (hResidual : x' ≤ 2 * s') :
    x + x' ≤ 2 * (s + s') := by
  omega

def EdgeDisjointFamily {T E : Type} (edgesOf : T → List E) (S : List T) : Prop :=
  (S.flatMap edgesOf).Nodup

def TrianglePackingSpec {T E : Type} (edgesOf : T → List E)
    (Valid : T → Prop) (S : List T) : Prop :=
  (∀ t, t ∈ S → Valid t) ∧ EdgeDisjointFamily edgesOf S

def TriangleCoverSpec {T E : Type} (edgesOf : T → List E)
    (Valid : T → Prop) (X : List E) : Prop :=
  ∀ t, Valid t → Hits edgesOf X t

theorem nodupAppendOfNoCommon {E : Type} {xs ys : List E}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hxy : ∀ e, e ∈ xs → e ∈ ys → False) :
    (xs ++ ys).Nodup := by
  revert hx hxy
  induction xs with
  | nil =>
      intro _ _
      simpa using hy
  | cons x xs ih =>
      intro hx hxy
      have hc := List.nodup_cons.mp hx
      apply List.nodup_cons.mpr
      constructor
      · intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hc.1 hm
        · exact hxy x (by simp) hm
      · apply ih hc.2
        intro e he
        exact hxy e (by simp [he])

theorem edgeDisjointFamily_append
    {T E : Type} (edgesOf : T → List E) {S R : List T}
    (hS : EdgeDisjointFamily edgesOf S)
    (hR : EdgeDisjointFamily edgesOf R)
    (hCross : CrossEdgeDisjoint edgesOf S R) :
    EdgeDisjointFamily edgesOf (S ++ R) := by
  change ((S ++ R).flatMap edgesOf).Nodup
  rw [List.flatMap_append]
  apply nodupAppendOfNoCommon hS hR
  intro e heS heR
  rcases List.mem_flatMap.mp heS with ⟨s, hs, hes⟩
  rcases List.mem_flatMap.mp heR with ⟨r, hr, her⟩
  exact hCross s hs r hr e hes her

theorem trianglePackingSpec_append
    {T E : Type} (edgesOf : T → List E) (Valid : T → Prop)
    {S R : List T}
    (hS : TrianglePackingSpec edgesOf Valid S)
    (hR : TrianglePackingSpec edgesOf Valid R)
    (hCross : CrossEdgeDisjoint edgesOf S R) :
    TrianglePackingSpec edgesOf Valid (S ++ R) := by
  constructor
  · intro t ht
    have ht' : t ∈ S ∨ t ∈ R := by simpa using ht
    rcases ht' with htS | htR
    · exact hS.1 t htS
    · exact hR.1 t htR
  · exact edgeDisjointFamily_append edgesOf hS.2 hR.2 hCross

theorem reductionCombinedWitness
    {T E : Type}
    (edgesOf : T → List E)
    (Valid Local : T → Prop)
    (touchesRemoved : E → Prop)
    (S R : List T) (X X' : List E)
    (hPackS : TrianglePackingSpec edgesOf Valid S)
    (hPackR : TrianglePackingSpec edgesOf Valid R)
    (hLocalCover : ∀ t, Valid t → Local t → Hits edgesOf X t)
    (hResidualCover : ∀ t, Valid t → ¬ Local t → ¬ Hits edgesOf X t →
      Hits edgesOf X' t)
    (hProtect : ∀ t, t ∈ S → ∀ e, e ∈ edgesOf t →
      ¬ touchesRemoved e → e ∈ X)
    (hResidualEdges : ∀ r, r ∈ R → ∀ e, e ∈ edgesOf r →
      e ∉ X ∧ ¬ touchesRemoved e)
    (hLocalBudget : X.length ≤ 2 * S.length)
    (hResidualBudget : X'.length ≤ 2 * R.length) :
    TrianglePackingSpec edgesOf Valid (S ++ R) ∧
    TriangleCoverSpec edgesOf Valid (X ++ X') ∧
    (X.length + X'.length ≤ 2 * ((S ++ R).length)) := by
  have hCross : CrossEdgeDisjoint edgesOf S R :=
    reductionCrossDisjoint edgesOf touchesRemoved S R X hProtect hResidualEdges
  constructor
  · exact trianglePackingSpec_append edgesOf Valid hPackS hPackR hCross
  constructor
  · intro t ht
    exact reductionCoverage edgesOf Valid Local X X' hLocalCover hResidualCover t ht
  · simpa [List.length_append] using
      (reductionCombinedBudget X.length X'.length S.length R.length
        hLocalBudget hResidualBudget)

end TuzaDelta8

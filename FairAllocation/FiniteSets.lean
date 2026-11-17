import FairAllocation.Partition
import Mathlib.Data.Finset.SDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-!
# Bridge to the paper's finite-set formulation

Any subset of an allocated bundle is represented by its filtered sublist.
Deletion witnesses are finite sets of at most `k` actual goods. Thus the
use of allocation-ordered lists does not restrict the fairness quantifiers.
-/

namespace FairAllocation

open scoped BigOperators

variable {A G : Type*} [DecidableEq G]

theorem total_eq_sum_toFinset (w : G → ℚ) {L : List G} (hL : L.Nodup) :
    total w L = ∑ g ∈ L.toFinset, w g := by
  induction L with
  | nil => simp
  | cons g L ih =>
    obtain ⟨hg, hL⟩ := List.nodup_cons.mp hL
    simp [List.toFinset_cons, hg, ih hL]

/-- The paper's 'remove at most k goods' definition. -/
def SetEF (k : ℕ) (v : G → ℚ) (u : ℚ) (F : Finset G) : Prop :=
  ∃ R : Finset G, R ⊆ F ∧ R.card ≤ k ∧ ∑ g ∈ F \ R, v g ≤ u

theorem EF.toFinset {k : ℕ} {v : G → ℚ} {u : ℚ} {Z : List G}
    (h : EF k v u Z) (hZ : Z.Nodup) : SetEF k v u Z.toFinset := by
  obtain ⟨K, hK, hlen, hval⟩ := h
  have hKn : K.Nodup := hZ.sublist hK
  have hsub : K.toFinset ⊆ Z.toFinset := by
    intro g hg
    exact List.mem_toFinset.mpr (hK.subset (List.mem_toFinset.mp hg))
  refine ⟨Z.toFinset \ K.toFinset, Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup hZ,
      List.toFinset_card_of_nodup hKn]
    omega
  · have hremain : Z.toFinset \ (Z.toFinset \ K.toFinset) = K.toFinset := by
      ext g
      simp only [Finset.mem_sdiff]
      constructor
      · intro hg
        by_contra hn
        exact hg.2 ⟨hg.1, hn⟩
      · intro hg
        exact ⟨hsub hg, fun hh => hh.2 hg⟩
    rw [hremain, ← total_eq_sum_toFinset v hKn]
    exact hval

theorem selected_toFinset (L : List G) (F : Finset G) (hF : F ⊆ L.toFinset) :
    (L.filter (fun g => decide (g ∈ F))).toFinset = F := by
  ext g
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hg => ⟨List.mem_toFinset.mp (hF hg), hg⟩⟩

namespace Instance

variable (I : Instance A G)

def FairSets (k : ℕ) (bundle : A → Finset G) (charity : Finset G) : Prop :=
  (∀ a b F, F ⊆ bundle b → (∑ g ∈ F, I.size a g) ≤ I.budget a →
    SetEF k I.value (∑ g ∈ bundle a, I.value g) F) ∧
  (∀ a F, F ⊆ charity → (∑ g ∈ F, I.size a g) ≤ I.budget a →
    SetEF k I.value (∑ g ∈ bundle a, I.value g) F)

theorem subset_fair_toFinset {k : ℕ} {X Y : List G} {a : A}
    (hX : X.Nodup) (hY : Y.Nodup)
    (h : ∀ Z, Z.Sublist Y → total (I.size a) Z ≤ I.budget a → EF k I.value (total I.value X) Z)
    (F : Finset G) (hF : F ⊆ Y.toFinset) (hsize : (∑ g ∈ F, I.size a g) ≤ I.budget a) :
    SetEF k I.value (∑ g ∈ X.toFinset, I.value g) F := by
  let Z := Y.filter (fun g => decide (g ∈ F))
  have hZY : Z.Sublist Y := List.filter_sublist
  have hZn : Z.Nodup := hY.sublist hZY
  have hZF : Z.toFinset = F := selected_toFinset Y F hF
  have hZsize : total (I.size a) Z ≤ I.budget a := by
    rw [total_eq_sum_toFinset _ hZn, hZF]
    exact hsize
  have hfair := (h Z hZY hZsize).toFinset hZn
  simpa [hZF, total_eq_sum_toFinset I.value hX] using hfair

variable [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem fair_toFinset {k : ℕ} {S : State A G} (hvalid : S.Valid)
    (hfair : I.Fair k S.bundle S.pool) :
    I.FairSets k (fun a => (S.bundle a).toFinset) S.pool.toFinset := by
  constructor
  · intro a b F hF hsize
    exact I.subset_fair_toFinset (hvalid.bundle_nodup a) (hvalid.bundle_nodup b)
      (hfair.1 a b) F hF hsize
  · intro a F hF hsize
    exact I.subset_fair_toFinset (hvalid.bundle_nodup a) hvalid.pool_nodup
      (hfair.2 a) F hF hsize

end Instance
end FairAllocation

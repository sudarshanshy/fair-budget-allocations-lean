import FairAllocation.Algorithm
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

/-!
# Allocation validity

Every good occurs exactly once across the agents' bundles and charity.
This is proved for the algorithm independently of its fairness invariant.
-/

namespace FairAllocation

open scoped BigOperators

variable {A G : Type*} [Fintype A] [DecidableEq A] [DecidableEq G]

/-- A partition into agents' bundles and charity, counted with multiplicity. -/
def State.Valid (S : State A G) : Prop :=
  ∀ g, S.pool.count g + ∑ a, (S.bundle a).count g = 1

omit [DecidableEq A] in
theorem State.Valid.pool_nodup {S : State A G} (hS : S.Valid) : S.pool.Nodup := by
  apply List.nodup_iff_count.mpr
  intro g
  have := hS g
  omega

omit [DecidableEq A] in
theorem State.Valid.bundle_count_le {S : State A G} (hS : S.Valid) (a : A) (g : G) :
    S.pool.count g + (S.bundle a).count g ≤ 1 := by
  have hle : (S.bundle a).count g ≤ ∑ b, (S.bundle b).count g :=
    Finset.single_le_sum (f := fun b => (S.bundle b).count g)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ a)
  have := hS g
  omega

omit [DecidableEq A] in
theorem State.Valid.bundle_nodup {S : State A G} (hS : S.Valid) (a : A) :
    (S.bundle a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro g
  have := hS.bundle_count_le a g
  omega

theorem State.Valid.disjoint {S : State A G} (hS : S.Valid) {a b : A} (hab : a ≠ b) :
    List.Disjoint (S.bundle a) (S.bundle b) := by
  intro g hga hgb
  have ha : 0 < (S.bundle a).count g := List.count_pos_iff.mpr hga
  have hb : 0 < (S.bundle b).count g := List.count_pos_iff.mpr hgb
  have hle : (S.bundle a).count g + (S.bundle b).count g ≤
      ∑ c, (S.bundle c).count g := by
    simpa [hab] using (Finset.sum_le_sum_of_subset
      (f := fun c => (S.bundle c).count g) (Finset.subset_univ ({a, b} : Finset A)))
  have := hS g
  omega

omit [DecidableEq A] in
/-- Charity is exactly the complement of the agents' bundles. -/
theorem State.Valid.charity_iff {S : State A G} (hS : S.Valid) (g : G) :
    g ∈ S.pool ↔ ∀ a, g ∉ S.bundle a := by
  constructor
  · intro hg a ha
    have hp : 0 < S.pool.count g := List.count_pos_iff.mpr hg
    have hb : 0 < (S.bundle a).count g := List.count_pos_iff.mpr ha
    have := hS.bundle_count_le a g
    omega
  · intro h
    have hsum : ∑ a, (S.bundle a).count g = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact List.count_eq_zero.mpr (h a)
    have := hS g
    have hpos : 0 < S.pool.count g := by omega
    exact List.count_pos_iff.mp hpos

namespace Instance

variable (I : Instance A G)

theorem give_count (S : State A G) (a : A) (g q : G) :
    (∑ b, ((I.give S a g).bundle b).count q) =
      (∑ b, (S.bundle b).count q) + [g].count q := by
  calc
    (∑ b, ((I.give S a g).bundle b).count q) =
        ∑ b, ((S.bundle b).count q + if b = a then [g].count q else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hba : b = a
      · subst b
        simp [give]
      · simp [give, hba]
    _ = (∑ b, (S.bundle b).count q) + [g].count q := by
      rw [Finset.sum_add_distrib]
      simp

theorem valid_give {S : State A G} (hS : S.Valid) {a : A} {g : G} (hg : g ∈ S.pool) :
    (I.give S a g).Valid := by
  intro q
  have hcount : S.pool.count q = (S.pool.erase g).count q + [g].count q := by
    have h := (List.perm_cons_erase hg).count_eq q
    simpa [List.count_cons, List.count_singleton, Nat.add_comm] using h
  rw [I.give_count]
  change (S.pool.erase g).count q + ((∑ b, (S.bundle b).count q) + [g].count q) = 1
  have := hS q
  omega

theorem valid_retire {S : State A G} (hS : S.Valid) (a : A) :
    (I.retire S a).Valid := hS

theorem run_valid {S : State A G} (hS : S.Valid) (t : ℕ) : (I.run t S).Valid :=
  I.run_preserves (P := State.Valid) (fun _ a h _ => I.valid_retire h a)
    (fun _ _ _ h hc => I.valid_give h hc.2.1) t hS

end Instance

theorem initial_valid {n m : ℕ} :
    (initial (List.finRange n) (List.finRange m)).Valid := by
  intro g
  simp only [initial, List.count_nil, Finset.sum_const_zero]
  exact List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange g)

theorem densestGreedy_valid {n m : ℕ} (I : Instance (Fin n) (Fin m)) :
    (densestGreedy I).Valid := I.run_valid initial_valid _

end FairAllocation

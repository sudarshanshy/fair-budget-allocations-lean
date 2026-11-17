import FairAllocation.Main
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

/-!
# Kernel-checked executable examples

These checks use `decide`, not `native_decide`; their proof terms are checked
by Lean's kernel. They complement, and do not replace, the universal proof.
-/

namespace FairAllocation.Examples

/-- Section 3.6's example with ε = 1/10. -/
def tight : Instance (Fin 2) (Fin 3) where
  value g := if g = 0 then 10 else if g = 1 then 1 / 2 else 4 / 5
  size _ g := if g = 0 then 1 / 10 else if g = 1 then 1 / 2 else 9 / 10
  budget _ := 1
  value_pos := by intro g; split_ifs <;> norm_num
  size_pos := by intro a g; split_ifs <;> norm_num
  budget_nonneg := by intro a; norm_num

theorem tight_first_bundle : (densestGreedy tight).bundle 0 = [0, 2] := by decide +kernel
theorem tight_second_bundle : (densestGreedy tight).bundle 1 = [1] := by decide +kernel
theorem tight_charity : (densestGreedy tight).pool = [] := by decide +kernel

theorem tight_pair_not_ef1 :
    ¬ SetEF 1 tight.value (total tight.value ((densestGreedy tight).bundle 1))
      ((densestGreedy tight).bundle 0).toFinset := by
  rw [tight_first_bundle, tight_second_bundle]
  unfold SetEF
  decide +kernel

/-- The EF2 guarantee cannot be strengthened to EF1 for this algorithm. -/
theorem tight_not_fair_one :
    ¬ tight.Fair 1 (densestGreedy tight).bundle (densestGreedy tight).pool := by
  intro h
  have hset := tight.fair_toFinset (densestGreedy_valid tight) h
  apply tight_pair_not_ef1
  rw [total_eq_sum_toFinset tight.value ((densestGreedy_valid tight).bundle_nodup 1)]
  apply hset.1 1 0 _ (Finset.Subset.refl _)
  dsimp only
  rw [tight_first_bundle]
  decide +kernel

/-- The agents see different sizes and hence different density rankings. -/
def heterogeneous : Instance (Fin 2) (Fin 3) where
  value g := if g = 0 then 6 else if g = 1 then 4 else 3
  size a g := if a = 0 then
      (if g = 0 then 4 else if g = 1 then 2 else 1)
    else (if g = 0 then 1 else if g = 1 then 2 else 4)
  budget _ := 3
  value_pos := by intro g; split_ifs <;> norm_num
  size_pos := by intro a g; split_ifs <;> norm_num
  budget_nonneg := by intro a; norm_num

example : (densestGreedy heterogeneous).bundle 0 = [2, 1] := by decide +kernel
example : (densestGreedy heterogeneous).bundle 1 = [0] := by decide +kernel
example : (densestGreedy heterogeneous).pool = [] := by decide +kernel

/-- A good which fits nowhere remains in charity. -/
def noCapacity : Instance (Fin 2) (Fin 1) where
  value _ := 1
  size _ _ := 1
  budget _ := 0
  value_pos := by intro g; norm_num
  size_pos := by intro a g; norm_num
  budget_nonneg := by intro a; norm_num

example : (densestGreedy noCapacity).pool = [0] := by decide +kernel
example : (densestGreedy noCapacity).active = [] := by decide +kernel
example : noCapacity.iterations 3 (initial (List.finRange 2) (List.finRange 1)) = 2 := by decide +kernel

end FairAllocation.Examples

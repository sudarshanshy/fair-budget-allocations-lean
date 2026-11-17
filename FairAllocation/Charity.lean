import FairAllocation.Fractional
import FairAllocation.Order

set_option autoImplicit false

/-!
# EF1 against charity (Appendix C, Proposition 5 and Lemma 11)
-/

namespace FairAllocation

variable {G : Type*}

/-- Every good still in the pool was available at every earlier choice. -/
def PoolPriority (v s : G → ℚ) (B : ℚ) (X C : List G) : Prop :=
  ∀ P x g, Before X P x → g ∈ C →
    total s P + s g ≤ B → v g / s g ≤ v x / s x

def NoFit (s : G → ℚ) (B : ℚ) (X C : List G) : Prop :=
  ∀ g ∈ C, B < total s X + s g

theorem ef_one_of_delete {v : G → ℚ} {u : ℚ} (P Q : List G) (g : G)
    (h : total v P + total v Q ≤ u) : EF 1 v u (P ++ g :: Q) := by
  refine ⟨P ++ Q, (List.Sublist.refl P).append (List.sublist_cons_self g Q), ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · simpa using h

theorem charity_ef1 {v s : G → ℚ}
    (hv : ∀ g, 0 ≤ v g) (hs : ∀ g, 0 < s g)
    {B : ℚ} {X C Z : List G}
    (horder : DensitySorted v s X)
    (hpriority : PoolPriority v s B X C)
    (hterminal : NoFit s B X C)
    (hZ : Z.Sublist C) (hfeas : total s Z ≤ B) :
    EF 1 v (total v X) Z := by
  by_cases hempty : Z = []
  · subst Z
    exact ef_nil (total_nonneg (fun x _ => hv x))
  obtain ⟨g, hg, hmax⟩ := exists_max_weight (fun x => v x / s x) hempty
  have hgC : g ∈ C := hZ.subset hg
  obtain ⟨D, R, hX, hdense, hlow⟩ := density_split horder (v g / s g)
  have hblocked : B < total s D + s g := by
    by_contra hn
    have hfit : total s D + s g ≤ B := le_of_not_gt hn
    cases R with
    | nil =>
      exact (not_lt_of_ge hfit) (by simpa [hX] using hterminal g hgC)
    | cons x R =>
      have hge := hpriority D x g ⟨R, hX⟩ hgC hfit
      exact (not_le_of_gt (hlow x (by simp))) hge
  have hd0 : 0 ≤ v g / s g := div_nonneg (hv g) (hs g).le
  have hDval : (v g / s g) * total s D ≤ total v D := by
    rw [← total_mul]
    exact total_mono (fun x hx => (le_density_iff hs).mp (hdense x hx))
  have hZval : total v Z ≤ (v g / s g) * total s Z := by
    rw [← total_mul]
    exact total_mono (fun x hx => (density_le_iff hs).mp (hmax x hx))
  have hsub : total v D ≤ total v X := by
    rw [hX, total_append]
    exact le_add_of_nonneg_right (total_nonneg (fun x _ => hv x))
  have hmul : (v g / s g) * total s Z ≤ (v g / s g) * (total s D + s g) :=
    mul_le_mul_of_nonneg_left (hfeas.trans hblocked.le) hd0
  have hvg := density_mul_size (v := v) hs g
  have hbound : total v Z ≤ total v X + v g := by nlinarith
  obtain ⟨P, Q, hPQ, _⟩ := List.eq_append_cons_of_mem hg
  rw [hPQ] at hbound ⊢
  apply ef_one_of_delete
  simp only [total_append, total_cons] at hbound
  linarith

end FairAllocation
